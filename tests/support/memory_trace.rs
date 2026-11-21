//! Compare static reaching-write masks with ordered concrete module replay.
use nirvana::ir::{self, Assignment, Control, Expr, Place, Reg, Width};
use nirvana::memory_ssa::{Analysis, MemoryId, Query};
use nirvana::module_ir::{self, Instruction, Module};
use nirvana::module_values::{FunctionValues, PointRole};
use nirvana::ssa::Site;
use nirvana::type_infer::{Operand, PathEdge};
use std::collections::BTreeMap;

#[derive(Default, Debug)]
pub struct Stats {
    pub instructions: usize,
    pub read_bytes: usize,
    pub written_bytes: usize,
}

struct Replay<'a> {
    base: u64,
    registers: Vec<u64>,
    memory: Vec<u8>,
    writers: Vec<MemoryId>,
    writer_bytes: Vec<u8>,
    analysis: &'a Analysis,
    queries: BTreeMap<usize, &'a Query>,
    sites: BTreeMap<(u64, usize, bool), Site>,
    targets: BTreeMap<u64, Site>,
    guards: BTreeMap<u64, Site>,
    stats: Stats,
}

impl Replay<'_> {
    fn evaluate(&self, expression: &Expr) -> Result<u64, ()> {
        let program = ir::Program::new(
            0,
            self.registers.len(),
            vec![ir::IrInstruction {
                address: 0,
                size: 1,
                assignments: vec![],
                control: Control::Return(expression.clone()),
            }],
        )
        .unwrap();
        match program
            .run_with_memory(&self.registers, self.base, &self.memory, 1)
            .unwrap()
            .status
        {
            ir::RunStatus::Returned(value) => Ok(value),
            ir::RunStatus::Fault(_) => Err(()),
            other => panic!("{other:?}"),
        }
    }
    fn offset(&self, address: u64, width: usize) -> Result<usize, ()> {
        let offset = usize::try_from(address.checked_sub(self.base).ok_or(())?).map_err(|_| ())?;
        if offset
            .checked_add(width)
            .is_none_or(|end| end > self.memory.len())
        {
            return Err(());
        }
        Ok(offset)
    }
    fn read(
        &mut self,
        site: Site,
        operand: Operand,
        path: &[PathEdge],
        address: u64,
        width: Width,
    ) -> Result<(), ()> {
        let offset = self.offset(address, width.bytes())?;
        let (index, access) = self
            .analysis
            .accesses()
            .iter()
            .enumerate()
            .find(|(_, a)| {
                a.source.site == site
                    && a.source.operand == operand
                    && a.source.path == path
                    && a.source.kind == ir::AccessKind::Read
            })
            .expect("concrete read has a source-bound memory use");
        assert_eq!(access.source.width, width);
        let query = self.queries[&index];
        for byte in 0..width.bytes() {
            let writer = self.writers[offset + byte];
            let candidate=query.candidates.iter().find(|c|c.definition==writer && c.byte_mask & (1 << byte)!=0)
                .unwrap_or_else(||panic!("lost writer: site={site:?} address={address:#x} byte={byte} writer={writer:?} query={query:?}"));
            assert!(
                candidate.unknown_bytes & (1 << byte) != 0
                    || candidate.byte_sources[byte] & (1 << self.writer_bytes[offset + byte]) != 0,
                "lost source byte: {site:?}/{address:#x}/byte {byte}/source {}: {candidate:?}",
                self.writer_bytes[offset + byte]
            );
            self.stats.read_bytes += 1;
        }
        Ok(())
    }
    fn expression(
        &mut self,
        site: Site,
        operand: Operand,
        expr: &Expr,
        path: &mut Vec<PathEdge>,
    ) -> Result<(), ()> {
        match expr {
            Expr::Const(_) | Expr::Register(_) => {}
            Expr::Unary(_, value) => self.child(site, operand, value, path, PathEdge::Unary)?,
            Expr::Binary(_, left, right) => {
                self.child(site, operand, left, path, PathEdge::Left)?;
                self.child(site, operand, right, path, PathEdge::Right)?;
            }
            Expr::Load { address, width } => {
                self.child(site, operand, address, path, PathEdge::Address)?;
                let address = self.evaluate(address)?;
                self.read(site, operand, path, address, *width)?;
            }
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => {
                self.child(site, operand, condition, path, PathEdge::Condition)?;
                let (expr, edge) = if self.evaluate(condition)? != 0 {
                    (taken, PathEdge::Taken)
                } else {
                    (not_taken, PathEdge::NotTaken)
                };
                self.child(site, operand, expr, path, edge)?;
            }
        }
        Ok(())
    }
    fn child(
        &mut self,
        site: Site,
        operand: Operand,
        expr: &Expr,
        path: &mut Vec<PathEdge>,
        edge: PathEdge,
    ) -> Result<(), ()> {
        path.push(edge);
        let result = self.expression(site, operand, expr, path);
        path.pop();
        result
    }
    fn assignment(&mut self, site: Site, assignment: &Assignment) -> Result<(), ()> {
        let destination = if let Place::Memory { address, width } = &assignment.destination {
            self.expression(
                site,
                Operand::Destination,
                address,
                &mut vec![PathEdge::Address],
            )?;
            let address = self.evaluate(address)?;
            Some((self.offset(address, width.bytes())?, *width))
        } else {
            None
        };
        self.expression(site, Operand::Value, &assignment.value, &mut Vec::new())?;
        let program = ir::Program::new(
            0,
            self.registers.len(),
            vec![ir::IrInstruction {
                address: 0,
                size: 1,
                assignments: vec![assignment.clone()],
                control: Control::Return(Expr::Const(0)),
            }],
        )
        .unwrap();
        let report = program
            .run_with_memory(&self.registers, self.base, &self.memory, 1)
            .unwrap();
        assert!(matches!(report.status, ir::RunStatus::Returned(_)));
        self.registers = report.state.registers;
        self.memory = report.state.memory;
        if let Some((offset, width)) = destination {
            let access = self
                .analysis
                .accesses()
                .iter()
                .find(|a| a.source.site == site && a.source.kind == ir::AccessKind::Write)
                .unwrap();
            let writer = access.definition.unwrap();
            self.writers[offset..offset + width.bytes()].fill(writer);
            for byte in 0..width.bytes() {
                self.writer_bytes[offset + byte] = byte as u8;
            }
            self.stats.written_bytes += width.bytes();
        }
        Ok(())
    }
    fn instruction(&mut self, instruction: &Instruction) -> Result<(), ()> {
        let pc = instruction.address();
        let (assignments, vector) = match instruction {
            Instruction::Core(i) => (&i.assignments, false),
            Instruction::Vector(v) => {
                if let Some(memory) = &v.memory {
                    self.expression(
                        self.guards[&pc],
                        Operand::Value,
                        &memory.address,
                        &mut Vec::new(),
                    )?;
                    let address = self.evaluate(&memory.address)?;
                    self.offset(address, memory.width as usize)?;
                    if memory.alignment == 0 || address % u64::from(memory.alignment) != 0 {
                        return Err(());
                    }
                }
                (&v.assignments, true)
            }
            Instruction::Return { extra_pop, .. } => {
                let expression = Expr::load(Expr::Register(Reg(nirvana::x86::RSP)), Width::U64);
                self.expression(
                    self.targets[&pc],
                    Operand::Value,
                    &expression,
                    &mut Vec::new(),
                )?;
                self.registers[nirvana::x86::RSP] =
                    self.registers[nirvana::x86::RSP].wrapping_add(8 + u64::from(*extra_pop));
                return Ok(());
            }
            other => panic!("replay corpus requires scalar/vector instructions and RET: {other:?}"),
        };
        for (index, assignment) in assignments.iter().enumerate() {
            self.assignment(self.sites[&(pc, index, vector)], assignment)?;
        }
        if let Instruction::Core(i) = instruction
            && let Control::Branch { condition, .. } | Control::Return(condition) = &i.control
        {
            self.expression(
                Site {
                    instruction: pc,
                    assignment: None,
                },
                Operand::Control,
                condition,
                &mut Vec::new(),
            )?;
        }
        Ok(())
    }
}

pub fn check(
    module: &Module,
    values: &FunctionValues,
    registers: Vec<u64>,
    memory: Vec<u8>,
    limit: usize,
) -> Stats {
    assert!(
        module.program.memory_layout().is_none(),
        "this corpus uses dense checked RAM"
    );
    let report = module
        .program
        .run(
            &registers,
            module.image.memory_base,
            &memory,
            module_ir::Limits {
                instructions: limit,
                imports: 0,
            },
            &mut module_ir::RejectImports,
        )
        .unwrap();
    let analysis = values.memory().unwrap().as_ref().unwrap();
    let mut replay = Replay {
        base: module.image.memory_base,
        writers: vec![MemoryId(0); memory.len()],
        writer_bytes: vec![0; memory.len()],
        registers,
        memory,
        analysis,
        queries: analysis
            .queries()
            .as_ref()
            .unwrap()
            .iter()
            .map(|q| (q.access, q))
            .collect(),
        sites: BTreeMap::new(),
        targets: BTreeMap::new(),
        guards: BTreeMap::new(),
        stats: Stats::default(),
    };
    for (site, role) in values.roles() {
        match role {
            PointRole::Assignment { original } => {
                replay
                    .sites
                    .insert((site.instruction, *original, false), *site);
            }
            PointRole::VectorAssignment { original } => {
                replay
                    .sites
                    .insert((site.instruction, *original, true), *site);
            }
            PointRole::Target => {
                replay.targets.insert(site.instruction, *site);
            }
            PointRole::VectorGuard => {
                replay.guards.insert(site.instruction, *site);
            }
            _ => {}
        }
    }
    for pc in &report.state.trace {
        let index = module
            .program
            .instructions()
            .binary_search_by_key(pc, Instruction::address)
            .unwrap();
        replay.stats.instructions += 1;
        if replay
            .instruction(&module.program.instructions()[index])
            .is_err()
        {
            break;
        }
    }
    assert_eq!(
        replay.registers, report.state.registers,
        "concrete per-assignment replay register state"
    );
    assert_eq!(
        replay.memory, report.state.memory,
        "concrete per-assignment replay memory state"
    );
    replay.stats
}

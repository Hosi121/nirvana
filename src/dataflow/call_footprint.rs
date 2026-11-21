//! Conservative register footprints for calls whose actual return slot is protected.
//!
//! A closed summary is conditional on a finite successful return: every reached
//! store is below the entry return slot, every ordinary call has a normal link,
//! and every return restores the entry stack pointer. Unknown memory effects or
//! control make the function and its callers opaque. No ABI rules are assumed.
//! DIV/IDIV have unknown normal results in AX or DX:AX; operand faults and #DE
//! stop before the normal continuation. Their loads preserve return-slot RAM.

use std::collections::{BTreeMap, VecDeque};

use crate::dataflow::stack::StackAnalysis;
use crate::model::ir::{
    AccessKind, Assignment, Control, Expr, IrInstruction, Place, Program, Reg, Width,
};
use crate::model::module_ir::{self, Instruction, Target};

const MAX_FUNCTIONS: usize = 512;
const MAX_INSTRUCTIONS: usize = 65_536;
const MAX_FUNCTION_INSTRUCTIONS: usize = 16_384;
const MAX_NODES: usize = 1_048_576;
const MAX_DEPTH: usize = 128;
const MAX_ASSIGNMENTS: usize = 131_072;
const MAX_PROJECTED_POINTS: usize = 98_000;
const MAX_QUERIES: usize = 131_072;
const MAX_QUERY_NODES: usize = 2_000_000;
const MAX_STACK_OFFSET: i64 = 1_048_576;
const RSP: Reg = Reg(crate::binary::x86::RSP);
type Registers = u128;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FunctionSummary {
    pub address: u64,
    pub closed: bool,
    pub reason: Option<String>,
    pub reads: Vec<Reg>,
    pub clobbers: Vec<Reg>,
    pub preserved: Vec<Reg>,
    pub callees: Vec<u64>,
}

#[derive(Clone, Debug)]
pub struct Analysis {
    pub functions: Vec<FunctionSummary>,
}

impl Analysis {
    pub fn at(&self, address: u64) -> Option<&FunctionSummary> {
        self.functions
            .binary_search_by_key(&address, |f| f.address)
            .ok()
            .map(|i| &self.functions[i])
    }
}

#[derive(Default)]
struct Work {
    nodes: usize,
    assignments: usize,
    projected_points: usize,
    queries: usize,
    query_nodes: usize,
    exhausted: bool,
}

impl Work {
    fn charge(&mut self, amount: usize, kind: &'static str) -> Result<(), String> {
        let (used, limit) = match kind {
            "syntax" => (&mut self.nodes, MAX_NODES),
            "assignments" => (&mut self.assignments, MAX_ASSIGNMENTS),
            "projection" => (&mut self.projected_points, MAX_PROJECTED_POINTS),
            "queries" => (&mut self.queries, MAX_QUERIES),
            _ => (&mut self.query_nodes, MAX_QUERY_NODES),
        };
        *used = used.saturating_add(amount);
        if *used > limit {
            self.exhausted = true;
            return Err(format!("call footprint module {kind} limit"));
        }
        Ok(())
    }

    // Iterative validation happens before any recursive Expr::clone or IR
    // validation. The extra register in the projection is never a guest input.
    fn expression(&mut self, expression: &Expr, registers: usize) -> Result<(), String> {
        let mut pending = vec![(expression, 1usize)];
        while let Some((e, depth)) = pending.pop() {
            self.charge(1, "syntax")?;
            if depth > MAX_DEPTH {
                return Err("call footprint expression depth limit".into());
            }
            if let Expr::Register(reg) = e
                && reg.0 >= registers
            {
                return Err("call footprint invalid guest register".into());
            }
            children(e, depth, &mut pending);
        }
        Ok(())
    }

    fn offset(
        &mut self,
        stack: &StackAnalysis,
        address: u64,
        assignment: usize,
        expression: &Expr,
    ) -> Result<Option<i64>, String> {
        self.charge(1, "queries")?;
        let mut pending = vec![(expression, 1usize)];
        while let Some((e, depth)) = pending.pop() {
            self.charge(1, "query nodes")?;
            children(e, depth, &mut pending);
        }
        Ok(stack.offset_before(address, assignment, expression))
    }
}

fn children<'a>(e: &'a Expr, depth: usize, pending: &mut Vec<(&'a Expr, usize)>) {
    match e {
        Expr::Binary(_, a, b) => {
            pending.push((b, depth + 1));
            pending.push((a, depth + 1));
        }
        Expr::Load { address, .. } => pending.push((address, depth + 1)),
        Expr::Select {
            condition,
            taken,
            not_taken,
        } => {
            pending.push((not_taken, depth + 1));
            pending.push((taken, depth + 1));
            pending.push((condition, depth + 1));
        }
        _ => {}
    }
}

fn reads(expression: &Expr) -> Registers {
    let mut result = 0;
    let mut pending = vec![(expression, 1usize)];
    while let Some((e, depth)) = pending.pop() {
        if let Expr::Register(reg) = e {
            result |= 1 << reg.0;
        }
        children(e, depth, &mut pending);
    }
    result
}

#[derive(Default)]
struct Local {
    reason: Option<String>,
    reads: Registers,
    clobbers: Registers,
    callees: Vec<usize>,
}

impl Local {
    fn reject(&mut self, reason: impl Into<String>) {
        if self.reason.is_none() {
            self.reason = Some(reason.into());
        }
    }
}

/// Summaries cover entry-reachable instructions and normal call continuations.
/// Whole-module resource exhaustion discards every partial summary atomically;
/// local proof failures remain explicit opaque summaries with their reason.
pub fn analyze(program: &module_ir::Program) -> Result<Analysis, String> {
    let registers = program.register_count();
    if program.functions().len() > MAX_FUNCTIONS
        || program.instructions().len() > MAX_INSTRUCTIONS
        || registers != module_ir::REGISTER_COUNT
        || registers >= Registers::BITS as usize
    {
        return Err("call footprint module source limit".into());
    }
    let mut functions: Vec<_> = program.functions().iter().collect();
    functions.sort_by_key(|f| f.address);
    let entries: BTreeMap<_, _> = functions
        .iter()
        .enumerate()
        .map(|(i, f)| (f.address, i))
        .collect();
    if entries.len() != functions.len() {
        return Err("call footprint duplicate function entry".into());
    }
    let addresses: Vec<_> = functions.iter().map(|f| f.address).collect();
    let mut work = Work::default();
    let mut locals = Vec::with_capacity(functions.len());
    for function in &functions {
        let result = local(program, function, &entries, &mut work);
        if work.exhausted {
            return Err(result
                .err()
                .unwrap_or_else(|| "call footprint module work limit".into()));
        }
        locals.push(result.unwrap_or_else(|reason| Local {
            reason: Some(reason),
            ..Default::default()
        }));
    }

    let mut callers = vec![Vec::new(); functions.len()];
    for (caller, local) in locals.iter().enumerate() {
        for &callee in &local.callees {
            callers[callee].push(caller);
        }
    }
    // Poison before footprint propagation. Safe recursive SCCs are accepted by
    // induction on completed finite calls; a bad member poisons the whole SCC.
    let mut pending: VecDeque<_> = locals
        .iter()
        .enumerate()
        .filter_map(|(i, local)| local.reason.as_ref().map(|_| i))
        .collect();
    while let Some(callee) = pending.pop_front() {
        for &caller in &callers[callee] {
            if locals[caller].reason.is_none() {
                locals[caller].reject(format!(
                    "callee {:#x} has no closed return contract",
                    functions[callee].address
                ));
                pending.push_back(caller);
            }
        }
    }
    let mut pending: VecDeque<_> = (0..locals.len())
        .filter(|&i| locals[i].reason.is_none())
        .collect();
    let mut queued = vec![true; locals.len()];
    while let Some(callee) = pending.pop_front() {
        queued[callee] = false;
        let (callee_reads, callee_clobbers) = (locals[callee].reads, locals[callee].clobbers);
        for &caller in &callers[callee] {
            if locals[caller].reason.is_some() {
                continue;
            }
            let old = (locals[caller].reads, locals[caller].clobbers);
            locals[caller].reads |= callee_reads;
            locals[caller].clobbers |= callee_clobbers;
            if old != (locals[caller].reads, locals[caller].clobbers) && !queued[caller] {
                queued[caller] = true;
                pending.push_back(caller);
            }
        }
    }
    let all = (1 << registers) - 1;
    Ok(Analysis {
        functions: functions
            .into_iter()
            .zip(locals)
            .map(|(function, local)| {
                let closed = local.reason.is_none();
                let clobbers = if closed { local.clobbers } else { all };
                FunctionSummary {
                    address: function.address,
                    closed,
                    reason: local.reason,
                    reads: register_set(if closed { local.reads } else { all }, registers),
                    clobbers: register_set(clobbers, registers),
                    preserved: register_set(if closed { all & !clobbers } else { 0 }, registers),
                    callees: local.callees.into_iter().map(|i| addresses[i]).collect(),
                }
            })
            .collect(),
    })
}

fn register_set(bits: Registers, count: usize) -> Vec<Reg> {
    (0..count)
        .filter(|i| bits & (1 << i) != 0)
        .map(Reg)
        .collect()
}

fn preflight(source: &[Instruction], registers: usize, work: &mut Work) -> Result<(), String> {
    if source.len() > MAX_FUNCTION_INSTRUCTIONS {
        return Err("call footprint function instruction limit".into());
    }
    for instruction in source {
        let assignments = match instruction {
            Instruction::StoreString { .. } | Instruction::MoveString { .. } => {
                return Err("call footprint string transfer requires a checked summary".into());
            }
            Instruction::Divide { source, .. } => {
                work.expression(source, registers)?;
                &[]
            }
            Instruction::Core(i) => &i.assignments[..],
            Instruction::Vector(i) => {
                if let Some(memory) = &i.memory {
                    work.expression(&memory.address, registers)?;
                }
                &i.assignments[..]
            }
            Instruction::Transfer { target, .. } => {
                if let Target::Value(value) = target {
                    work.expression(value, registers)?;
                }
                &[]
            }
            _ => &[],
        };
        work.charge(assignments.len(), "assignments")?;
        for assignment in assignments {
            match &assignment.destination {
                Place::Memory { address, .. } => work.expression(address, registers)?,
                Place::Register(reg) if reg.0 >= registers => {
                    return Err("call footprint invalid destination register".into());
                }
                _ => {}
            }
            work.expression(&assignment.value, registers)?;
        }
        if let Instruction::Core(i) = instruction
            && let Control::Branch { condition, .. } | Control::Return(condition) = &i.control
        {
            work.expression(condition, registers)?;
        }
    }
    Ok(())
}

fn project(
    source: &[Instruction],
    registers: usize,
    work: &mut Work,
) -> Result<Vec<IrInstruction>, String> {
    let mut result = Vec::with_capacity(source.len());
    for instruction in source {
        let point_count = match instruction {
            Instruction::Core(i) => i.assignments.len() + 1,
            Instruction::Vector(i) => i.assignments.len() + 1,
            Instruction::Transfer { link: Some(_), .. } => registers,
            Instruction::Divide { width, .. } => divide_registers(*width).len() + 1,
            _ => 1,
        };
        work.charge(point_count, "projection")?;
        let (assignments, control) = match instruction {
            Instruction::StoreString { .. } | Instruction::MoveString { .. } => {
                return Err("call footprint string transfer requires a checked summary".into());
            }
            Instruction::Divide { width, .. } => (
                divide_registers(*width)
                    .iter()
                    .map(|&reg| Assignment {
                        destination: reg.into(),
                        // A successful divide produces a new unknown bit pattern.
                        // Its source Load can fault, but never modifies guest RAM.
                        value: Expr::Register(Reg(registers)),
                    })
                    .collect(),
                Control::Next,
            ),
            Instruction::Core(i) => (i.assignments.clone(), i.control.clone()),
            Instruction::Vector(i) => (i.assignments.clone(), Control::Next),
            Instruction::Transfer {
                link: Some(next), ..
            } => (
                (0..registers)
                    .filter(|&i| i != RSP.0)
                    .map(|i| Assignment {
                        destination: Reg(i).into(),
                        // This input is never assigned. Unlike a numeric
                        // placeholder it cannot invent a pointer/constant fact.
                        value: Expr::Register(Reg(registers)),
                    })
                    .collect(),
                Control::Jump(*next),
            ),
            _ => (Vec::new(), Control::Return(Expr::Const(0))),
        };
        result.push(IrInstruction {
            address: instruction.address(),
            size: instruction.size(),
            assignments,
            control,
        });
    }
    Ok(result)
}

fn safe_offset(offset: Option<i64>, width: u64) -> bool {
    offset.is_some_and(|offset| {
        (-MAX_STACK_OFFSET..0).contains(&offset)
            && width != 0
            && i128::from(offset) + i128::from(width) <= 0
    })
}

fn divide_registers(width: Width) -> &'static [Reg] {
    const AX: &[Reg] = &[Reg(crate::binary::x86::RAX)];
    const DX_AX: &[Reg] = &[Reg(crate::binary::x86::RAX), Reg(crate::binary::x86::RDX)];
    if width == Width::U8 { AX } else { DX_AX }
}

fn local(
    program: &module_ir::Program,
    function: &module_ir::Function,
    entries: &BTreeMap<u64, usize>,
    work: &mut Work,
) -> Result<Local, String> {
    let end = function
        .address
        .checked_add(function.size)
        .ok_or("call footprint function range overflow")?;
    let source = &program.instructions()[program
        .instructions()
        .partition_point(|i| i.address() < function.address)
        ..program
            .instructions()
            .partition_point(|i| i.address() < end)];
    local_source(
        source,
        function.address,
        program.register_count(),
        entries,
        work,
    )
}

fn local_source(
    source: &[Instruction],
    entry: u64,
    registers: usize,
    entries: &BTreeMap<u64, usize>,
    work: &mut Work,
) -> Result<Local, String> {
    preflight(source, registers, work)?;
    let projected = Program::new(entry, registers + 1, project(source, registers, work)?)
        .map_err(|e| format!("call footprint local control: {e}"))?;
    let stack = StackAnalysis::try_analyze(&projected, RSP)
        .ok_or("call footprint stack analysis unavailable: control or resource limit")?;
    let mut local = Local::default();
    for id in projected.cfg().reachable_blocks() {
        for index in projected.cfg().block(id).instructions.clone() {
            let instruction = &source[index];
            let address = instruction.address();
            let assignments = match instruction {
                Instruction::StoreString { .. } | Instruction::MoveString { .. } => {
                    return Err("call footprint string transfer requires a checked summary".into());
                }
                Instruction::Divide { source, width, .. } => {
                    local.reads |= reads(source);
                    for &register in divide_registers(*width) {
                        local.reads |= 1 << register.0;
                        local.clobbers |= 1 << register.0;
                    }
                    &[]
                }
                Instruction::Core(i) => {
                    match &i.control {
                        Control::Branch { condition, .. } => local.reads |= reads(condition),
                        Control::Return(value) => {
                            local.reads |= reads(value);
                            local.reject("scalar return bypasses the actual return slot");
                        }
                        _ => {}
                    }
                    &i.assignments[..]
                }
                Instruction::Vector(i) => {
                    if let Some(memory) = &i.memory {
                        local.reads |= reads(&memory.address);
                        if memory.access == AccessKind::Write
                            && !safe_offset(
                                work.offset(&stack, address, 0, &memory.address)?,
                                u64::from(memory.width),
                            )
                        {
                            local
                                .reject("vector store may touch the return slot or unknown memory");
                        }
                    }
                    &i.assignments[..]
                }
                Instruction::Transfer {
                    target, link, size, ..
                } => {
                    local.reads |= 1 << RSP.0;
                    match target {
                        Target::Value(value) => {
                            local.reads |= reads(value);
                            match value {
                                Expr::Const(target) => match entries.get(target) {
                                    Some(&callee) => local.callees.push(callee),
                                    None => local.reject(
                                        "direct target is not an exact internal function entry",
                                    ),
                                },
                                _ => local.reject("dynamic transfer has no closed return contract"),
                            }
                        }
                        Target::Plt(_) => {
                            local.reject("mutable PLT transfer has no closed return contract")
                        }
                    }
                    let offset = work.offset(&stack, address, 0, &Expr::Register(RSP))?;
                    if let Some(link) = link {
                        if address.checked_add(u64::from(*size)) != Some(*link) {
                            local.reject("ordinary call link is not its next PC");
                        }
                        if !offset.is_some_and(|o| (-MAX_STACK_OFFSET..=0).contains(&o)) {
                            local.reject("ordinary call has unknown or positive stack offset");
                        }
                    } else if offset != Some(0) {
                        local.reject("tail transfer does not restore the entry stack pointer");
                    }
                    &[]
                }
                Instruction::Return { extra_pop, .. } => {
                    local.reads |= 1 << RSP.0;
                    if *extra_pop != 0
                        || work.offset(&stack, address, 0, &Expr::Register(RSP))? != Some(0)
                    {
                        local.reject("return has unknown/unbalanced stack pointer or extra pop");
                    }
                    &[]
                }
            };
            for (assignment, effect) in assignments.iter().enumerate() {
                local.reads |= reads(&effect.value);
                match &effect.destination {
                    Place::Register(reg) => local.clobbers |= 1 << reg.0,
                    Place::Memory {
                        address: destination,
                        width,
                    } => {
                        local.reads |= reads(destination);
                        if !safe_offset(
                            work.offset(&stack, address, assignment, destination)?,
                            width.bytes() as u64,
                        ) {
                            local.reject("store may touch the return slot or unknown memory");
                        }
                    }
                }
            }
        }
    }
    local.callees.sort_unstable();
    local.callees.dedup();
    // A write is also a conservative observation boundary for lifetime users.
    // Only proven ordinary-call stack restoration permits excluding RSP.
    local.reads |= local.clobbers;
    local.clobbers &= !(1 << RSP.0);
    Ok(local)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::binary::x86::{VectorInstruction, VectorMemory};
    use crate::model::ir::{BinaryOp, Width};

    fn ret(address: u64) -> Instruction {
        Instruction::Return {
            address,
            size: 1,
            extra_pop: 0,
        }
    }

    fn call(address: u64, target: Target, link: Option<u64>) -> Instruction {
        Instruction::Transfer {
            address,
            size: 1,
            target,
            link,
        }
    }

    fn check(source: &[Instruction]) -> Result<Local, String> {
        local_source(
            source,
            1,
            80,
            &BTreeMap::from([(1, 0), (10, 1)]),
            &mut Work::default(),
        )
    }

    #[test]
    fn malformed_links_and_nonentry_targets_are_opaque() {
        let wrong_link =
            check(&[call(1, Target::Value(Expr::Const(10)), Some(3)), ret(3)]).unwrap();
        assert!(wrong_link.reason.unwrap().contains("next PC"));
        let interior = check(&[call(1, Target::Value(Expr::Const(11)), Some(2)), ret(2)]).unwrap();
        assert!(
            interior
                .reason
                .unwrap()
                .contains("exact internal function entry")
        );
        let plt = check(&[call(1, Target::Plt(10), Some(2)), ret(2)]).unwrap();
        assert!(plt.reason.unwrap().contains("PLT"));
        let outside = check(&[Instruction::Core(IrInstruction {
            address: 1,
            size: 1,
            assignments: vec![],
            control: Control::Jump(10),
        })]);
        assert!(outside.err().unwrap().contains("local control"));
        let scalar = check(&[Instruction::Core(IrInstruction {
            address: 1,
            size: 1,
            assignments: vec![],
            control: Control::Return(Expr::Const(0)),
        })])
        .unwrap();
        assert!(scalar.reason.unwrap().contains("bypasses"));
    }

    #[test]
    fn vector_guard_checks_full_width_before_assignments() {
        let vector = |offset: u64, width: u32| {
            Instruction::Vector(VectorInstruction {
                address: 1,
                size: 1,
                assignments: vec![],
                memory: Some(VectorMemory {
                    address: Expr::binary(BinaryOp::Add, Expr::Register(RSP), Expr::Const(offset)),
                    width,
                    access: AccessKind::Write,
                    alignment: 1,
                }),
            })
        };
        assert!(
            check(&[vector((-16i64) as u64, 16), ret(2)])
                .unwrap()
                .reason
                .is_none()
        );
        assert!(
            check(&[vector((-8i64) as u64, 16), ret(2)])
                .unwrap()
                .reason
                .is_some()
        );
        assert!(
            check(&[vector((-8i64) as u64, 0), ret(2)])
                .unwrap()
                .reason
                .is_some()
        );
    }

    #[test]
    fn successful_divides_preserve_every_register_except_their_result_pair() {
        for width in [Width::U8, Width::U16, Width::U32, Width::U64] {
            for signed in [false, true] {
                let division = Instruction::Divide {
                    address: 1,
                    size: 1,
                    width,
                    signed,
                    source: Expr::load(Expr::Register(Reg(63)), width),
                };
                let local = check(&[division, ret(2)]).unwrap();
                assert!(local.reason.is_none());
                let results = if width == Width::U8 { 1 } else { 1 | (1 << 2) };
                assert_eq!(local.clobbers, results);
                assert_eq!(local.reads, results | (1 << 63) | (1 << RSP.0));
                assert!(local.callees.is_empty());
            }
        }
    }

    #[test]
    fn divide_results_become_unknown_before_later_stack_proofs() {
        let core = |address, destination, value| {
            Instruction::Core(IrInstruction {
                address,
                size: 1,
                assignments: vec![Assignment {
                    destination: Place::Register(destination),
                    value,
                }],
                control: Control::Next,
            })
        };
        for width in [Width::U8, Width::U16, Width::U32, Width::U64] {
            let source = [
                core(1, Reg(2), Expr::Register(RSP)),
                Instruction::Divide {
                    address: 2,
                    size: 1,
                    width,
                    signed: false,
                    source: Expr::Register(Reg(6)),
                },
                core(3, RSP, Expr::Register(Reg(2))),
                ret(4),
            ];
            let local = check(&source).unwrap();
            assert_eq!(local.reason.is_none(), width == Width::U8);
        }
        let invalid = Instruction::Divide {
            address: 1,
            size: 1,
            width: Width::U64,
            signed: false,
            source: Expr::Register(Reg(80)),
        };
        assert!(
            check(&[invalid, ret(2)])
                .err()
                .unwrap()
                .contains("invalid guest register")
        );
        let division = Instruction::Divide {
            address: 1,
            size: 1,
            width: Width::U64,
            signed: false,
            source: Expr::Const(1),
        };
        let mut work = Work {
            projected_points: MAX_PROJECTED_POINTS - 2,
            ..Work::default()
        };
        assert!(project(&[division], 80, &mut work).is_err());
        assert!(work.exhausted);
    }

    #[test]
    fn resource_limits_fail_before_recursive_clone_and_discard_partial_work() {
        let mut expression = Expr::Register(RSP);
        for _ in 0..MAX_DEPTH {
            expression = Expr::load(expression, Width::U64);
        }
        let source = [Instruction::Core(IrInstruction {
            address: 1,
            size: 1,
            assignments: vec![Assignment {
                destination: Reg(0).into(),
                value: expression,
            }],
            control: Control::Return(Expr::Const(0)),
        })];
        assert!(check(&source).err().unwrap().contains("depth limit"));
        let mut work = Work {
            nodes: MAX_NODES,
            ..Default::default()
        };
        assert!(preflight(&source, 80, &mut work).is_err());
        assert!(work.exhausted);
        let mut work = Work {
            projected_points: MAX_PROJECTED_POINTS,
            ..Default::default()
        };
        assert!(project(&[ret(1)], 80, &mut work).is_err());
        assert!(work.exhausted);
        let many = vec![ret(1); MAX_FUNCTION_INSTRUCTIONS + 1];
        assert!(check(&many).err().unwrap().contains("instruction limit"));
        let mut work = Work {
            queries: MAX_QUERIES,
            ..Default::default()
        };
        assert!(
            work.offset(&StackAnalysis::default(), 1, 0, &Expr::Register(RSP))
                .is_err()
        );
        assert!(work.exhausted);
    }
}

//! Executable local storage plans over the original checked module effects.
//!
//! Module value events are analysis metadata. In particular, opaque output
//! placeholders and synthetic register observations never become executable
//! assignments. Canonical registers remain authoritative at every resume and
//! call boundary, and every successful source register write is mirrored.

use std::collections::{BTreeMap, BTreeSet};

use crate::ir::{self, Assignment, Control, Expr, IrInstruction, Place, Reg};
use crate::module_ir::{self, Instruction};
use crate::module_values::{self, FunctionValues, PointRole};
use crate::parallel_copy::{self, Copy};
use crate::ssa::{self, Definition, PointValues, ValueId};

const RAW: usize = module_ir::REGISTER_COUNT;
const MAX_FUNCTIONS: usize = 512;
const MAX_MEMBERS: usize = 2_000_000;
const MAX_WORK: usize = 8_000_000;
const MAX_NODES: usize = 1_048_576;

#[derive(Clone, Debug)]
pub struct Plan {
    pub functions: Vec<FunctionLocals>,
}

#[derive(Clone, Debug)]
pub struct FunctionLocals {
    pub address: u64,
    pub result: Result<Locals, String>,
}

#[derive(Clone, Debug)]
pub struct Locals {
    pub local_count: usize,
    /// Storage IDs relative to register 80. Includes the two optional temps.
    pub used_locals: Vec<usize>,
    pub steps: BTreeMap<u64, StepLocals>,
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Binding {
    pub local: usize,
    pub register: Reg,
}

#[derive(Clone, Debug)]
pub struct StepLocals {
    pub resume: Vec<Binding>,
    pub assignments: Vec<Assignment>,
    pub after: Vec<Assignment>,
}

struct Budget {
    work: usize,
    members: usize,
    nodes: usize,
}

impl Budget {
    fn spend(&mut self, n: usize) -> Result<(), String> {
        self.work = self.work.checked_sub(n).ok_or("module local work limit")?;
        Ok(())
    }
    fn reserve(&mut self, n: usize) -> Result<(), String> {
        self.spend(n)?;
        self.members = self
            .members
            .checked_add(n)
            .filter(|n| *n <= MAX_MEMBERS)
            .ok_or("module local membership limit")?;
        Ok(())
    }
    // Scan before any recursive cloning/rewriting of source syntax.
    fn scan(&mut self, expression: &Expr) -> Result<(), String> {
        let mut pending = vec![(expression, 1usize)];
        while let Some((e, depth)) = pending.pop() {
            self.spend(1)?;
            self.nodes += 1;
            if self.nodes > MAX_NODES || depth > ssa::MAX_DEPTH {
                return Err("module local expression limit".into());
            }
            match e {
                Expr::Register(r) if r.0 >= RAW => {
                    return Err("invalid module local source register".into());
                }
                Expr::Binary(_, a, b) => pending.extend([(&**b, depth + 1), (&**a, depth + 1)]),
                Expr::Load { address, .. } => pending.push((address, depth + 1)),
                Expr::Select {
                    condition,
                    taken,
                    not_taken,
                } => pending.extend([
                    (&**not_taken, depth + 1),
                    (&**taken, depth + 1),
                    (&**condition, depth + 1),
                ]),
                _ => {}
            }
        }
        Ok(())
    }
}

/// Recover immutable per-function plans. A local limit or source mismatch
/// returns a whole-function fallback, never a partial execution plan.
pub fn recover(
    program: &module_ir::Program,
    values: &module_values::Analysis,
) -> Result<Plan, String> {
    if program.functions().len() > MAX_FUNCTIONS
        || program.register_count() != RAW
        || values.functions.len() != program.functions().len()
    {
        return Err("module local source/function limit or mismatch".into());
    }
    let mut budget = Budget {
        work: MAX_WORK,
        members: 0,
        nodes: 0,
    };
    let mut functions = Vec::with_capacity(program.functions().len());
    for (function, analysis) in program.functions().iter().zip(&values.functions) {
        let result = if function != &analysis.function {
            Err("module local source function mismatch".into())
        } else {
            analysis
                .result
                .as_ref()
                .map_err(Clone::clone)
                .and_then(|v| function_plan(program, function, v, &mut budget))
        };
        functions.push(FunctionLocals {
            address: function.address,
            result,
        });
    }
    Ok(Plan { functions })
}

fn function_plan(
    program: &module_ir::Program,
    function: &module_ir::Function,
    values: &FunctionValues,
    budget: &mut Budget,
) -> Result<Locals, String> {
    let end = function
        .address
        .checked_add(function.size)
        .ok_or("module local function overflow")?;
    let first = program
        .instructions()
        .partition_point(|i| i.address() < function.address);
    let last = program
        .instructions()
        .partition_point(|i| i.address() < end);
    let source = &program.instructions()[first..last];
    let graph = values.graph();
    let recovery = values.local_recovery().as_ref().map_err(Clone::clone)?;
    let plan = &recovery.plan;
    if source.is_empty()
        || source.len() > ssa::MAX_INSTRUCTIONS
        || source.len() != values.source_instructions()
        || values.guest_registers() != RAW
        || graph.entry != function.address
        || graph.register_count != RAW + 1
        || graph.values.len() > ssa::MAX_VALUES
        || graph.blocks.len() > ssa::MAX_BLOCKS
        || plan.by_value.len() != graph.values.len()
        || plan.local_count > parallel_copy::MAX_LOCALS
        || plan.by_value.iter().any(|id| *id >= plan.local_count)
    {
        return Err("module local analysis/source limit or mismatch".into());
    }
    budget.reserve(source.len() + graph.values.len() + plan.local_count + 2)?;
    let mut metadata = Vec::with_capacity(source.len());
    let mut source_assignments = 0usize;
    for instruction in source {
        budget.spend(1)?;
        for assignment in assignments(instruction) {
            source_assignments += 1;
            if source_assignments > ssa::MAX_ASSIGNMENTS {
                return Err("module local assignment limit".into());
            }
            match &assignment.destination {
                Place::Register(r) if r.0 >= RAW => {
                    return Err("invalid module local destination".into());
                }
                Place::Memory { address, .. } => budget.scan(address)?,
                _ => {}
            }
            budget.scan(&assignment.value)?;
        }
        let control = match instruction {
            Instruction::StoreString { .. } => {
                return Err("string stores require explicit repeated memory SSA effects".into());
            }
            Instruction::Divide { source, .. } => {
                budget.scan(source)?;
                Control::Jump(
                    instruction
                        .address()
                        .checked_add(u64::from(instruction.size()))
                        .ok_or("module local division continuation overflow")?,
                )
            }
            Instruction::Core(i) => match &i.control {
                Control::Branch { condition, target } => {
                    budget.scan(condition)?;
                    Control::Branch {
                        condition: Expr::Const(0),
                        target: *target,
                    }
                }
                Control::Return(e) => {
                    budget.scan(e)?;
                    Control::Return(Expr::Const(0))
                }
                c => c.clone(),
            },
            Instruction::Vector(v) => {
                if let Some(memory) = &v.memory {
                    budget.scan(&memory.address)?;
                }
                Control::Next
            }
            Instruction::Transfer { target, link, .. } => {
                if let module_ir::Target::Value(e) = target {
                    budget.scan(e)?;
                }
                link.map(Control::Jump)
                    .unwrap_or(Control::Return(Expr::Const(0)))
            }
            Instruction::Return { .. } => Control::Return(Expr::Const(0)),
        };
        metadata.push(IrInstruction {
            address: instruction.address(),
            size: instruction.size(),
            assignments: Vec::new(),
            control,
        });
    }
    let metadata =
        ir::Program::new(function.address, RAW + 1, metadata).map_err(|e| e.to_string())?;
    let cfg = metadata.cfg();
    let reachable = cfg.reachable_blocks();
    budget.spend(cfg.blocks().len())?;
    if reachable.len() != cfg.blocks().len() || graph.blocks.len() != reachable.len() {
        return Err("module local requires reachable coverage of every decoded instruction".into());
    }
    let blocks: BTreeMap<_, _> = graph.blocks.iter().map(|b| (b.start, b)).collect();
    let live: BTreeMap<_, _> = values
        .lifetimes()
        .blocks
        .iter()
        .map(|b| (b.start, b))
        .collect();
    if blocks.len() != graph.blocks.len()
        || live.len() != blocks.len()
        || cfg
            .blocks()
            .iter()
            .any(|b| !blocks.contains_key(&b.start) || !live.contains_key(&b.start))
    {
        return Err("module local CFG/SSA coverage mismatch".into());
    }
    let mut expected_edges = BTreeSet::from([(None, function.address)]);
    for block in cfg.blocks() {
        for edge in &block.successors {
            budget.spend(1)?;
            let crate::cfg::Target::Block(to) = edge.target else {
                return Err("module local unresolved CFG edge".into());
            };
            expected_edges.insert((Some(block.start), cfg.block(to).start));
        }
    }
    budget.spend(values.lifetimes().edges.len())?;
    let actual_edges: BTreeSet<_> = values
        .lifetimes()
        .edges
        .iter()
        .map(|e| (e.from, e.to))
        .collect();
    if actual_edges != expected_edges || actual_edges.len() != values.lifetimes().edges.len() {
        return Err("module local CFG/SSA edge mismatch".into());
    }
    // All source reads and writes are demanded, even dead writes and lazy arms.
    // Synthetic return/call observations do not seed the executable demand.
    let mut demand = vec![false; graph.values.len()];
    let mut pending = Vec::new();
    let mut point_count = 0usize;
    for block in &graph.blocks {
        for point in &block.points {
            point_count += 1;
            if point_count > ssa::MAX_NODES || point.reads.len() > ssa::MAX_NODES {
                return Err("module local point limit".into());
            }
            budget.spend(1 + point.reads.len())?;
            if matches!(
                values.roles().get(&point.site),
                Some(PointRole::Assignment { .. } | PointRole::VectorAssignment { .. })
            ) {
                if let Some(id) = point.definition {
                    pending.push(id);
                }
                pending.extend(point.reads.iter().map(|r| r.value));
            }
        }
    }
    budget.reserve(pending.len())?;
    while let Some(id) = pending.pop() {
        budget.spend(1)?;
        let bit = demand
            .get_mut(id.0)
            .ok_or("module local invalid demand identity")?;
        if std::mem::replace(bit, true) {
            continue;
        }
        if let Definition::Phi { inputs, .. } = &graph.values[id.0] {
            budget.reserve(inputs.len())?;
            pending.extend(inputs.iter().map(|i| i.value));
        }
    }
    let mut edges: BTreeMap<(u64, u64), Vec<Copy>> = BTreeMap::new();
    for (id, definition) in graph.values.iter().enumerate() {
        budget.spend(1)?;
        if demand[id]
            && let Definition::Phi { block, inputs, .. } = definition
        {
            for input in inputs {
                budget.spend(1)?;
                let source = *plan
                    .by_value
                    .get(input.value.0)
                    .ok_or("module local phi identity")?;
                if let Some(from) = input.predecessor {
                    let destination = plan.by_value[id];
                    if destination != source {
                        budget.reserve(1)?;
                        edges.entry((from, *block)).or_default().push(Copy {
                            destination,
                            source,
                        });
                    }
                }
            }
        }
    }
    // Filtering a previously scheduled edge is incorrect for cycles. Schedule
    // the demanded parallel set afresh, then check it with the symbolic proof.
    for copies in edges.values_mut() {
        budget.spend(copies.len() * (copies.len().checked_ilog2().unwrap_or(0) as usize + 1))?;
        copies.sort_unstable_by_key(|c| c.destination);
        let schedule = parallel_copy::schedule(plan.local_count, copies)?;
        budget.reserve(schedule.copies.len())?;
        parallel_copy::validate(plan.local_count, copies, &schedule.copies)?;
        *copies = schedule.copies;
    }
    let mut steps = BTreeMap::new();
    let mut used = BTreeSet::new();
    for block in cfg.blocks() {
        let ssa_block = blocks[&block.start];
        let live_block = live[&block.start];
        budget.spend(ssa_block.points.len() + live_block.points.len())?;
        if ssa_block.points.len() != live_block.points.len() {
            return Err("module local point liveness mismatch".into());
        }
        let mut point_ranges = BTreeMap::new();
        let mut at = 0usize;
        for index in block.instructions.clone() {
            let address = source[index].address();
            let start = at;
            while at < ssa_block.points.len() && ssa_block.points[at].site.instruction == address {
                at += 1;
            }
            point_ranges.insert(address, start..at);
        }
        if at != ssa_block.points.len() {
            return Err("module local point instruction mismatch".into());
        }
        // A no-op or jump has no SSA point. Propagate the adjacent checked
        // live sets backward so it receives the same precise resume contract.
        let mut before = BTreeMap::new();
        let mut cursor: &[ValueId] = &live_block.live_out;
        for index in block.instructions.clone().rev() {
            let address = source[index].address();
            for p in point_ranges[&address].clone().rev() {
                let point = &ssa_block.points[p];
                let lifetime = &live_block.points[p];
                budget.spend(cursor.len() + lifetime.after.len() + 1)?;
                if point.site != lifetime.site || cursor != lifetime.after {
                    return Err("module local inconsistent point liveness".into());
                }
                cursor = &lifetime.before;
            }
            before.insert(address, cursor);
        }
        if cursor != live_block.live_in {
            return Err("module local block liveness mismatch".into());
        }
        let mut current = [None; RAW + 1];
        for id in &ssa_block.phis {
            budget.spend(1)?;
            match graph.values.get(id.0) {
                Some(Definition::Phi {
                    block: owner,
                    register,
                    ..
                }) if *owner == block.start && register.0 <= RAW => {
                    if current[register.0].replace(*id).is_some() {
                        return Err("module local duplicate phi register".into());
                    }
                }
                _ => return Err("module local phi source mismatch".into()),
            }
        }
        for index in block.instructions.clone() {
            let instruction = &source[index];
            let address = instruction.address();
            let resume = bindings(before[&address], &demand, &current, graph, plan, budget)?;
            budget.reserve(resume.len() + 1)?;
            used.extend(resume.iter().map(|b| b.local));
            let mut step = StepLocals {
                resume,
                assignments: Vec::new(),
                after: Vec::new(),
            };
            let mut seen = vec![false; assignments(instruction).len()];
            if let Instruction::Divide { width, .. } = instruction {
                // Check complete coverage independently of the event producer:
                // source observation, dividend inputs, then fresh results.
                let registers: &[Reg] = if *width == ir::Width::U8 {
                    &[Reg(crate::x86::RAX)]
                } else {
                    &[Reg(crate::x86::RAX), Reg(crate::x86::RDX)]
                };
                let range = point_ranges[&address].clone();
                if range.len() != 1 + registers.len() * 2 {
                    return Err("module local division event coverage mismatch".into());
                }
                for (event, p) in range.enumerate() {
                    budget.spend(1)?;
                    let point = &ssa_block.points[p];
                    let (role, register) = if event == 0 {
                        (PointRole::DivideSource, Reg(RAW))
                    } else if event <= registers.len() {
                        (
                            PointRole::Input {
                                register: registers[event - 1],
                            },
                            Reg(RAW),
                        )
                    } else {
                        let register = registers[event - 1 - registers.len()];
                        (PointRole::OpaqueOutput { register }, register)
                    };
                    if point.site.assignment != Some(event)
                        || values.roles().get(&point.site) != Some(&role)
                        || point.definition.and_then(|id| graph.values.get(id.0))
                            != Some(&Definition::Assignment {
                                site: point.site,
                                register,
                            })
                    {
                        return Err("module local division event role/definition mismatch".into());
                    }
                }
            }
            for p in point_ranges[&address].clone() {
                let point = &ssa_block.points[p];
                for read in &point.reads {
                    budget.spend(1)?;
                    if current.get(read.register.0).copied().flatten() != Some(read.value) {
                        return Err("module local read does not name current raw register".into());
                    }
                }
                let role = values.roles().get(&point.site);
                let original = match (instruction, role) {
                    (Instruction::Core(_), Some(PointRole::Assignment { original })) => {
                        Some(*original)
                    }
                    (Instruction::Vector(_), Some(PointRole::VectorAssignment { original })) => {
                        Some(*original)
                    }
                    (
                        _,
                        Some(PointRole::Assignment { .. } | PointRole::VectorAssignment { .. }),
                    ) => return Err("module local source assignment role mismatch".into()),
                    _ => None,
                };
                if let Some(original) = original {
                    let a = assignments(instruction)
                        .get(original)
                        .ok_or("module local source assignment index")?;
                    if std::mem::replace(
                        seen.get_mut(original)
                            .ok_or("module local source assignment index")?,
                        true,
                    ) {
                        return Err("module local duplicate source assignment".into());
                    }
                    let expected_site = original
                        + usize::from(
                            matches!(instruction, Instruction::Vector(v) if v.memory.is_some()),
                        );
                    if point.site.assignment != Some(expected_site) {
                        return Err("module local source site mismatch".into());
                    }
                    let mut reads = Reads {
                        point,
                        at: 0,
                        plan,
                        budget,
                    };
                    let rewritten = match &a.destination {
                        Place::Register(register) => {
                            let id = point
                                .definition
                                .ok_or("module local missing source definition")?;
                            if graph.values.get(id.0)
                                != Some(&Definition::Assignment {
                                    site: point.site,
                                    register: *register,
                                })
                            {
                                return Err("module local source destination mismatch".into());
                            }
                            let local = Reg(RAW + plan.by_value[id.0]);
                            let value = reads.expression(&a.value)?;
                            let mut assignments = Vec::with_capacity(2);
                            if value != Expr::Register(local) {
                                assignments.push(Assignment {
                                    destination: local.into(),
                                    value,
                                });
                            }
                            assignments.push(Assignment {
                                destination: (*register).into(),
                                value: Expr::Register(local),
                            });
                            assignments
                        }
                        Place::Memory { address, width } => {
                            if point.definition.is_some() {
                                return Err("module local store definition mismatch".into());
                            }
                            vec![Assignment {
                                destination: Place::Memory {
                                    address: reads.expression(address)?,
                                    width: *width,
                                },
                                value: reads.expression(&a.value)?,
                            }]
                        }
                    };
                    if reads.at != point.reads.len() {
                        return Err("module local unconsumed source reads".into());
                    }
                    step.assignments.extend(rewritten);
                } else {
                    validate_observation(instruction, point, role, budget)?;
                }
                if let Some(id) = point.definition {
                    let Some(Definition::Assignment { site, register }) = graph.values.get(id.0)
                    else {
                        return Err("module local definition kind".into());
                    };
                    if *site != point.site || register.0 > RAW {
                        return Err("module local definition site/register".into());
                    }
                    current[register.0] = Some(id);
                }
            }
            if seen.iter().any(|b| !b) {
                return Err("module local missing original assignment point".into());
            }
            if index + 1 == block.instructions.end {
                for exit in &ssa_block.exit_values {
                    budget.spend(1)?;
                    if current.get(exit.register.0).copied().flatten() != Some(exit.value) {
                        return Err("module local exit register mismatch".into());
                    }
                }
                if matches!(
                    instruction,
                    Instruction::Transfer { link: Some(_), .. } | Instruction::Divide { .. }
                ) {
                    for binding in
                        bindings(&live_block.live_out, &demand, &current, graph, plan, budget)?
                    {
                        step.after.push(Assignment {
                            destination: Reg(RAW + binding.local).into(),
                            value: Expr::Register(binding.register),
                        });
                    }
                }
                append_edges(
                    &mut step.after,
                    instruction,
                    block.start,
                    &edges,
                    plan.local_count,
                    budget,
                )?;
            }
            budget.reserve(step.assignments.len() + step.after.len())?;
            for a in step.assignments.iter().chain(&step.after) {
                collect_used(a, &mut used, budget)?;
            }
            steps.insert(address, step);
        }
    }
    if steps.len() != source.len() {
        return Err("module local incomplete source coverage".into());
    }
    budget.reserve(used.len())?;
    let mut locals = Locals {
        local_count: plan.local_count,
        used_locals: used.into_iter().collect(),
        steps,
    };
    dense_names(&mut locals, budget)?;
    Ok(locals)
}

// Analysis-only slots and private initial values can leave gaps in the used
// colors. Give displayed locals dense IDs while retaining the two special temps.
fn dense_names(locals: &mut Locals, budget: &mut Budget) -> Result<(), String> {
    let old_count = locals.local_count;
    budget.reserve(old_count + 2)?;
    let mut names = vec![usize::MAX; old_count + 2];
    let mut count = 0;
    for &old in &locals.used_locals {
        if old < old_count {
            names[old] = count;
            count += 1;
        }
    }
    names[old_count] = count;
    names[old_count + 1] = count + 1;
    let rename = |register: &mut Reg| -> Result<(), String> {
        if register.0 >= RAW {
            let name = names
                .get(register.0 - RAW)
                .filter(|&&n| n != usize::MAX)
                .ok_or("module local missing display name")?;
            register.0 = RAW + name;
        }
        Ok(())
    };
    for step in locals.steps.values_mut() {
        for binding in &mut step.resume {
            budget.spend(1)?;
            binding.local = names[binding.local];
        }
        for assignment in step.assignments.iter_mut().chain(&mut step.after) {
            let mut pending = vec![&mut assignment.value];
            match &mut assignment.destination {
                Place::Register(r) => rename(r)?,
                Place::Memory { address, .. } => pending.push(address),
            }
            while let Some(expression) = pending.pop() {
                budget.spend(1)?;
                match expression {
                    Expr::Register(r) => rename(r)?,
                    Expr::Binary(_, a, b) => pending.extend([&mut **a, &mut **b]),
                    Expr::Load { address, .. } => pending.push(address),
                    Expr::Select {
                        condition,
                        taken,
                        not_taken,
                    } => pending.extend([&mut **condition, &mut **taken, &mut **not_taken]),
                    Expr::Const(_) => {}
                }
            }
        }
    }
    for name in &mut locals.used_locals {
        *name = names[*name];
    }
    locals.local_count = count;
    Ok(())
}

fn assignments(instruction: &Instruction) -> &[Assignment] {
    match instruction {
        Instruction::Core(i) => &i.assignments,
        Instruction::Vector(i) => &i.assignments,
        _ => &[],
    }
}

fn bindings(
    live: &[ValueId],
    demand: &[bool],
    current: &[Option<ValueId>],
    graph: &ssa::SsaFunction,
    plan: &crate::ssa_locals::Plan,
    budget: &mut Budget,
) -> Result<Vec<Binding>, String> {
    let mut bindings = BTreeMap::new();
    for id in live {
        budget.spend(1)?;
        if !*demand.get(id.0).ok_or("module local live identity")? {
            continue;
        }
        let register = match graph.values.get(id.0) {
            Some(
                Definition::Initial { register }
                | Definition::Assignment { register, .. }
                | Definition::Phi { register, .. },
            ) => *register,
            None => return Err("module local live definition".into()),
        };
        if register.0 >= RAW || current[register.0] != Some(*id) {
            return Err("module local resume value does not name current raw register".into());
        }
        if bindings.insert(plan.by_value[id.0], register).is_some() {
            return Err("module local conflicting live local bindings".into());
        }
    }
    Ok(bindings
        .into_iter()
        .map(|(local, register)| Binding { local, register })
        .collect())
}

struct Reads<'a> {
    point: &'a PointValues,
    at: usize,
    plan: &'a crate::ssa_locals::Plan,
    budget: &'a mut Budget,
}
impl Reads<'_> {
    fn expression(&mut self, e: &Expr) -> Result<Expr, String> {
        self.budget.spend(1)?;
        Ok(match e {
            Expr::Const(v) => Expr::Const(*v),
            Expr::Register(register) => {
                let read = self
                    .point
                    .reads
                    .get(self.at)
                    .ok_or("module local missing ordered read")?;
                self.at += 1;
                if read.register != *register {
                    return Err("module local source read order mismatch".into());
                }
                Expr::Register(Reg(RAW
                    + *self
                        .plan
                        .by_value
                        .get(read.value.0)
                        .ok_or("module local read identity")?))
            }
            Expr::Binary(op, a, b) => Expr::binary(*op, self.expression(a)?, self.expression(b)?),
            Expr::Load { address, width } => Expr::load(self.expression(address)?, *width),
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => Expr::select(
                self.expression(condition)?,
                self.expression(taken)?,
                self.expression(not_taken)?,
            ),
        })
    }
}

fn validate_observation(
    instruction: &Instruction,
    point: &PointValues,
    role: Option<&PointRole>,
    budget: &mut Budget,
) -> Result<(), String> {
    let expression = match (instruction, role) {
        (Instruction::Core(i), None) if point.site.assignment.is_none() => match &i.control {
            Control::Branch { condition, .. } | Control::Return(condition) => {
                Some(condition.clone())
            }
            _ => return Err("module local unexpected control point".into()),
        },
        (Instruction::Vector(v), Some(PointRole::VectorGuard)) => Some(
            v.memory
                .as_ref()
                .ok_or("module local unexpected vector guard")?
                .address
                .clone(),
        ),
        (Instruction::Divide { source, .. }, Some(PointRole::DivideSource)) => Some(source.clone()),
        (Instruction::Transfer { target, .. }, Some(PointRole::Target)) => Some(match target {
            module_ir::Target::Value(e) => e.clone(),
            module_ir::Target::Plt(address) => Expr::load(Expr::Const(*address), ir::Width::U64),
        }),
        (Instruction::Return { .. }, Some(PointRole::Target)) => Some(Expr::load(
            Expr::Register(Reg(crate::x86::RSP)),
            ir::Width::U64,
        )),
        (
            Instruction::Transfer { .. } | Instruction::Return { .. } | Instruction::Divide { .. },
            Some(PointRole::Input { register }),
        ) => Some(Expr::Register(*register)),
        (
            Instruction::Transfer { link: Some(_), .. } | Instruction::Divide { .. },
            Some(PointRole::OpaqueOutput { register }),
        ) => {
            if !point.reads.is_empty() || point.definition.is_none() || register.0 >= RAW {
                return Err("module local opaque output mismatch".into());
            }
            None
        }
        (Instruction::Transfer { link: None, .. } | Instruction::Return { .. }, None)
            if point.site.assignment.is_none() =>
        {
            Some(Expr::Const(0))
        }
        _ => return Err("module local unexpected observation role".into()),
    };
    if let Some(expression) = expression {
        let mut expected = Vec::new();
        let mut pending = vec![&expression];
        while let Some(e) = pending.pop() {
            budget.spend(1)?;
            match e {
                Expr::Register(r) => expected.push(*r),
                Expr::Binary(_, a, b) => pending.extend([&**b, &**a]),
                Expr::Load { address, .. } => pending.push(address),
                Expr::Select {
                    condition,
                    taken,
                    not_taken,
                } => pending.extend([&**not_taken, &**taken, &**condition]),
                _ => {}
            }
        }
        if expected.len() != point.reads.len()
            || expected
                .iter()
                .zip(&point.reads)
                .any(|(r, v)| *r != v.register)
        {
            return Err("module local observation source reads mismatch".into());
        }
    }
    Ok(())
}

fn append_edges(
    out: &mut Vec<Assignment>,
    instruction: &Instruction,
    from: u64,
    edges: &BTreeMap<(u64, u64), Vec<Copy>>,
    count: usize,
    budget: &mut Budget,
) -> Result<(), String> {
    let next = instruction
        .address()
        .checked_add(u64::from(instruction.size()))
        .ok_or("module local next overflow")?;
    let mut append = |target, guard: Option<(Reg, bool)>| -> Result<(), String> {
        if let Some(copies) = edges.get(&(from, target)) {
            budget.reserve(copies.len())?;
            for copy in copies {
                let destination = Reg(RAW + copy.destination);
                let source = Expr::Register(Reg(RAW + copy.source));
                let value = match guard {
                    Some((condition, true)) => Expr::select(
                        Expr::Register(condition),
                        source,
                        Expr::Register(destination),
                    ),
                    Some((condition, false)) => Expr::select(
                        Expr::Register(condition),
                        Expr::Register(destination),
                        source,
                    ),
                    None => source,
                };
                out.push(Assignment {
                    destination: destination.into(),
                    value,
                });
            }
        }
        Ok(())
    };
    match instruction {
        Instruction::Core(i) => match &i.control {
            Control::Branch { condition, target } if *target != next => {
                if edges.contains_key(&(from, *target)) || edges.contains_key(&(from, next)) {
                    // Use the original canonical expression. Synthetic liveness
                    // need not provide locals for branch-only register reads.
                    let temporary = Reg(RAW + count + 1);
                    budget.reserve(1)?;
                    out.push(Assignment {
                        destination: temporary.into(),
                        value: condition.clone(),
                    });
                    for (to, taken) in [(*target, true), (next, false)] {
                        if let Some(copies) = edges.get(&(from, to)) {
                            budget.reserve(copies.len())?;
                            for copy in copies {
                                let destination = Reg(RAW + copy.destination);
                                let source = Expr::Register(Reg(RAW + copy.source));
                                let old = Expr::Register(destination);
                                let value = if taken {
                                    Expr::select(Expr::Register(temporary), source, old)
                                } else {
                                    Expr::select(Expr::Register(temporary), old, source)
                                };
                                out.push(Assignment {
                                    destination: destination.into(),
                                    value,
                                });
                            }
                        }
                    }
                }
            }
            Control::Branch { target, .. } | Control::Jump(target) => append(*target, None)?,
            Control::Next => append(next, None)?,
            Control::Return(_) => {}
        },
        Instruction::Vector(_) | Instruction::StoreString { .. } => append(next, None)?,
        Instruction::Divide { .. } => append(next, None)?,
        Instruction::Transfer {
            link: Some(link), ..
        } => append(*link, None)?,
        Instruction::Transfer { link: None, .. } | Instruction::Return { .. } => {}
    }
    Ok(())
}

fn collect_used(
    a: &Assignment,
    used: &mut BTreeSet<usize>,
    budget: &mut Budget,
) -> Result<(), String> {
    let mut pending = vec![&a.value];
    match &a.destination {
        Place::Register(r) if r.0 >= RAW => {
            used.insert(r.0 - RAW);
        }
        Place::Memory { address, .. } => pending.push(address),
        _ => {}
    }
    while let Some(e) = pending.pop() {
        budget.spend(1)?;
        match e {
            Expr::Register(r) if r.0 >= RAW => {
                used.insert(r.0 - RAW);
            }
            Expr::Binary(_, a, b) => pending.extend([&**b, &**a]),
            Expr::Load { address, .. } => pending.push(address),
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => pending.extend([&**not_taken, &**taken, &**condition]),
            _ => {}
        }
    }
    Ok(())
}

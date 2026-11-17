//! Independent inductive validation of C storage assignment.
//!
//! A fact for a mapped register says that its current original value equals
//! the value in its C slot. The entry boundary is empty: local slots initially
//! contain arbitrary poison. The unchanged IR operations retain checked memory,
//! faults and traces under this u64-slot correspondence. C widths, rendering and
//! the final original register file are outside this check.

use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::fmt;

use crate::cfg::Target;
use crate::ir::{Control, Expr, Place, Program, Reg};

pub const MAX_MAPPED_REGISTERS: usize = 4_096;
pub const MAX_ACTIVE_REGISTERS: usize = 8_192;
pub const MAX_BLOCKS: usize = 4_096;
pub const MAX_POINTS: usize = 100_000;
pub const MAX_ITEMS: usize = 250_000;
pub const MAX_EXPRESSION_DEPTH: usize = 128;
pub const MAX_STATE_CELLS: usize = 1_000_000;
pub const MAX_WORK: usize = 8_000_000;
pub const MAX_BLOCK_VISITS: usize = 100_000;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct AllocationEvidence {
    /// Reachable blocks included in the fixed point.
    pub blocks: usize,
    /// Reachable mapped-register read occurrences, including lazy arms.
    pub register_reads: usize,
    pub mapped_registers: usize,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum AllocationError {
    Malformed {
        register: Option<Reg>,
        detail: &'static str,
    },
    ReadCorrespondence {
        instruction: u64,
        assignment: Option<usize>,
        register: Reg,
        color: usize,
    },
    Unavailable {
        resource: &'static str,
    },
}

impl AllocationError {
    pub fn is_resource_limit(&self) -> bool {
        matches!(self, Self::Unavailable { .. })
    }
}
impl fmt::Display for AllocationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Malformed { register, detail } => {
                write!(f, "invalid allocation mapping {register:?}: {detail}")
            }
            Self::ReadCorrespondence {
                instruction,
                assignment,
                register,
                color,
            } => write!(
                f,
                "r{} is unavailable in C slot {color} at {instruction:#x}, assignment {assignment:?}",
                register.0
            ),
            Self::Unavailable { resource } => {
                write!(f, "allocation validation unavailable: {resource} limit")
            }
        }
    }
}
impl std::error::Error for AllocationError {}

type Result<T> = std::result::Result<T, AllocationError>;
type Facts = BTreeSet<usize>;
fn unavailable(resource: &'static str) -> AllocationError {
    AllocationError::Unavailable { resource }
}
fn malformed(register: Option<Reg>, detail: &'static str) -> AllocationError {
    AllocationError::Malformed { register, detail }
}

struct Work(usize);
impl Work {
    fn spend(&mut self, amount: usize) -> Result<()> {
        self.0 = self
            .0
            .checked_sub(amount)
            .ok_or_else(|| unavailable("work"))?;
        Ok(())
    }
}

struct Mapping {
    registers: Vec<Reg>,
    colors: Vec<usize>,
    by_register: BTreeMap<usize, usize>,
    groups: Vec<Vec<usize>>,
    group_of: Vec<usize>,
}
impl Mapping {
    fn new(program: &Program, mapping: &[(Reg, usize)], work: &mut Work) -> Result<Self> {
        if mapping.len() > MAX_MAPPED_REGISTERS {
            return Err(unavailable("mapped registers"));
        }
        let mut ordered = BTreeMap::new();
        for &(reg, color) in mapping {
            work.spend(1)?;
            if reg.0 >= program.register_count() {
                return Err(malformed(Some(reg), "register out of range"));
            }
            if ordered.insert(reg.0, color).is_some() {
                return Err(malformed(Some(reg), "duplicate register"));
            }
        }
        let mut registers = Vec::new();
        let mut colors = Vec::new();
        let mut by_register = BTreeMap::new();
        let mut by_color: BTreeMap<usize, Vec<usize>> = BTreeMap::new();
        for (index, (reg, color)) in ordered.into_iter().enumerate() {
            registers.push(Reg(reg));
            colors.push(color);
            by_register.insert(reg, index);
            by_color.entry(color).or_default().push(index);
        }
        let groups: Vec<_> = by_color.into_values().collect();
        let mut group_of = vec![0; registers.len()];
        for (group, members) in groups.iter().enumerate() {
            for &member in members {
                group_of[member] = group;
            }
        }
        Ok(Self {
            registers,
            colors,
            by_register,
            groups,
            group_of,
        })
    }
}

struct Write {
    destination: usize,
    same_slot_copy: bool,
}
struct Operation {
    instruction: u64,
    assignment: Option<usize>,
    reads: Vec<usize>,
    write: Option<Write>,
}

/// Validate exactly the supplied local-to-color mapping. Unmapped registers
/// retain separate original storage; sparse register/color labels are allowed.
/// No allocation graph or allocator helper is used.
pub fn validate(program: &Program, mapping: &[(Reg, usize)]) -> Result<AllocationEvidence> {
    let mut work = Work(MAX_WORK);
    let mapping = Mapping::new(program, mapping, &mut work)?;
    bounds(program, &mut work)?;
    let cfg = program.cfg();
    let reachable = cfg.reachable_blocks();
    // Account for both retained boundary states, TOP, and temporary clones
    // before allocating any dataflow facts.
    let state_cells = reachable
        .len()
        .checked_mul(2)
        .and_then(|n| n.checked_add(4))
        .and_then(|n| n.checked_mul(mapping.registers.len()))
        .ok_or_else(|| unavailable("state cells"))?;
    if state_cells > MAX_STATE_CELLS {
        return Err(unavailable("state cells"));
    }
    work.spend(state_cells)?;
    let mut reachable_instruction = vec![false; program.instructions().len()];
    for &id in &reachable {
        for index in cfg.block(id).instructions.clone() {
            reachable_instruction[index] = true;
        }
    }
    let mut offsets = Vec::with_capacity(program.instructions().len() + 1);
    let mut operations = Vec::new();
    let mut register_reads = 0;
    for (index, instruction) in program.instructions().iter().enumerate() {
        offsets.push(operations.len());
        work.spend(1)?;
        if !reachable_instruction[index] {
            continue;
        }
        for (assignment, value) in instruction.assignments.iter().enumerate() {
            work.spend(1)?;
            let mut operation = Operation {
                instruction: instruction.address,
                assignment: Some(assignment),
                reads: Vec::new(),
                write: None,
            };
            if let Place::Memory { address, .. } = &value.destination {
                reads(address, &mapping, &mut operation.reads, &mut work)?;
            }
            reads(&value.value, &mapping, &mut operation.reads, &mut work)?;
            if let Place::Register(destination) = value.destination
                && let Some(&destination) = mapping.by_register.get(&destination.0)
            {
                let same_slot_copy = match value.value {
                    Expr::Register(source) => {
                        mapping.by_register.get(&source.0).is_some_and(|&source| {
                            mapping.group_of[source] == mapping.group_of[destination]
                        })
                    }
                    _ => false,
                };
                operation.write = Some(Write {
                    destination,
                    same_slot_copy,
                });
            }
            register_reads += operation.reads.len();
            operations.push(operation);
        }
        let mut operation = Operation {
            instruction: instruction.address,
            assignment: None,
            reads: Vec::new(),
            write: None,
        };
        match &instruction.control {
            Control::Branch { condition, .. } | Control::Return(condition) => {
                reads(condition, &mapping, &mut operation.reads, &mut work)?
            }
            _ => {}
        }
        register_reads += operation.reads.len();
        operations.push(operation);
    }
    offsets.push(operations.len());

    let top: Facts = (0..mapping.registers.len()).collect();
    let mut incoming = vec![Facts::new(); cfg.blocks().len()];
    let mut outgoing = incoming.clone();
    for &id in &reachable {
        incoming[id.index()] = top.clone();
        outgoing[id.index()] = top.clone();
    }
    let mut pending: VecDeque<_> = reachable.iter().copied().collect();
    let mut queued = vec![false; cfg.blocks().len()];
    for &id in &reachable {
        queued[id.index()] = true;
    }
    let mut visits = MAX_BLOCK_VISITS;
    while let Some(id) = pending.pop_front() {
        visits = visits
            .checked_sub(1)
            .ok_or_else(|| unavailable("block visits"))?;
        queued[id.index()] = false;
        work.spend(1)?;
        let block = cfg.block(id);
        let mut before = if id == cfg.entry() {
            Facts::new()
        } else {
            work.spend(top.len())?;
            top.clone()
        };
        let mut predecessors = 0;
        for pred in block.predecessors.iter().filter(|p| reachable.contains(p)) {
            predecessors += 1;
            work.spend(before.len() + outgoing[pred.index()].len())?;
            before.retain(|reg| outgoing[pred.index()].contains(reg));
        }
        if id != cfg.entry() && predecessors == 0 {
            return Err(malformed(None, "reachable block without predecessor"));
        }
        work.spend(before.len())?;
        incoming[id.index()] = before.clone();
        let mut after = before;
        for operation in
            &operations[offsets[block.instructions.start]..offsets[block.instructions.end]]
        {
            transfer(operation, &mapping, &mut after, &mut work)?;
        }
        if after != outgoing[id.index()] {
            outgoing[id.index()] = after;
            for edge in &block.successors {
                let Target::Block(next) = edge.target else {
                    return Err(malformed(None, "unresolved reachable edge"));
                };
                if !queued[next.index()] {
                    pending.push_back(next);
                    queued[next.index()] = true;
                }
            }
        }
    }
    // Reads are checked only after convergence, against the local pre-write
    // facts. A copy preserves aliases only if its source read is justified here.
    for &id in &reachable {
        let block = cfg.block(id);
        work.spend(incoming[id.index()].len())?;
        let mut facts = incoming[id.index()].clone();
        for operation in
            &operations[offsets[block.instructions.start]..offsets[block.instructions.end]]
        {
            for &reg in &operation.reads {
                work.spend(1)?;
                if !facts.contains(&reg) {
                    return Err(AllocationError::ReadCorrespondence {
                        instruction: operation.instruction,
                        assignment: operation.assignment,
                        register: mapping.registers[reg],
                        color: mapping.colors[reg],
                    });
                }
            }
            transfer(operation, &mapping, &mut facts, &mut work)?;
        }
    }
    Ok(AllocationEvidence {
        blocks: reachable.len(),
        register_reads,
        mapped_registers: mapping.registers.len(),
    })
}

fn transfer(
    operation: &Operation,
    mapping: &Mapping,
    facts: &mut Facts,
    work: &mut Work,
) -> Result<()> {
    work.spend(1)?;
    if let Some(write) = &operation.write {
        if !write.same_slot_copy {
            let peers = &mapping.groups[mapping.group_of[write.destination]];
            work.spend(peers.len())?;
            for peer in peers {
                facts.remove(peer);
            }
        }
        facts.insert(write.destination);
    }
    Ok(())
}

fn reads(
    expression: &Expr,
    mapping: &Mapping,
    result: &mut Vec<usize>,
    work: &mut Work,
) -> Result<()> {
    let mut pending = vec![expression];
    while let Some(expression) = pending.pop() {
        work.spend(1)?;
        match expression {
            Expr::Register(reg) => {
                if let Some(&index) = mapping.by_register.get(&reg.0) {
                    result.push(index);
                }
            }
            Expr::Const(_) => {}
            Expr::Load { address, .. } => pending.push(address),
            Expr::Binary(_, left, right) => pending.extend([&**right, &**left]),
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => pending.extend([&**not_taken, &**taken, &**condition]),
        }
    }
    Ok(())
}

// Whole-input validation precedes recursive consumers, clones of facts, and
// dataflow state allocation. Unreachable/lazy expressions and store addresses
// count too; large register_count does not cause dense index allocation.
fn bounds(program: &Program, work: &mut Work) -> Result<()> {
    if program.cfg().blocks().len() > MAX_BLOCKS {
        return Err(unavailable("blocks"));
    }
    if program.instructions().len() > MAX_POINTS {
        return Err(unavailable("points"));
    }
    let mut points = program.instructions().len();
    let mut items = points;
    let mut active = BTreeSet::new();
    for instruction in program.instructions() {
        work.spend(1)?;
        points = points
            .checked_add(instruction.assignments.len())
            .ok_or_else(|| unavailable("points"))?;
        if points > MAX_POINTS {
            return Err(unavailable("points"));
        }
        for assignment in &instruction.assignments {
            work.spend(1)?;
            items += 1;
            if let Place::Register(reg) = assignment.destination {
                active.insert(reg.0);
            }
            if let Place::Memory { address, .. } = &assignment.destination {
                expression_bounds(address, &mut items, &mut active, work)?;
            }
            expression_bounds(&assignment.value, &mut items, &mut active, work)?;
        }
        if let Control::Branch { condition, .. } | Control::Return(condition) = &instruction.control
        {
            expression_bounds(condition, &mut items, &mut active, work)?;
        }
    }
    Ok(())
}

fn expression_bounds(
    expression: &Expr,
    items: &mut usize,
    active: &mut BTreeSet<usize>,
    work: &mut Work,
) -> Result<()> {
    let mut pending = vec![(expression, 1)];
    while let Some((expression, depth)) = pending.pop() {
        work.spend(1)?;
        *items += 1;
        if *items > MAX_ITEMS || depth > MAX_EXPRESSION_DEPTH {
            return Err(unavailable("expression items/depth"));
        }
        match expression {
            Expr::Const(_) => {}
            Expr::Register(reg) => {
                active.insert(reg.0);
            }
            Expr::Load { address, .. } => pending.push((address, depth + 1)),
            Expr::Binary(_, left, right) => {
                pending.extend([(&**right, depth + 1), (&**left, depth + 1)])
            }
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => pending.extend([
                (&**not_taken, depth + 1),
                (&**taken, depth + 1),
                (&**condition, depth + 1),
            ]),
        }
        if active.len() > MAX_ACTIVE_REGISTERS {
            return Err(unavailable("active registers"));
        }
    }
    Ok(())
}

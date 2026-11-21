//! Bounded display-only elimination of unobservable pure register assignments.
//!
//! Observations are return values, all guest-memory bytes, and the exact first
//! memory fault (including preceding successful stores). Register snapshots are
//! deliberately outside this contract. Every store and every syntactic load is
//! retained, including loads in unselected `Select` arms. No expression is moved
//! or rewritten. Exceeding any analysis bound declines the transformation.

use crate::model::ir::{Control, Expr, Place, Program};

const MAX_REGISTERS: usize = 4096;
const MAX_INSTRUCTIONS: usize = 16_384;
const MAX_ASSIGNMENTS: usize = 16_384;
const MAX_NODES: usize = 262_144;
const MAX_DEPTH: usize = 128;
const MAX_VISITS: usize = 131_072;
const MAX_WORK: usize = 16_000_000;
// Count u64 cells before allocating fixed-width liveness and write summaries.
const MAX_STATE_CELLS: usize = 2_097_152;
const REGISTER_WORDS: usize = MAX_REGISTERS / 64;

#[derive(Clone, Copy, Eq, PartialEq)]
struct Registers([u64; REGISTER_WORDS]);

impl Default for Registers {
    fn default() -> Self {
        Self([0; REGISTER_WORDS])
    }
}

impl Registers {
    fn insert(&mut self, register: usize) {
        self.0[register / 64] |= 1 << (register % 64);
    }
    fn remove(&mut self, register: usize) {
        self.0[register / 64] &= !(1 << (register % 64));
    }
    fn contains(self, register: usize) -> bool {
        self.0[register / 64] & (1 << (register % 64)) != 0
    }
    fn union(&mut self, other: Self) {
        for (left, right) in self.0.iter_mut().zip(other.0) {
            *left |= right;
        }
    }
}

#[derive(Default)]
struct Budget {
    nodes: usize,
    work: usize,
    visits: usize,
}

impl Budget {
    fn work(&mut self) -> Option<()> {
        self.work = self.work.checked_add(1)?;
        (self.work <= MAX_WORK).then_some(())
    }
    fn words(&mut self) -> Option<()> {
        self.work = self.work.checked_add(REGISTER_WORDS)?;
        (self.work <= MAX_WORK).then_some(())
    }
    fn visit(&mut self) -> Option<()> {
        self.words()?;
        self.visits = self.visits.checked_add(1)?;
        (self.visits <= MAX_VISITS).then_some(())
    }
}

#[derive(Clone, Copy)]
struct Write {
    register: Option<usize>,
    reads: Registers,
    has_load: bool,
}

struct Instruction {
    writes: Vec<Write>,
    control_reads: Registers,
    successors: Vec<usize>,
}

/// Iterative preflight precedes all recursive IR equality, cloning, or rebuilding.
/// Its summaries are inputs to the proposer only; validation reads the AST again.
fn preflight(program: &Program, budget: &mut Budget) -> Option<Vec<Instruction>> {
    let instructions = program.instructions();
    if program.register_count() > MAX_REGISTERS || instructions.len() > MAX_INSTRUCTIONS {
        return None;
    }
    let mut assignments = 0usize;
    // Count cheap collection bounds before allocating per-assignment summaries.
    for instruction in instructions {
        assignments = assignments.checked_add(instruction.assignments.len())?;
        if assignments > MAX_ASSIGNMENTS {
            return None;
        }
    }
    let state_cells = instructions
        .len()
        .checked_mul(3)?
        .checked_add(assignments)?
        .checked_mul(REGISTER_WORDS)?;
    if state_cells > MAX_STATE_CELLS {
        return None;
    }
    let mut result = Vec::with_capacity(instructions.len());
    for instruction in instructions {
        let mut writes = Vec::with_capacity(instruction.assignments.len());
        for assignment in &instruction.assignments {
            budget.words()?;
            let (mut reads, mut has_load) = inspect(&assignment.value, program, budget)?;
            let register = match &assignment.destination {
                Place::Register(register) => {
                    if register.0 >= program.register_count() {
                        return None;
                    }
                    Some(register.0)
                }
                Place::Memory { address, .. } => {
                    let (address_reads, address_load) = inspect(address, program, budget)?;
                    reads.union(address_reads);
                    has_load |= address_load;
                    None
                }
            };
            writes.push(Write {
                register,
                reads,
                has_load,
            });
        }
        let mut successors = Vec::with_capacity(2);
        let mut add_successor = |address| {
            let index = instructions
                .binary_search_by_key(&address, |item| item.address)
                .ok()?;
            successors.push(index);
            Some(())
        };
        let control_reads = match &instruction.control {
            Control::Next => {
                add_successor(
                    instruction
                        .address
                        .checked_add(u64::from(instruction.size))?,
                )?;
                Registers::default()
            }
            Control::Jump(target) => {
                add_successor(*target)?;
                Registers::default()
            }
            Control::Branch { condition, target } => {
                add_successor(*target)?;
                add_successor(
                    instruction
                        .address
                        .checked_add(u64::from(instruction.size))?,
                )?;
                inspect(condition, program, budget)?.0
            }
            Control::Return(value) => inspect(value, program, budget)?.0,
        };
        result.push(Instruction {
            writes,
            control_reads,
            successors,
        });
    }
    Some(result)
}

fn inspect(expression: &Expr, program: &Program, budget: &mut Budget) -> Option<(Registers, bool)> {
    let mut stack = vec![(expression, 1usize)];
    let mut reads = Registers::default();
    let mut has_load = false;
    while let Some((expression, depth)) = stack.pop() {
        budget.nodes = budget.nodes.checked_add(1)?;
        budget.work()?;
        if budget.nodes > MAX_NODES || depth > MAX_DEPTH {
            return None;
        }
        match expression {
            Expr::Const(_) => {}
            Expr::Register(register) => {
                if register.0 >= program.register_count() {
                    return None;
                }
                reads.insert(register.0);
            }
            Expr::Binary(_, left, right) => {
                stack.push((right, depth + 1));
                stack.push((left, depth + 1));
            }
            Expr::Load { address, .. } => {
                has_load = true;
                stack.push((address, depth + 1));
            }
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => {
                stack.push((not_taken, depth + 1));
                stack.push((taken, depth + 1));
                stack.push((condition, depth + 1));
            }
        }
    }
    Some((reads, has_load))
}

/// Propose an instruction-preserving program with dead pure writes removed.
/// `None` means the bounded analysis declined; an unchanged proposal is valid.
pub fn propose(source: &Program) -> Option<Program> {
    let mut budget = Budget::default();
    let model = preflight(source, &mut budget)?;
    let mut inputs = vec![Registers::default(); model.len()];
    loop {
        let mut changed = false;
        for index in (0..model.len()).rev() {
            budget.visit()?;
            let instruction = &model[index];
            let mut live = instruction.control_reads;
            for successor in &instruction.successors {
                live.union(inputs[*successor]);
            }
            for write in instruction.writes.iter().rev() {
                budget.words()?;
                match write.register {
                    Some(register) if !write.has_load && !live.contains(register) => {}
                    Some(register) => {
                        live.remove(register);
                        live.union(write.reads);
                    }
                    None => live.union(write.reads),
                }
            }
            if inputs[index] != live {
                inputs[index] = live;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    let mut selections = Vec::with_capacity(model.len());
    for summary in &model {
        let mut live = summary.control_reads;
        for successor in &summary.successors {
            live.union(inputs[*successor]);
        }
        let mut keep = vec![true; summary.writes.len()];
        for (position, write) in summary.writes.iter().enumerate().rev() {
            budget.words()?;
            match write.register {
                Some(register) if !write.has_load && !live.contains(register) => {
                    keep[position] = false
                }
                Some(register) => {
                    live.remove(register);
                    live.union(write.reads);
                }
                None => live.union(write.reads),
            }
        }
        selections.push(keep);
    }
    // Clone only after input shape, state size, fixed point, and mask work pass.
    let mut instructions = source.instructions().to_vec();
    for (instruction, keep) in instructions.iter_mut().zip(selections) {
        let mut position = 0;
        instruction.assignments.retain(|_| {
            let retain = keep[position];
            position += 1;
            retain
        });
    }
    let entry = source.cfg().block(source.cfg().entry()).start;
    let candidate = Program::new(entry, source.register_count(), instructions).ok()?;
    validate(source, &candidate).then_some(candidate)
}

/// Independently check an actual candidate, never a proposer-supplied mask.
/// All metadata and control expressions must be unchanged. Assignments must be
/// an ordered subsequence, and every omitted assignment must be pure and dead.
/// Matching repeated equal assignments is conservative: a valid deletion can be
/// rejected if greedy subsequence matching chooses a different occurrence.
pub fn validate(source: &Program, candidate: &Program) -> bool {
    validate_bounded(source, candidate).is_some()
}

fn validate_bounded(source: &Program, candidate: &Program) -> Option<()> {
    let mut budget = Budget::default();
    // These scans establish bounds before recursive equality; their dependency
    // summaries and proposer transfer function are not used for the proof.
    preflight(source, &mut budget)?;
    budget.nodes = 0;
    preflight(candidate, &mut budget)?;
    if source.register_count() != candidate.register_count()
        || source.instructions().len() != candidate.instructions().len()
        || source.cfg().block(source.cfg().entry()).start
            != candidate.cfg().block(candidate.cfg().entry()).start
    {
        return None;
    }
    let mut retained = Vec::with_capacity(source.instructions().len());
    for (original, proposed) in source.instructions().iter().zip(candidate.instructions()) {
        if original.address != proposed.address
            || original.size != proposed.size
            || original.control != proposed.control
        {
            return None;
        }
        let mut next = 0;
        let mut flags = Vec::with_capacity(original.assignments.len());
        for assignment in &original.assignments {
            budget.work()?;
            let matches = proposed.assignments.get(next) == Some(assignment);
            flags.push(matches);
            if matches {
                next += 1;
            }
        }
        if next != proposed.assignments.len() {
            return None;
        }
        retained.push(flags);
    }
    // Proof uses a separate raw-AST traversal and transfer: kept assignments
    // always contribute their dependencies, even when a pure kept write is dead.
    let instructions = source.instructions();
    let mut inputs = vec![Registers::default(); instructions.len()];
    loop {
        let mut changed = false;
        for index in (0..instructions.len()).rev() {
            budget.visit()?;
            let live =
                proof_transfer(source, index, &retained[index], &inputs, false, &mut budget)?;
            if live != inputs[index] {
                inputs[index] = live;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    for (index, flags) in retained.iter().enumerate() {
        proof_transfer(source, index, flags, &inputs, true, &mut budget)?;
    }
    Some(())
}

fn proof_transfer(
    program: &Program,
    index: usize,
    retained: &[bool],
    inputs: &[Registers],
    check_dead: bool,
    budget: &mut Budget,
) -> Option<Registers> {
    let instructions = program.instructions();
    let instruction = &instructions[index];
    let mut live = Registers::default();
    let mut join = |address| {
        let successor = instructions
            .binary_search_by_key(&address, |item| item.address)
            .ok()?;
        live.union(inputs[successor]);
        Some(())
    };
    match &instruction.control {
        Control::Next => join(
            instruction
                .address
                .checked_add(u64::from(instruction.size))?,
        )?,
        Control::Jump(target) => join(*target)?,
        Control::Branch { condition, target } => {
            join(*target)?;
            join(
                instruction
                    .address
                    .checked_add(u64::from(instruction.size))?,
            )?;
            proof_reads(condition, &mut live, budget, false)?;
        }
        Control::Return(value) => proof_reads(value, &mut live, budget, false)?,
    }
    for (assignment, keep) in instruction.assignments.iter().zip(retained).rev() {
        budget.words()?;
        if !keep {
            let Place::Register(register) = assignment.destination else {
                return None;
            };
            if check_dead && live.contains(register.0) {
                return None;
            }
            // Reject any syntactic load, including loads in lazy dead arms.
            proof_reads(&assignment.value, &mut Registers::default(), budget, true)?;
            continue;
        }
        match &assignment.destination {
            Place::Register(register) => live.remove(register.0),
            Place::Memory { address, .. } => proof_reads(address, &mut live, budget, false)?,
        }
        proof_reads(&assignment.value, &mut live, budget, false)?;
    }
    Some(live)
}

/// Independent proof traversal. Bounds were checked before equality, and work
/// remains charged while traversing during fixed-point propagation.
fn proof_reads(
    expression: &Expr,
    live: &mut Registers,
    budget: &mut Budget,
    require_pure: bool,
) -> Option<()> {
    let mut pending = vec![expression];
    while let Some(expression) = pending.pop() {
        budget.work()?;
        match expression {
            Expr::Const(_) => {}
            Expr::Register(register) => live.insert(register.0),
            Expr::Binary(_, left, right) => {
                pending.push(left);
                pending.push(right);
            }
            Expr::Load { address, .. } => {
                if require_pure {
                    return None;
                }
                pending.push(address);
            }
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => {
                pending.push(condition);
                pending.push(taken);
                pending.push(not_taken);
            }
        }
    }
    Some(())
}

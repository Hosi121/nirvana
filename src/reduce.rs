//! Return-and-memory preserving reduction, separate from full machine-state IR.
//!
//! Each block gets fresh local value definitions. Original registers carry values
//! across edges; liveness determines the copies needed at block exits. Loads stay
//! at their original instruction because even an unused load can fault.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use crate::block_verify::{Validation, validate_program};
use crate::cfg::Target;
use crate::ir::{
    Control, ExecutionError, Expr, IrInstruction, Place, Program, ProgramError, Reg, RunReport,
};
use crate::simplify::{node_count, simplify};
use crate::verify::Solver;

type Live = BTreeSet<usize>;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ReductionStats {
    pub original_assignments: usize,
    pub reduced_assignments: usize,
    pub fresh_values: usize,
    pub passes: usize,
}

/// Observable state for this mode. Machine registers are deliberately excluded.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Observation {
    pub value: u64,
    pub memory: Vec<u8>,
    pub trace: Vec<u64>,
}

#[derive(Clone, Debug)]
pub struct ReducedFunction {
    program: Program,
    original_register_count: usize,
    parameters: Vec<Reg>,
    stats: ReductionStats,
}

#[derive(Clone, Debug)]
pub struct CheckedReduction {
    /// The candidate only if all block obligations passed; otherwise the exact
    /// original IR, with value parameters for its complete initial register file.
    pub function: ReducedFunction,
    pub validation: Validation,
}

pub fn reduce_checked(
    program: &Program,
    solver: &Solver,
) -> Result<CheckedReduction, ReductionError> {
    let candidate = reduce(program)?;
    let validation = validate_program(program, candidate.program(), solver);
    let function = if validation.accepted() {
        candidate
    } else {
        let assignments = program
            .instructions()
            .iter()
            .map(|instruction| instruction.assignments.len())
            .sum();
        ReducedFunction {
            program: program.clone(),
            original_register_count: program.register_count(),
            parameters: (0..program.register_count()).map(Reg).collect(),
            stats: ReductionStats {
                original_assignments: assignments,
                reduced_assignments: assignments,
                fresh_values: 0,
                passes: 0,
            },
        }
    };
    Ok(CheckedReduction {
        function,
        validation,
    })
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ReductionError {
    Program(ProgramError),
    RegisterOverflow,
    UndefinedValue(Reg),
}

impl fmt::Display for ReductionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Program(error) => error.fmt(f),
            Self::RegisterOverflow => f.write_str("too many local values"),
            Self::UndefinedValue(reg) => write!(f, "local value {} is undefined at entry", reg.0),
        }
    }
}
impl std::error::Error for ReductionError {}

impl ReducedFunction {
    pub fn program(&self) -> &Program {
        &self.program
    }
    /// Original input-register indices, in argument order.
    pub fn parameters(&self) -> &[Reg] {
        &self.parameters
    }
    pub fn stats(&self) -> ReductionStats {
        self.stats
    }
    pub fn execute_with_memory(
        &self,
        input: &[u64],
        base: u64,
        memory: &[u8],
        limit: usize,
    ) -> Result<Observation, ExecutionError> {
        let execution = self
            .run_with_memory(input, base, memory, limit)?
            .into_execution()?;
        Ok(Observation {
            value: execution.value,
            memory: execution.memory,
            trace: execution.trace,
        })
    }

    /// The report contains the reduced program's extended register file.
    /// Compare it with the return-and-memory observation contract.
    pub fn run_with_memory(
        &self,
        input: &[u64],
        base: u64,
        memory: &[u8],
        limit: usize,
    ) -> Result<RunReport, ExecutionError> {
        if input.len() != self.original_register_count {
            return Err(ExecutionError::RegisterCount {
                expected: self.original_register_count,
                actual: input.len(),
            });
        }
        let mut registers = vec![0; self.program.register_count()];
        registers[..input.len()].copy_from_slice(input);
        self.program
            .run_with_memory(&registers, base, memory, limit)
    }
}

fn reads(expression: &Expr, live: &mut Live) {
    match expression {
        Expr::Const(_) => {}
        Expr::Register(reg) => {
            live.insert(reg.0);
        }
        Expr::Binary(_, left, right) => {
            reads(left, live);
            reads(right, live);
        }
        Expr::Load { address, .. } => reads(address, live),
        Expr::Select {
            condition,
            taken,
            not_taken,
        } => {
            reads(condition, live);
            reads(taken, live);
            reads(not_taken, live);
        }
    }
}

fn control_reads(control: &Control, live: &mut Live) {
    match control {
        Control::Branch { condition, .. } => reads(condition, live),
        Control::Return(value) => reads(value, live),
        _ => {}
    }
}

fn transfer(instructions: &[IrInstruction], mut live: Live) -> Live {
    for instruction in instructions.iter().rev() {
        control_reads(&instruction.control, &mut live);
        for assignment in instruction.assignments.iter().rev() {
            match &assignment.destination {
                Place::Register(reg) => {
                    let needed = live.remove(&reg.0);
                    if needed || assignment.value.uses_memory() {
                        reads(&assignment.value, &mut live);
                    }
                }
                Place::Memory { address, .. } => {
                    reads(address, &mut live);
                    reads(&assignment.value, &mut live);
                }
            }
        }
    }
    live
}

fn liveness(program: &Program) -> (Vec<Live>, Vec<Live>) {
    let blocks = program.cfg().blocks();
    let mut incoming = vec![Live::new(); blocks.len()];
    let mut outgoing = incoming.clone();
    let reachable = program.cfg().reachable_blocks();
    loop {
        let mut changed = false;
        for &id in reachable.iter().rev() {
            let block = program.cfg().block(id);
            let mut live = Live::new();
            for edge in &block.successors {
                if let Target::Block(successor) = edge.target {
                    live.extend(&incoming[successor.index()]);
                }
            }
            let before = transfer(
                &program.instructions()[block.instructions.clone()],
                live.clone(),
            );
            changed |= before != incoming[id.index()] || live != outgoing[id.index()];
            incoming[id.index()] = before;
            outgoing[id.index()] = live;
        }
        if !changed {
            return (incoming, outgoing);
        }
    }
}

fn map_expr(expression: &Expr, lookup: &impl Fn(usize) -> Option<Expr>) -> Expr {
    match expression {
        Expr::Const(_) => expression.clone(),
        Expr::Register(reg) => lookup(reg.0).unwrap_or_else(|| expression.clone()),
        Expr::Binary(op, left, right) => {
            Expr::binary(*op, map_expr(left, lookup), map_expr(right, lookup))
        }
        Expr::Load { address, width } => Expr::load(map_expr(address, lookup), *width),
        Expr::Select {
            condition,
            taken,
            not_taken,
        } => Expr::select(
            map_expr(condition, lookup),
            map_expr(taken, lookup),
            map_expr(not_taken, lookup),
        ),
    }
}

fn map_control(control: &mut Control, lookup: &impl Fn(usize) -> Option<Expr>, fold: bool) {
    let value = match control {
        Control::Branch { condition, .. } => condition,
        Control::Return(value) => value,
        _ => return,
    };
    let mapped = map_expr(value, lookup);
    if !fold || node_count(&mapped) <= 128 {
        *value = mapped;
    }
    if fold {
        *value = simplify(value);
    }
}

fn local_values(program: &Program) -> Result<Program, ReductionError> {
    let (_, outgoing) = liveness(program);
    let mut instructions = program.instructions().to_vec();
    let mut count = program.register_count();
    for id in program.cfg().reachable_blocks() {
        let block = program.cfg().block(id);
        let mut versions = BTreeMap::new();
        for instruction in &mut instructions[block.instructions.clone()] {
            for assignment in &mut instruction.assignments {
                let lookup = |index| versions.get(&index).copied().map(Expr::Register);
                assignment.value = map_expr(&assignment.value, &lookup);
                match &mut assignment.destination {
                    Place::Memory { address, .. } => *address = map_expr(address, &lookup),
                    Place::Register(reg) => {
                        let original = reg.0;
                        *reg = Reg(count);
                        count = count
                            .checked_add(1)
                            .ok_or(ReductionError::RegisterOverflow)?;
                        versions.insert(original, *reg);
                    }
                }
            }
            map_control(
                &mut instruction.control,
                &|index| versions.get(&index).copied().map(Expr::Register),
                false,
            );
        }
        let last = &mut instructions[block.instructions.end - 1];
        for original in &outgoing[id.index()] {
            if let Some(version) = versions.get(original) {
                last.assignments.push(crate::ir::Assignment {
                    destination: Reg(*original).into(),
                    value: Expr::Register(*version),
                });
            }
        }
    }
    Program::new(
        program.cfg().block(program.cfg().entry()).start,
        count,
        instructions,
    )
    .map_err(ReductionError::Program)
}

fn eliminate(program: &Program, instructions: &mut [IrInstruction]) {
    let (_, outgoing) = liveness(program);
    for id in program.cfg().reachable_blocks() {
        let block = program.cfg().block(id);
        let mut live = outgoing[id.index()].clone();
        for instruction in instructions[block.instructions.clone()].iter_mut().rev() {
            control_reads(&instruction.control, &mut live);
            let mut kept = Vec::new();
            for assignment in instruction.assignments.iter().rev() {
                let keep = match &assignment.destination {
                    Place::Register(reg) => {
                        let needed = live.remove(&reg.0);
                        needed || assignment.value.uses_memory()
                    }
                    Place::Memory { address, .. } => {
                        reads(address, &mut live);
                        true
                    }
                };
                if keep {
                    reads(&assignment.value, &mut live);
                    kept.push(assignment.clone());
                }
            }
            kept.reverse();
            instruction.assignments = kept;
        }
    }
}

fn propagate(program: &Program, instructions: &mut [IrInstruction]) {
    for id in program.cfg().reachable_blocks() {
        let block = program.cfg().block(id);
        let mut uses = BTreeMap::<usize, usize>::new();
        let mut add_uses = |expression: &Expr| {
            let mut registers = Live::new();
            reads(expression, &mut registers);
            for index in registers {
                *uses.entry(index).or_default() += 1;
            }
        };
        for instruction in &instructions[block.instructions.clone()] {
            for assignment in &instruction.assignments {
                add_uses(&assignment.value);
                if let Place::Memory { address, .. } = &assignment.destination {
                    add_uses(address);
                }
            }
            match &instruction.control {
                Control::Branch { condition, .. } => add_uses(condition),
                Control::Return(value) => add_uses(value),
                _ => {}
            }
        }
        let mut values = BTreeMap::<usize, Expr>::new();
        for instruction in &mut instructions[block.instructions.clone()] {
            for assignment in &mut instruction.assignments {
                let lookup = |index| values.get(&index).cloned();
                let mapped = map_expr(&assignment.value, &lookup);
                assignment.value = simplify(&if node_count(&mapped) <= 128 {
                    mapped
                } else {
                    assignment.value.clone()
                });
                match &mut assignment.destination {
                    Place::Memory { address, .. } => {
                        let mapped = map_expr(address, &lookup);
                        *address = simplify(&if node_count(&mapped) <= 128 {
                            mapped
                        } else {
                            address.clone()
                        });
                    }
                    Place::Register(reg) => {
                        // A block-exit copy may overwrite an original input.
                        // Keep snapshots of that input materialized afterward.
                        values.retain(|index, value| {
                            let mut dependencies = Live::new();
                            reads(value, &mut dependencies);
                            *index != reg.0 && !dependencies.contains(&reg.0)
                        });
                        let mut dependencies = Live::new();
                        reads(&assignment.value, &mut dependencies);
                        let cheap = matches!(assignment.value, Expr::Const(_) | Expr::Register(_));
                        if !assignment.value.uses_memory()
                            && !dependencies.contains(&reg.0)
                            && (cheap || uses.get(&reg.0).copied().unwrap_or(0) <= 1)
                        {
                            values.insert(reg.0, assignment.value.clone());
                        }
                    }
                }
            }
            map_control(
                &mut instruction.control,
                &|index| values.get(&index).cloned(),
                true,
            );
        }
    }
}

pub fn reduce(program: &Program) -> Result<ReducedFunction, ReductionError> {
    let assignments = |program: &Program| {
        program
            .instructions()
            .iter()
            .map(|i| i.assignments.len())
            .sum()
    };
    let original_assignments = assignments(program);
    let mut current = local_values(program)?;
    let mut passes = 0;
    for _ in 0..8 {
        passes += 1;
        let mut instructions = current.instructions().to_vec();
        eliminate(&current, &mut instructions);
        propagate(&current, &mut instructions);
        if instructions == current.instructions() {
            break;
        }
        current = Program::new(
            current.cfg().block(current.cfg().entry()).start,
            current.register_count(),
            instructions,
        )
        .map_err(ReductionError::Program)?;
    }
    // Propagation on the final pass can leave unused value definitions.
    let mut instructions = current.instructions().to_vec();
    eliminate(&current, &mut instructions);
    current = Program::new(
        current.cfg().block(current.cfg().entry()).start,
        current.register_count(),
        instructions,
    )
    .map_err(ReductionError::Program)?;
    let (incoming, _) = liveness(&current);
    let parameters: Vec<_> = incoming[current.cfg().entry().index()]
        .iter()
        .copied()
        .map(Reg)
        .collect();
    if let Some(reg) = parameters
        .iter()
        .find(|reg| reg.0 >= program.register_count())
    {
        return Err(ReductionError::UndefinedValue(*reg));
    }
    let stats = ReductionStats {
        original_assignments,
        reduced_assignments: assignments(&current),
        fresh_values: current.register_count() - program.register_count(),
        passes,
    };
    Ok(ReducedFunction {
        program: current,
        original_register_count: program.register_count(),
        parameters,
        stats,
    })
}

//! Source-bound inductive checking of entry-stack-relative facts.
//!
//! The source instruction graph, virtual entry boundary, ordered assignments,
//! and access occurrences are checked without using the producer's CFG walk,
//! transfer evaluator, meet, or collector. Unknown is an admissible weakening;
//! a successful check certifies a sound invariant, not a least fixed point.

use super::{
    MAX_ACCESSES, MAX_EXPRESSION_DEPTH, MAX_EXPRESSION_WORK, MAX_POINTS, MAX_STATE_CELLS,
    StackAccess, StackAnalysis, Value,
};
use crate::model::ir::{
    AccessKind, BinaryOp, Control, Expr, IrInstruction, Place, Program, Reg, UnaryOp, Width,
};

const MAX_VALIDATION_WORK: usize = 8_000_000;

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct ValidationEvidence {
    pub instructions: usize,
    pub points: usize,
    pub known_values: usize,
    pub accesses: usize,
    /// Source instruction successor occurrences, excluding the virtual entry.
    pub edges: usize,
}

/// Facts checked against this particular immutable source and stack register.
#[derive(Debug)]
pub struct CheckedStack<'a> {
    _program: &'a Program,
    candidate: &'a StackAnalysis,
    evidence: ValidationEvidence,
}

impl CheckedStack<'_> {
    pub fn evidence(&self) -> ValidationEvidence {
        self.evidence
    }

    /// Evaluate a pure query with the checker's independent restricted algebra.
    /// Missing points and unknown addresses give None; exhaustion is an error.
    pub fn offset_before(
        &self,
        instruction: u64,
        assignment: usize,
        expression: &Expr,
    ) -> Result<Option<i64>, String> {
        query(self.candidate, instruction, assignment, expression)
    }

    pub fn accesses(&self) -> &[StackAccess] {
        &self.candidate.accesses
    }
}

/// Check all reachable point facts, source edges, and potential stack accesses.
/// No partial checked wrapper or evidence is returned on failure/exhaustion.
pub fn validate<'a>(
    program: &'a Program,
    stack_register: Reg,
    candidate: &'a StackAnalysis,
) -> Result<CheckedStack<'a>, String> {
    let registers = program.register_count();
    if stack_register.0 >= registers {
        return Err("stack validation stack register".into());
    }
    let instructions = program.instructions();
    let points = instructions.iter().try_fold(0usize, |n, i| {
        n.checked_add(i.assignments.len())?.checked_add(1)
    });
    let points = points.ok_or("stack validation source dimensions overflow")?;
    let cells = points
        .checked_add(program.cfg().blocks().len())
        .and_then(|n| n.checked_add(2))
        .and_then(|n| n.checked_mul(registers));
    if points > MAX_POINTS || cells.is_none_or(|n| n > MAX_STATE_CELLS) {
        return Err("stack validation source dimensions limit".into());
    }
    if candidate.points.len() > instructions.len() || candidate.accesses.len() > MAX_ACCESSES {
        return Err("stack validation candidate dimensions limit".into());
    }

    // Check dimensions before using candidate lengths as loops or dense indices.
    let mut work = Work(MAX_VALIDATION_WORK);
    let mut retained_cells = 0usize;
    for (&address, states) in &candidate.points {
        work.take(1)?;
        let instruction = &instructions[source_index(instructions, address)?];
        if states.len() != instruction.assignments.len() + 1 {
            return Err("stack validation point count".into());
        }
        work.take(states.len())?;
        for state in states {
            if state.len() != registers {
                return Err("stack validation state width".into());
            }
            retained_cells = retained_cells
                .checked_add(state.len())
                .ok_or("stack validation candidate cells overflow")?;
            if retained_cells > MAX_STATE_CELLS {
                return Err("stack validation candidate cells limit".into());
            }
        }
    }

    // The entry address is IR layout infrastructure. All successor/reachability
    // decisions below come from original Control expressions, not CFG edges.
    let entry = program.cfg().block(program.cfg().entry()).start;
    let entry_index = source_index(instructions, entry)?;
    let mut reachable = vec![false; instructions.len()];
    reachable[entry_index] = true;
    let mut pending = vec![entry_index];
    while let Some(index) = pending.pop() {
        work.take(1)?;
        for target in successors(&instructions[index])?.into_iter().flatten() {
            work.take(1)?;
            let next = source_index(instructions, target)?;
            if !reachable[next] {
                reachable[next] = true;
                pending.push(next);
            }
        }
    }
    for (index, instruction) in instructions.iter().enumerate() {
        work.take(1)?;
        if reachable[index] != candidate.points.contains_key(&instruction.address) {
            return Err("stack validation reachable point coverage".into());
        }
    }

    let boundary = &candidate.points[&entry][0];
    work.take(registers)?;
    for (index, &claimed) in boundary.iter().enumerate() {
        let expected = if index == stack_register.0 {
            Value::Stack(0)
        } else {
            Value::Unknown
        };
        require_implied(expected, claimed, "entry boundary")?;
    }

    let mut evidence = ValidationEvidence::default();
    let mut expressions = ExpressionWork(MAX_EXPRESSION_WORK);
    let mut accesses = AccessCheck {
        candidate: &candidate.accesses,
        matched: 0,
    };
    for (index, instruction) in instructions.iter().enumerate() {
        if !reachable[index] {
            continue;
        }
        let states = &candidate.points[&instruction.address];
        evidence.instructions += 1;
        evidence.points += states.len();
        for state in states {
            work.take(registers)?;
            evidence.known_values += state.iter().filter(|&&v| v != Value::Unknown).count();
        }
        for (assignment_index, assignment) in instruction.assignments.iter().enumerate() {
            let before = &states[assignment_index];
            let after = &states[assignment_index + 1];
            let written = match assignment.destination {
                Place::Register(reg) => Some((
                    reg,
                    term(&assignment.value, before, &mut expressions, 0)?.value(),
                )),
                Place::Memory { .. } => None,
            };
            work.take(registers)?;
            for (register, &claimed) in after.iter().enumerate() {
                let expected = match written {
                    Some((Reg(destination), value)) if destination == register => value,
                    _ => before[register],
                };
                require_implied(expected, claimed, "ordered assignment")?;
            }
            let site = (instruction.address, assignment_index);
            if let Place::Memory { address, width } = &assignment.destination {
                accesses.expression(address, before, site, &mut expressions)?;
                accesses.access(
                    address,
                    *width,
                    AccessKind::Write,
                    before,
                    site,
                    &mut expressions,
                )?;
            }
            accesses.expression(&assignment.value, before, site, &mut expressions)?;
        }
        let final_state = &states[instruction.assignments.len()];
        if let Control::Branch { condition, .. } | Control::Return(condition) = &instruction.control
        {
            accesses.expression(
                condition,
                final_state,
                (instruction.address, instruction.assignments.len()),
                &mut expressions,
            )?;
        }
        for target in successors(instruction)?.into_iter().flatten() {
            work.take(registers)?;
            let incoming = &candidate.points[&target][0];
            for (&expected, &claimed) in final_state.iter().zip(incoming) {
                require_implied(expected, claimed, "source successor")?;
            }
            evidence.edges += 1;
        }
    }
    if accesses.matched != candidate.accesses.len() {
        return Err("stack validation extra access occurrence".into());
    }
    evidence.accesses = accesses.matched;
    Ok(CheckedStack {
        _program: program,
        candidate,
        evidence,
    })
}

fn source_index(instructions: &[IrInstruction], address: u64) -> Result<usize, String> {
    instructions
        .binary_search_by_key(&address, |i| i.address)
        .map_err(|_| "stack validation missing source instruction".into())
}

fn successors(instruction: &IrInstruction) -> Result<[Option<u64>; 2], String> {
    let next = || {
        instruction
            .address
            .checked_add(u64::from(instruction.size))
            .ok_or_else(|| "stack validation next PC overflow".to_string())
    };
    Ok(match instruction.control {
        Control::Next => [Some(next()?), None],
        Control::Jump(target) => [Some(target), None],
        Control::Branch { target, .. } => [Some(next()?), Some(target)],
        Control::Return(_) => [None, None],
    })
}

fn require_implied(expected: Value, claimed: Value, obligation: &str) -> Result<(), String> {
    if claimed == Value::Unknown || claimed == expected {
        Ok(())
    } else {
        Err(format!("stack validation {obligation} fact"))
    }
}

struct Work(usize);

impl Work {
    fn take(&mut self, amount: usize) -> Result<(), String> {
        self.0 = self
            .0
            .checked_sub(amount)
            .ok_or("stack validation work limit")?;
        Ok(())
    }
}

struct ExpressionWork(usize);

impl ExpressionWork {
    fn take(&mut self, depth: usize) -> Result<(), String> {
        if depth > MAX_EXPRESSION_DEPTH {
            return Err("stack validation expression depth limit".into());
        }
        self.0 = self
            .0
            .checked_sub(1)
            .ok_or("stack validation expression work limit")?;
        Ok(())
    }
}

/// Restricted affine grammar: coefficient is always zero or one. Restricting
/// intermediate forms preserves the producer's precision, including accesses:
/// cancellation must not invent new facts for unsupported stack-stack terms.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Affine {
    coefficient: u64,
    bias: u64,
}

struct Term {
    affine: Option<Affine>,
    pure: bool,
}

impl Term {
    fn new(affine: Option<Affine>, pure: bool) -> Self {
        Self {
            affine: if pure { affine } else { None },
            pure,
        }
    }

    fn value(&self) -> Value {
        match self.affine {
            Some(Affine {
                coefficient: 0,
                bias,
            }) => Value::Constant(bias),
            Some(Affine {
                coefficient: 1,
                bias,
            }) => Value::Stack(bias),
            _ => Value::Unknown,
        }
    }
}

fn term(
    expression: &Expr,
    state: &[Value],
    work: &mut ExpressionWork,
    depth: usize,
) -> Result<Term, String> {
    work.take(depth)?;
    Ok(match expression {
        Expr::Const(bias) => Term::new(
            Some(Affine {
                coefficient: 0,
                bias: *bias,
            }),
            true,
        ),
        Expr::Register(reg) => {
            let affine = match state.get(reg.0) {
                Some(Value::Constant(bias)) => Some(Affine {
                    coefficient: 0,
                    bias: *bias,
                }),
                Some(Value::Stack(bias)) => Some(Affine {
                    coefficient: 1,
                    bias: *bias,
                }),
                _ => None,
            };
            Term::new(affine, true)
        }
        Expr::Load { .. } => Term::new(None, false),
        Expr::Unary(op, child) => {
            let child = term(child, state, work, depth + 1)?;
            let affine = match child.affine {
                Some(Affine {
                    coefficient: 0,
                    bias,
                }) => Some(Affine {
                    coefficient: 0,
                    bias: op.evaluate(bias),
                }),
                affine
                    if matches!(
                        op,
                        UnaryOp::SignExtend(Width::U64)
                            | UnaryOp::Extract {
                                start: 0,
                                width: Width::U64
                            }
                    ) =>
                {
                    affine
                }
                _ => None,
            };
            Term::new(affine, child.pure)
        }
        Expr::Binary(op, left, right) => {
            let left = term(left, state, work, depth + 1)?;
            let right = term(right, state, work, depth + 1)?;
            let affine = match (op, left.affine, right.affine) {
                (BinaryOp::Add, Some(a), Some(b)) if a.coefficient + b.coefficient <= 1 => {
                    Some(Affine {
                        coefficient: a.coefficient + b.coefficient,
                        bias: a.bias.wrapping_add(b.bias),
                    })
                }
                (BinaryOp::Sub, Some(a), Some(b)) if b.coefficient == 0 => Some(Affine {
                    coefficient: a.coefficient,
                    bias: a.bias.wrapping_sub(b.bias),
                }),
                _ => None,
            };
            Term::new(affine, left.pure && right.pure)
        }
        Expr::Select {
            condition,
            taken,
            not_taken,
        } => {
            let condition = term(condition, state, work, depth + 1)?;
            let taken = term(taken, state, work, depth + 1)?;
            let not_taken = term(not_taken, state, work, depth + 1)?;
            let affine = if taken.affine == not_taken.affine {
                taken.affine
            } else {
                None
            };
            Term::new(affine, condition.pure && taken.pure && not_taken.pure)
        }
    })
}

fn query(
    candidate: &StackAnalysis,
    instruction: u64,
    assignment: usize,
    expression: &Expr,
) -> Result<Option<i64>, String> {
    let Some(state) = candidate
        .points
        .get(&instruction)
        .and_then(|p| p.get(assignment))
    else {
        return Ok(None);
    };
    let result = term(
        expression,
        state,
        &mut ExpressionWork(MAX_EXPRESSION_WORK),
        0,
    )?;
    Ok(match result.affine {
        Some(Affine {
            coefficient: 1,
            bias,
        }) => Some(bias as i64),
        _ => None,
    })
}

/// Shared independent query kernel for the producer's public query facade.
pub(super) fn offset_before(
    candidate: &StackAnalysis,
    instruction: u64,
    assignment: usize,
    expression: &Expr,
) -> Option<i64> {
    query(candidate, instruction, assignment, expression)
        .ok()
        .flatten()
}

struct AccessCheck<'a> {
    candidate: &'a [StackAccess],
    matched: usize,
}

impl AccessCheck<'_> {
    fn access(
        &mut self,
        expression: &Expr,
        width: Width,
        kind: AccessKind,
        state: &[Value],
        site: (u64, usize),
        work: &mut ExpressionWork,
    ) -> Result<(), String> {
        if let Some(Affine {
            coefficient: 1,
            bias,
        }) = term(expression, state, work, 0)?.affine
        {
            let expected = StackAccess {
                instruction: site.0,
                assignment: site.1,
                offset: bias as i64,
                width,
                kind,
            };
            if self.matched >= MAX_ACCESSES || self.candidate.get(self.matched) != Some(&expected) {
                return Err("stack validation access occurrence".into());
            }
            self.matched += 1;
        }
        Ok(())
    }

    fn expression(
        &mut self,
        expression: &Expr,
        state: &[Value],
        site: (u64, usize),
        work: &mut ExpressionWork,
    ) -> Result<(), String> {
        enum Visit<'a> {
            Expression(&'a Expr, usize),
            Read(&'a Expr, Width),
        }
        let mut pending = vec![Visit::Expression(expression, 0)];
        while let Some(visit) = pending.pop() {
            match visit {
                Visit::Read(address, width) => {
                    self.access(address, width, AccessKind::Read, state, site, work)?
                }
                Visit::Expression(expression, depth) => {
                    work.take(depth)?;
                    match expression {
                        Expr::Const(_) | Expr::Register(_) => {}
                        Expr::Unary(_, child) => pending.push(Visit::Expression(child, depth + 1)),
                        Expr::Binary(_, left, right) => {
                            pending.push(Visit::Expression(right, depth + 1));
                            pending.push(Visit::Expression(left, depth + 1));
                        }
                        Expr::Load { address, width } => {
                            pending.push(Visit::Read(address, *width));
                            pending.push(Visit::Expression(address, depth + 1));
                        }
                        Expr::Select {
                            condition,
                            taken,
                            not_taken,
                        } => {
                            pending.push(Visit::Expression(not_taken, depth + 1));
                            pending.push(Visit::Expression(taken, depth + 1));
                            pending.push(Visit::Expression(condition, depth + 1));
                        }
                    }
                }
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests;

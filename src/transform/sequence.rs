//! Make expression memory reads explicit before rendering into a language whose
//! operand evaluation order may differ from the IR's left-to-right order.
//!
//! This is an expression plan, not an assignment plan. In particular, callers
//! must check a store destination before running the plan for its right-hand
//! side. Temporaries are private state and must not be observed as guest state.
use crate::model::ir::{Control, Place, Program};

use std::fmt;

use crate::model::ir::{Expr, Reg, Width};

/// Hard limits keep validation, recursive construction, and metadata cloning
/// bounded even for expressions supplied by an untrusted frontend.
pub const MAX_EXPRESSION_DEPTH: usize = 128;
pub const MAX_EXPRESSION_NODES: usize = 65_536;
pub const MAX_ADDRESS_METADATA_NODES: usize = 262_144;
pub const MAX_EVALUATIONS: usize = 65_536;

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Evaluation {
    Assign {
        destination: Reg,
        value: Expr,
    },
    Load {
        destination: Reg,
        address: Expr,
        /// The original address at the original instruction/assignment point.
        /// This may contain loads; it is analysis metadata, never executable.
        original_address: Expr,
        width: Width,
    },
    If {
        condition: Expr,
        taken: Vec<Evaluation>,
        not_taken: Vec<Evaluation>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SequencedExpr {
    pub steps: Vec<Evaluation>,
    pub value: Expr,
    /// The first unused register, suitable for sequencing another expression.
    pub next_register: usize,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SequenceError {
    RegisterCollision {
        register: Reg,
        first_temporary: usize,
    },
    RegisterOverflow,
    ExpressionTooDeep,
    ExpressionTooLarge,
    AddressMetadataTooLarge,
    TooManyEvaluations,
}

impl fmt::Display for SequenceError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::RegisterCollision {
                register,
                first_temporary,
            } => write!(
                f,
                "input r{} overlaps temporary range starting at r{first_temporary}",
                register.0
            ),
            Self::RegisterOverflow => f.write_str("temporary register index overflow"),
            Self::ExpressionTooDeep => {
                write!(f, "expression exceeds depth limit {MAX_EXPRESSION_DEPTH}")
            }
            Self::ExpressionTooLarge => {
                write!(f, "expression exceeds node limit {MAX_EXPRESSION_NODES}")
            }
            Self::AddressMetadataTooLarge => write!(
                f,
                "load address metadata exceeds node limit {MAX_ADDRESS_METADATA_NODES}"
            ),
            Self::TooManyEvaluations => {
                write!(f, "plan exceeds evaluation limit {MAX_EVALUATIONS}")
            }
        }
    }
}

impl std::error::Error for SequenceError {}

/// Preserve every memory read and its order, including reads in expressions
/// such as `0 * load(...)`. Only the selected arm of a select executes.
///
/// All input registers must be below `first_temporary`, including inputs in
/// unused select arms. No execution-facing expression in the result contains a
/// load: reads appear only as [`Evaluation::Load`]. Pure selects remain compact;
/// a select with branch steps assigns a shared, fresh result register.
pub fn sequence(expression: &Expr, first_temporary: usize) -> Result<SequencedExpr, SequenceError> {
    validate(expression, first_temporary)?;
    let mut builder = Builder {
        next_register: first_temporary,
        evaluations: 0,
    };
    let (steps, value) = builder.expression(expression)?;
    Ok(SequencedExpr {
        steps,
        value,
        next_register: builder.next_register,
    })
}

// Validate iteratively before calling recursive code or cloning any subtree.
// Each node contributes to the metadata of all enclosing load addresses. This
// bounds the total clones even when many nested loads share large addresses.
fn validate(expression: &Expr, first_temporary: usize) -> Result<(), SequenceError> {
    let mut pending = vec![(expression, 1, 0)];
    let mut nodes = 0usize;
    let mut metadata_nodes = 0usize;
    while let Some((expression, depth, load_ancestors)) = pending.pop() {
        if depth > MAX_EXPRESSION_DEPTH {
            return Err(SequenceError::ExpressionTooDeep);
        }
        nodes += 1;
        if nodes > MAX_EXPRESSION_NODES {
            return Err(SequenceError::ExpressionTooLarge);
        }
        // Both addends are already bounded by the limits above.
        metadata_nodes += load_ancestors;
        if metadata_nodes > MAX_ADDRESS_METADATA_NODES {
            return Err(SequenceError::AddressMetadataTooLarge);
        }
        match expression {
            Expr::Const(_) => {}
            Expr::Unary(_, value) => pending.push((value, depth + 1, load_ancestors)),
            Expr::Register(register) => {
                if register.0 >= first_temporary {
                    return Err(SequenceError::RegisterCollision {
                        register: *register,
                        first_temporary,
                    });
                }
            }
            Expr::Binary(_, left, right) => {
                pending.push((right, depth + 1, load_ancestors));
                pending.push((left, depth + 1, load_ancestors));
            }
            Expr::Load { address, .. } => {
                pending.push((address, depth + 1, load_ancestors + 1));
            }
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => {
                pending.push((not_taken, depth + 1, load_ancestors));
                pending.push((taken, depth + 1, load_ancestors));
                pending.push((condition, depth + 1, load_ancestors));
            }
        }
    }
    Ok(())
}

struct Builder {
    next_register: usize,
    evaluations: usize,
}

impl Builder {
    fn temporary(&mut self) -> Result<Reg, SequenceError> {
        let register = Reg(self.next_register);
        self.next_register = self
            .next_register
            .checked_add(1)
            .ok_or(SequenceError::RegisterOverflow)?;
        Ok(register)
    }

    fn step(&mut self, count: usize) -> Result<(), SequenceError> {
        self.evaluations += count;
        if self.evaluations > MAX_EVALUATIONS {
            return Err(SequenceError::TooManyEvaluations);
        }
        Ok(())
    }

    fn expression(&mut self, expression: &Expr) -> Result<(Vec<Evaluation>, Expr), SequenceError> {
        match expression {
            Expr::Const(_) | Expr::Register(_) => Ok((vec![], expression.clone())),
            Expr::Unary(op, value) => {
                let (steps, value) = self.expression(value)?;
                Ok((steps, Expr::unary(*op, value)))
            }
            Expr::Binary(operator, left, right) => {
                let (mut steps, left) = self.expression(left)?;
                let (right_steps, right) = self.expression(right)?;
                steps.extend(right_steps);
                Ok((steps, Expr::binary(*operator, left, right)))
            }
            Expr::Load { address, width } => {
                let (mut steps, pure_address) = self.expression(address)?;
                let destination = self.temporary()?;
                self.step(1)?;
                steps.push(Evaluation::Load {
                    destination,
                    address: pure_address,
                    original_address: (**address).clone(),
                    width: *width,
                });
                Ok((steps, Expr::Register(destination)))
            }
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => {
                let (mut steps, condition) = self.expression(condition)?;
                let (mut taken_steps, taken) = self.expression(taken)?;
                let (mut not_taken_steps, not_taken) = self.expression(not_taken)?;
                if taken_steps.is_empty() && not_taken_steps.is_empty() {
                    return Ok((steps, Expr::select(condition, taken, not_taken)));
                }
                let destination = self.temporary()?;
                self.step(3)?;
                taken_steps.push(Evaluation::Assign {
                    destination,
                    value: taken,
                });
                not_taken_steps.push(Evaluation::Assign {
                    destination,
                    value: not_taken,
                });
                steps.push(Evaluation::If {
                    condition,
                    taken: taken_steps,
                    not_taken: not_taken_steps,
                });
                Ok((steps, Expr::Register(destination)))
            }
        }
    }
}

// Bound the complete input before recursive helper detection, AST recovery, or
// rendering. Per-expression limits agree with the shared sequencing pass.
const MAX_PROGRAM_NODES: usize = 1_048_576;

pub(crate) fn validate_program(program: &Program) -> Result<(), SequenceError> {
    let mut remaining = MAX_PROGRAM_NODES;
    for instruction in program.instructions() {
        remaining = remaining
            .checked_sub(1 + instruction.assignments.len())
            .ok_or(SequenceError::ExpressionTooLarge)?;
    }
    let mut validate = |root: &Expr| -> Result<(), SequenceError> {
        let mut pending = vec![(root, 1usize, 0usize)];
        let mut nodes = 0usize;
        let mut metadata = 0usize;
        let mut loads = 0usize;
        while let Some((expr, depth, ancestors)) = pending.pop() {
            if depth > MAX_EXPRESSION_DEPTH {
                return Err(SequenceError::ExpressionTooDeep);
            }
            remaining = remaining
                .checked_sub(1)
                .ok_or(SequenceError::ExpressionTooLarge)?;
            nodes += 1;
            metadata += ancestors;
            if metadata > MAX_ADDRESS_METADATA_NODES {
                return Err(SequenceError::AddressMetadataTooLarge);
            }
            match expr {
                Expr::Const(_) | Expr::Register(_) => {}
                Expr::Unary(_, value) => pending.push((value, depth + 1, ancestors)),
                Expr::Binary(_, left, right) => {
                    pending.push((right, depth + 1, ancestors));
                    pending.push((left, depth + 1, ancestors));
                }
                Expr::Load { address, .. } => {
                    loads += 1;
                    pending.push((address, depth + 1, ancestors + 1));
                }
                Expr::Select {
                    condition,
                    taken,
                    not_taken,
                } => {
                    pending.push((not_taken, depth + 1, ancestors));
                    pending.push((taken, depth + 1, ancestors));
                    pending.push((condition, depth + 1, ancestors));
                }
            }
        }
        if loads > 1 && nodes > MAX_EXPRESSION_NODES {
            return Err(SequenceError::ExpressionTooLarge);
        }
        Ok(())
    };
    for instruction in program.instructions() {
        for assignment in &instruction.assignments {
            if let Place::Memory { address, .. } = &assignment.destination {
                validate(address)?;
            }
            validate(&assignment.value)?;
        }
        match &instruction.control {
            Control::Branch { condition, .. } => validate(condition)?,
            Control::Return(value) => validate(value)?,
            _ => {}
        }
    }
    Ok(())
}

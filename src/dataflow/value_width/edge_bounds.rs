//! Optional source-local unsigned branch bounds for width inference.
//!
//! Identities describe one execution of a block. Predicates capture operand
//! identities when computed; they never follow register names across writes
//! or carry a predicate through a block boundary.

use crate::control_flow::cfg::EdgeKind;
use crate::model::ir::{BinaryOp, Control, Expr, Place, Program};

use super::{Budget, MAX_DEPTH, MAX_POINTS, MAX_STATE_CELLS};

const MAX_REGISTERS: usize = 4096;
const MAX_PLAN_WORK: usize = 1_000_000;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Identity {
    Entry(usize),
    Constant(u64),
    Definition(usize),
}

#[derive(Clone, Copy, Debug)]
struct Predicate {
    left: Identity,
    right: Identity,
    inclusive: bool,
    inverted: bool,
}

#[derive(Clone, Copy)]
struct Value {
    identity: Identity,
    predicate: Option<Predicate>,
}

struct Operand {
    aliases: Vec<usize>,
    constant: Option<u64>,
}

impl Operand {
    fn capture(identity: Identity, values: &[Value], work: &mut Budget) -> Option<Self> {
        work.spend(values.len())?;
        Some(Self {
            aliases: values
                .iter()
                .enumerate()
                .filter_map(|(reg, value)| (value.identity == identity).then_some(reg))
                .collect(),
            constant: match identity {
                Identity::Constant(value) => Some(value),
                _ => None,
            },
        })
    }

    fn upper(&self, state: &[u8]) -> Option<u128> {
        self.aliases
            .iter()
            .map(|&reg| (1u128 << state[reg]) - 1)
            .chain(self.constant.map(u128::from))
            .min()
    }
}

struct Guard {
    left: Operand,
    right: Operand,
    inclusive: bool,
    inverted: bool,
}

pub(super) struct Plans(Vec<Option<Guard>>);

impl Plans {
    pub(super) fn build(program: &Program, points: usize) -> Option<Self> {
        let count = program.register_count();
        if count > MAX_REGISTERS
            || points > MAX_POINTS
            || program.cfg().blocks().len().checked_mul(count)? > MAX_STATE_CELLS
        {
            return None;
        }
        let mut work = Budget(MAX_PLAN_WORK);
        let mut guards = Vec::with_capacity(program.cfg().blocks().len());
        for block in program.cfg().blocks() {
            work.spend(1)?;
            let instructions = &program.instructions()[block.instructions.clone()];
            let Some(Control::Branch { condition, .. }) =
                instructions.last().map(|instruction| &instruction.control)
            else {
                guards.push(None);
                continue;
            };
            work.spend(count)?;
            let mut values: Vec<_> = (0..count)
                .map(|reg| Value {
                    identity: Identity::Entry(reg),
                    predicate: None,
                })
                .collect();
            let mut site = 0;
            for instruction in instructions {
                work.spend(1)?;
                for assignment in &instruction.assignments {
                    work.spend(1)?;
                    let Place::Register(reg) = assignment.destination else {
                        continue;
                    };
                    let value = match &assignment.value {
                        Expr::Register(source) => values[source.0],
                        Expr::Const(value) => Value {
                            identity: Identity::Constant(*value),
                            predicate: None,
                        },
                        expression => Value {
                            identity: Identity::Definition(site),
                            predicate: predicate(expression, &values, &mut work, 0)?,
                        },
                    };
                    values[reg.0] = value;
                    site += 1;
                }
            }
            let guard = if let Some(predicate) = predicate(condition, &values, &mut work, 0)? {
                Some(Guard {
                    left: Operand::capture(predicate.left, &values, &mut work)?,
                    right: Operand::capture(predicate.right, &values, &mut work)?,
                    inclusive: predicate.inclusive,
                    inverted: predicate.inverted,
                })
            } else {
                None
            };
            guards.push(guard);
        }
        Some(Self(guards))
    }

    /// Each edge starts with the same post-block state. In particular, two
    /// differently labeled edges to one target must both contribute a row.
    pub(super) fn refine(
        &self,
        block: usize,
        kind: EdgeKind,
        state: &[u8],
        budget: &mut Budget,
    ) -> Option<Option<Vec<u8>>> {
        let Some(guard) = self.0[block].as_ref() else {
            return Some(None);
        };
        let taken = match kind {
            EdgeKind::Taken => true,
            EdgeKind::NotTaken => false,
            _ => return Some(None),
        };
        budget.spend(1 + guard.left.aliases.len() + guard.right.aliases.len())?;
        let truth = taken != guard.inverted;
        let (constrained, cap, strict) = if truth {
            (&guard.left, guard.right.upper(state), !guard.inclusive)
        } else {
            (&guard.right, guard.left.upper(state), guard.inclusive)
        };
        let Some(cap) = cap else {
            return Some(None);
        };
        let cap = if strict {
            let Some(cap) = cap.checked_sub(1) else {
                // No underflow, and no attempt to infer unreachable edges.
                return Some(None);
            };
            cap
        } else {
            cap
        };
        if constrained.aliases.is_empty() {
            return Some(None);
        }
        budget.spend(state.len())?;
        let bits = (128 - cap.leading_zeros()) as u8;
        let mut result = state.to_vec();
        for &reg in &constrained.aliases {
            result[reg] = result[reg].min(bits);
        }
        Some(Some(result))
    }
}

fn identity(expression: &Expr, values: &[Value]) -> Option<Identity> {
    match expression {
        Expr::Register(reg) => Some(values[reg.0].identity),
        Expr::Const(value) => Some(Identity::Constant(*value)),
        _ => None,
    }
}

/// Only a captured relational boolean permits boolean normalizations. An
/// arbitrary word XOR 1 does not encode boolean negation in this IR.
fn predicate(
    expression: &Expr,
    values: &[Value],
    work: &mut Budget,
    depth: usize,
) -> Option<Option<Predicate>> {
    work.spend(1)?;
    if depth > MAX_DEPTH {
        return Some(None);
    }
    let predicate = match expression {
        Expr::Register(reg) => values[reg.0].predicate,
        Expr::Binary(op @ (BinaryOp::Ult | BinaryOp::Ule), left, right) => {
            match (identity(left, values), identity(right, values)) {
                (Some(left), Some(right)) => Some(Predicate {
                    left,
                    right,
                    inclusive: *op == BinaryOp::Ule,
                    inverted: false,
                }),
                _ => None,
            }
        }
        Expr::Binary(op @ (BinaryOp::Eq | BinaryOp::Ne | BinaryOp::Xor), left, right) => {
            let (value, constant) = match (left.as_ref(), right.as_ref()) {
                (value, Expr::Const(constant)) | (Expr::Const(constant), value) => {
                    (value, *constant)
                }
                _ => return Some(None),
            };
            let inverted = match (*op, constant) {
                (BinaryOp::Eq, 0) | (BinaryOp::Ne, 1) | (BinaryOp::Xor, 1) => true,
                (BinaryOp::Eq, 1) | (BinaryOp::Ne, 0) => false,
                _ => return Some(None),
            };
            predicate(value, values, work, depth + 1)?.map(|mut predicate| {
                predicate.inverted ^= inverted;
                predicate
            })
        }
        _ => None,
    };
    Some(predicate)
}

#[cfg(test)]
mod tests;

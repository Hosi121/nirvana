//! Source-local conditional bounds reconstructed by the checker.  Definitions
//! are found backwards from each use; no producer identities or plans enter
//! this module, and an entry register belongs only to this block execution.

use super::{ValidationError, Work};
use crate::control_flow::cfg::EdgeKind;
use crate::dataflow::unsigned_caps;
use crate::model::ir::{BinaryOp, Control, Expr, IrInstruction, Place, Reg};

const MAX_GUARD_REGISTERS: usize = 4096;
const MAX_GUARD_WORK: usize = 1_000_000;

/// Optional structural work has a separate bound. Exhaustion discards the
/// incomplete guard, leaving the existing unconditional numeric check intact.
pub(super) struct Budget {
    remaining: usize,
}

impl Budget {
    pub(super) fn new(registers: usize) -> Self {
        Self {
            remaining: if registers <= MAX_GUARD_REGISTERS {
                MAX_GUARD_WORK
            } else {
                0
            },
        }
    }

    fn take(&mut self, amount: usize) -> Result<(), ()> {
        self.remaining = self.remaining.checked_sub(amount).ok_or(())?;
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Value {
    Entry(usize),
    Definition(usize),
    Literal(u64),
}

struct History<'a> {
    /// Register writes in actual source order. A definition's operands see
    /// only definitions with a strictly smaller index, including self-copies.
    values: Vec<&'a Expr>,
    writers: Vec<Vec<usize>>,
}

impl<'a> History<'a> {
    fn new(
        instructions: &'a [IrInstruction],
        registers: usize,
        budget: &mut Budget,
    ) -> Result<Self, ()> {
        budget.take(registers)?;
        let mut result = Self {
            values: Vec::new(),
            writers: vec![Vec::new(); registers],
        };
        for instruction in instructions {
            budget.take(1)?;
            for assignment in &instruction.assignments {
                budget.take(1)?;
                if let Place::Register(reg) = assignment.destination {
                    let index = result.values.len();
                    result.values.push(&assignment.value);
                    result.writers[reg.0].push(index);
                }
            }
        }
        Ok(result)
    }

    fn preceding(
        &self,
        register: Reg,
        before: usize,
        budget: &mut Budget,
    ) -> Result<Option<usize>, ()> {
        let writers = &self.writers[register.0];
        let (mut low, mut high) = (0, writers.len());
        while low < high {
            budget.take(1)?;
            let middle = low + (high - low) / 2;
            if writers[middle] < before {
                low = middle + 1;
            } else {
                high = middle;
            }
        }
        Ok(low.checked_sub(1).map(|index| writers[index]))
    }

    /// Resolve only register/constant operands. Pure copies and constants
    /// preserve equality; every other write is its own immutable reference.
    /// The loop also bounds arbitrarily long copy chains without recursion.
    fn value<'b>(
        &'b self,
        mut expression: &'b Expr,
        mut before: usize,
        resolved: &mut [Option<Value>],
        budget: &mut Budget,
    ) -> Result<Option<Value>, ()> {
        let mut path = Vec::new();
        let result = loop {
            budget.take(1)?;
            match expression {
                Expr::Const(value) => break Some(Value::Literal(*value)),
                Expr::Register(reg) => match self.preceding(*reg, before, budget)? {
                    None => break Some(Value::Entry(reg.0)),
                    Some(index) => {
                        if let Some(value) = resolved[index] {
                            break Some(value);
                        }
                        path.push(index);
                        match self.values[index] {
                            value @ (Expr::Register(_) | Expr::Const(_)) => {
                                expression = value;
                                before = index;
                            }
                            _ => break Some(Value::Definition(index)),
                        }
                    }
                },
                _ => break None,
            }
        };
        if let Some(value) = result {
            // A writer site's reference is immutable, even when later writes
            // change its register. Cache only references discovered backwards
            // on demand, never current aliases or candidate numeric bounds.
            for index in path {
                budget.take(1)?;
                resolved[index] = Some(value);
            }
        }
        Ok(result)
    }

    fn predicate<'b>(
        &'b self,
        mut expression: &'b Expr,
        resolved: &mut [Option<Value>],
        budget: &mut Budget,
    ) -> Result<Option<Predicate>, ()> {
        let mut before = self.values.len();
        let mut positive = true;
        loop {
            budget.take(1)?;
            match expression {
                Expr::Register(reg) => {
                    let Some(index) = self.preceding(*reg, before, budget)? else {
                        return Ok(None);
                    };
                    expression = self.values[index];
                    before = index;
                }
                Expr::Binary(operation @ (BinaryOp::Ult | BinaryOp::Ule), left, right) => {
                    let Some(left) = self.value(left, before, resolved, budget)? else {
                        return Ok(None);
                    };
                    let Some(right) = self.value(right, before, resolved, budget)? else {
                        return Ok(None);
                    };
                    return Ok(Some(Predicate {
                        strict: *operation == BinaryOp::Ult,
                        positive,
                        left,
                        right,
                    }));
                }
                Expr::Binary(operation @ (BinaryOp::Xor | BinaryOp::Eq | BinaryOp::Ne), a, b) => {
                    let left = self.value(a, before, resolved, budget)?;
                    let right = self.value(b, before, resolved, budget)?;
                    let (next, literal) = match (left, right) {
                        (_, Some(Value::Literal(value @ 0..=1))) => (&**a, value),
                        (Some(Value::Literal(value @ 0..=1)), _) => (&**b, value),
                        _ => return Ok(None),
                    };
                    let invert = match (operation, literal) {
                        (BinaryOp::Xor, 1) | (BinaryOp::Eq, 0) | (BinaryOp::Ne, 1) => true,
                        (BinaryOp::Eq, 1) | (BinaryOp::Ne, 0) => false,
                        _ => return Ok(None),
                    };
                    positive ^= invert;
                    expression = next;
                    // This is only a boolean normalization if the entire
                    // chain eventually reaches an actual relational result.
                }
                _ => return Ok(None),
            }
        }
    }
}

struct Predicate {
    strict: bool,
    positive: bool,
    left: Value,
    right: Value,
}

pub(super) struct Guard {
    strict: bool,
    positive: bool,
    left: Vec<usize>,
    right: Vec<usize>,
    left_literal: Option<u128>,
    right_literal: Option<u128>,
}

pub(super) fn derive(
    instructions: &[IrInstruction],
    registers: usize,
    budget: &mut Budget,
) -> Option<Guard> {
    derive_bounded(instructions, registers, budget)
        .ok()
        .flatten()
}

fn derive_bounded(
    instructions: &[IrInstruction],
    registers: usize,
    budget: &mut Budget,
) -> Result<Option<Guard>, ()> {
    budget.take(1)?;
    let Some(IrInstruction {
        control: Control::Branch { condition, .. },
        ..
    }) = instructions.last()
    else {
        return Ok(None);
    };
    let history = History::new(instructions, registers, budget)?;
    budget.take(history.values.len())?;
    let mut resolved = vec![None; history.values.len()];
    let Some(predicate) = history.predicate(condition, &mut resolved, budget)? else {
        return Ok(None);
    };
    let literal = |value| match value {
        Value::Literal(value) => Some(u128::from(value)),
        _ => None,
    };
    let mut result = Guard {
        strict: predicate.strict,
        positive: predicate.positive,
        left: Vec::new(),
        right: Vec::new(),
        left_literal: literal(predicate.left),
        right_literal: literal(predicate.right),
    };
    for register in 0..registers {
        budget.take(1)?;
        let reference = history
            .value(
                &Expr::Register(Reg(register)),
                history.values.len(),
                &mut resolved,
                budget,
            )?
            .unwrap();
        if reference == predicate.left {
            result.left.push(register);
        }
        if reference == predicate.right {
            result.right.push(register);
        }
    }
    Ok(Some(result))
}

/// Check every register on this successor occurrence, including when the two
/// branch occurrences have the same target. Caller charges the linear row
/// comparison; numeric guard applications charge their additional alias scan.
pub(super) fn covers(
    guard: Option<&Guard>,
    kind: EdgeKind,
    post: &[u128],
    next: &[u8],
    work: &mut Work,
) -> Result<bool, ValidationError> {
    let mut aliases: &[usize] = &[];
    let mut cap = unsigned_caps::WORD_MAX;
    if let Some(guard) = guard {
        let truth = match kind {
            EdgeKind::Taken => Some(guard.positive),
            EdgeKind::NotTaken => Some(!guard.positive),
            _ => None,
        };
        if let Some(truth) = truth {
            let (constrained, bounding, literal, subtract) = if truth {
                (&guard.left, &guard.right, guard.right_literal, guard.strict)
            } else {
                (&guard.right, &guard.left, guard.left_literal, !guard.strict)
            };
            work.take(bounding.len() + 1)?;
            let upper = bounding
                .iter()
                .map(|&register| post[register])
                .chain(literal)
                .min();
            if let Some(upper) = upper.and_then(|value| value.checked_sub(u128::from(subtract))) {
                cap = upper;
                aliases = constrained;
            }
        }
    }
    let mut aliases = aliases.iter().copied().peekable();
    for (register, (&value, &bits)) in post.iter().zip(next).enumerate() {
        let value = if aliases.peek() == Some(&register) {
            aliases.next();
            value.min(cap)
        } else {
            value
        };
        if value > unsigned_caps::from_bits(bits).unwrap() {
            return Ok(false);
        }
    }
    Ok(true)
}

#[cfg(test)]
mod tests;

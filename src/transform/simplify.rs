//! Local u64 expression rewrites with checked-memory evaluation preserved.
//!
//! Every rule is non-expanding. Rules that remove repeated operands or change
//! their order require load-free operands; Select keeps its lazy evaluation.

use crate::model::ir::{BinaryOp as B, Expr};

pub fn node_count(expression: &Expr) -> usize {
    match expression {
        Expr::Const(_) | Expr::Register(_) => 1,
        Expr::Load { address, .. } => 1usize.saturating_add(node_count(address)),
        Expr::Binary(_, left, right) => 1usize
            .saturating_add(node_count(left))
            .saturating_add(node_count(right)),
        Expr::Select {
            condition,
            taken,
            not_taken,
        } => 1usize
            .saturating_add(node_count(condition))
            .saturating_add(node_count(taken))
            .saturating_add(node_count(not_taken)),
    }
}

/// Preserve modulo-2^64 arithmetic, masked shifts, and the order/count of loads
/// that can execute. In particular, zero multiplication does not erase a load.
pub fn simplify(expression: &Expr) -> Expr {
    let mut result = match expression {
        Expr::Const(_) | Expr::Register(_) => expression.clone(),
        Expr::Load { address, width } => Expr::load(simplify(address), *width),
        Expr::Binary(op, left, right) => Expr::binary(*op, simplify(left), simplify(right)),
        Expr::Select {
            condition,
            taken,
            not_taken,
        } => {
            let condition = simplify(condition);
            if let Expr::Const(value) = condition {
                return simplify(if value != 0 { taken } else { not_taken });
            }
            Expr::select(condition, simplify(taken), simplify(not_taken))
        }
    };
    // Most rewrites strictly reduce the tree. Shift normalization is same-size
    // and one-way; the fixed cap also bounds work if more rules are added.
    for _ in 0..16 {
        let Some(next) = rewrite(&result) else { break };
        if next == result || node_count(&next) > node_count(&result) {
            break;
        }
        result = next;
    }
    result
}

fn pure(expression: &Expr) -> bool {
    match expression {
        Expr::Const(_) | Expr::Register(_) => true,
        Expr::Load { .. } => false,
        Expr::Binary(_, left, right) => pure(left) && pure(right),
        Expr::Select {
            condition,
            taken,
            not_taken,
        } => pure(condition) && pure(taken) && pure(not_taken),
    }
}

fn boolean(expression: &Expr) -> bool {
    match expression {
        Expr::Const(value) => *value <= 1,
        Expr::Binary(B::Eq | B::Ne | B::Ult | B::Ule, ..) => true,
        Expr::Binary(B::And, left, right)
            if matches!(**left, Expr::Const(1)) || matches!(**right, Expr::Const(1)) =>
        {
            true
        }
        Expr::Binary(B::And | B::Or | B::Xor, left, right) => boolean(left) && boolean(right),
        Expr::Binary(B::Shr, _, right) if matches!(**right, Expr::Const(value) if value & 63 == 63) => {
            true
        }
        Expr::Select {
            taken, not_taken, ..
        } => boolean(taken) && boolean(not_taken),
        _ => false,
    }
}

fn constant(expression: &Expr) -> Option<u64> {
    if let Expr::Const(value) = expression {
        Some(*value)
    } else {
        None
    }
}

fn binary(op: B, left: &Expr, right: &Expr) -> Expr {
    Expr::binary(op, left.clone(), right.clone())
}

fn fold(op: B, left: u64, right: u64) -> u64 {
    op.evaluate(left, right)
}

fn invert(expression: &Expr) -> Option<Expr> {
    match expression {
        Expr::Const(value) if *value <= 1 => Some(Expr::Const(1 - value)),
        Expr::Binary(B::Eq, left, right) => Some(binary(B::Ne, left, right)),
        Expr::Binary(B::Ne, left, right) => Some(binary(B::Eq, left, right)),
        Expr::Binary(B::Ult, left, right) if pure(expression) => Some(binary(B::Ule, right, left)),
        Expr::Binary(B::Ule, left, right) if pure(expression) => Some(binary(B::Ult, right, left)),
        _ => None,
    }
}

fn rewrite(expression: &Expr) -> Option<Expr> {
    match expression {
        Expr::Binary(op, left, right) => rewrite_binary(*op, left, right),
        Expr::Select {
            condition,
            taken,
            not_taken,
        } => {
            if taken == not_taken && pure(condition) {
                return Some((**taken).clone());
            }
            if constant(taken) == Some(1) && constant(not_taken) == Some(0) {
                return Some(if boolean(condition) {
                    (**condition).clone()
                } else {
                    binary(B::Ne, condition, &Expr::Const(0))
                });
            }
            if constant(taken) == Some(0) && constant(not_taken) == Some(1) {
                return Some(
                    invert(condition).unwrap_or_else(|| binary(B::Eq, condition, &Expr::Const(0))),
                );
            }
            if let Expr::Binary(op @ (B::Eq | B::Ne), left, right) = &**condition {
                let value = if constant(right) == Some(0) {
                    Some(&**left)
                } else if constant(left) == Some(0) {
                    Some(&**right)
                } else {
                    None
                };
                if let Some(value) = value {
                    return Some(if *op == B::Eq {
                        Expr::select(value.clone(), (**not_taken).clone(), (**taken).clone())
                    } else {
                        Expr::select(value.clone(), (**taken).clone(), (**not_taken).clone())
                    });
                }
            }
            None
        }
        _ => None,
    }
}

fn rewrite_binary(op: B, left: &Expr, right: &Expr) -> Option<Expr> {
    let a = constant(left);
    let b = constant(right);
    if let (Some(a), Some(b)) = (a, b) {
        return Some(Expr::Const(fold(op, a, b)));
    }
    if left == right && pure(left) {
        match op {
            B::Sub | B::Xor | B::Ne | B::Ult => return Some(Expr::Const(0)),
            B::Eq | B::Ule => return Some(Expr::Const(1)),
            B::And | B::Or => return Some(left.clone()),
            _ => {}
        }
    }
    match op {
        B::Add | B::Or | B::Xor if a == Some(0) => return Some(right.clone()),
        B::Add | B::Sub | B::Or | B::Xor if b == Some(0) => return Some(left.clone()),
        B::Mul if a == Some(1) => return Some(right.clone()),
        B::Mul if b == Some(1) => return Some(left.clone()),
        B::And if a == Some(u64::MAX) => return Some(right.clone()),
        B::And if b == Some(u64::MAX) => return Some(left.clone()),
        B::And if a == Some(1) && boolean(right) => return Some(right.clone()),
        B::And if b == Some(1) && boolean(left) => return Some(left.clone()),
        B::Mul | B::And | B::UMulHigh if a == Some(0) && pure(right) => {
            return Some(Expr::Const(0));
        }
        B::Mul | B::And | B::UMulHigh if b == Some(0) && pure(left) => return Some(Expr::Const(0)),
        B::Or if a == Some(u64::MAX) && pure(right) => return Some(Expr::Const(u64::MAX)),
        B::Or if b == Some(u64::MAX) && pure(left) => return Some(Expr::Const(u64::MAX)),
        B::Shl | B::Shr => {
            if let Some(value) = b {
                if value & 63 == 0 {
                    return Some(left.clone());
                }
                if value >= 64 {
                    return Some(binary(op, left, &Expr::Const(value & 63)));
                }
            }
            if a == Some(0) && pure(right) {
                return Some(Expr::Const(0));
            }
            if let Expr::Binary(B::And, count, mask) = right
                && constant(mask).is_some_and(|mask| mask & 63 == 63)
            {
                return Some(binary(op, left, count));
            }
        }
        B::Ult if b == Some(0) && pure(left) => return Some(Expr::Const(0)),
        B::Ult if a == Some(u64::MAX) && pure(right) => return Some(Expr::Const(0)),
        B::Ule if a == Some(0) && pure(right) => return Some(Expr::Const(1)),
        B::Ule if b == Some(u64::MAX) && pure(left) => return Some(Expr::Const(1)),
        B::Eq | B::Ne => {
            // Modulo subtraction is zero exactly when its operands are equal;
            // both operands are still evaluated once, in their original order.
            let difference = if b == Some(0) {
                Some(left)
            } else if a == Some(0) {
                Some(right)
            } else {
                None
            };
            if let Some(Expr::Binary(B::Sub, first, second)) = difference {
                return Some(binary(op, first, second));
            }
            for (value, number) in [(left, b), (right, a)] {
                if boolean(value) {
                    match (op, number) {
                        (B::Eq, Some(1)) | (B::Ne, Some(0)) => return Some(value.clone()),
                        (B::Eq, Some(0)) | (B::Ne, Some(1)) => {
                            if let Some(inverse) = invert(value) {
                                return Some(inverse);
                            }
                        }
                        (_, Some(number)) if number > 1 && pure(value) => {
                            return Some(Expr::Const(u64::from(op == B::Ne)));
                        }
                        _ => {}
                    }
                }
            }
        }
        B::Xor => {
            if a == Some(1) && boolean(right) {
                return invert(right);
            }
            if b == Some(1) && boolean(left) {
                return invert(left);
            }
        }
        _ => {}
    }
    if op == B::Or {
        for (less, equal) in [(left, right), (right, left)] {
            if let (Expr::Binary(B::Ult, first, second), Expr::Binary(B::Eq, a, b)) = (less, equal)
                && ((first == a && second == b) || (first == b && second == a))
                && pure(first)
                && pure(second)
            {
                return Some(binary(B::Ule, first, second));
            }
        }
    }
    // Combine neighboring constants without moving any potentially faulting
    // evaluation. The operand subtree remains once and in the same position.
    if let (Expr::Binary(inner, value, first), Some(second)) = (left, b)
        && let Some(first) = constant(first)
    {
        if *inner == op && matches!(op, B::Add | B::Mul | B::And | B::Or | B::Xor) {
            return Some(binary(op, value, &Expr::Const(fold(op, first, second))));
        }
        if matches!(
            (inner, op),
            (B::Sub, B::Sub) | (B::Add, B::Sub) | (B::Sub, B::Add)
        ) {
            let (new_op, constant) = match (inner, op) {
                (B::Sub, B::Sub) => (B::Sub, first.wrapping_add(second)),
                (B::Add, B::Sub) => (B::Add, first.wrapping_sub(second)),
                _ => (B::Add, second.wrapping_sub(first)),
            };
            return Some(binary(new_op, value, &Expr::Const(constant)));
        }
    }
    if op == B::Add {
        let (a, ca) = scaled(left);
        let (b, cb) = scaled(right);
        if a == b && pure(a) {
            let coefficient = ca.wrapping_add(cb);
            return Some(if coefficient == 0 {
                Expr::Const(0)
            } else if coefficient == 1 {
                a.clone()
            } else {
                binary(B::Mul, a, &Expr::Const(coefficient))
            });
        }
    }
    None
}

fn scaled(expression: &Expr) -> (&Expr, u64) {
    if let Expr::Binary(B::Mul, left, right) = expression {
        if let Some(number) = constant(right) {
            return (left, number);
        }
        if let Some(number) = constant(left) {
            return (right, number);
        }
    }
    (expression, 1)
}

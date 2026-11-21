//! Extract one leading storage read for associative compound assignment.
//!
//! This is syntax extraction only. The consumer must preserve unsigned-u64
//! arithmetic (including promotions for narrow C storage) and the implicit
//! destination read. It must establish that `same` really denotes shared
//! current storage; equality of virtual register numbers is not assumed here.

use crate::model::ir::{BinaryOp, Expr, Reg};

const MAX_DEPTH: usize = 128;
const MAX_NODES: usize = 16_384;

/// For an identical Add/Mul/And/Or/Xor left spine beginning at the destination
/// storage, remove exactly that first Register read and return the operator
/// and remaining expression. The sole prefix exception is an innermost
/// `Const op Register(self)` pair: these two pure leaves may commute, leaving
/// the constant as the first RHS operand. No other operand is simplified,
/// reordered, duplicated, or removed; lazy/faulting subtrees remain intact.
/// The returned RHS has two fewer nodes than `value`. On limits or any other
/// shape, return `None` without mutating the supplied expression.
pub fn extract(
    value: &Expr,
    destination: Reg,
    same: impl Fn(Reg, Reg) -> bool,
) -> Option<(BinaryOp, Expr)> {
    validate(value)?;
    let Expr::Binary(op, _, _) = value else {
        return None;
    };
    if !matches!(
        op,
        BinaryOp::Add | BinaryOp::Mul | BinaryOp::And | BinaryOp::Or | BinaryOp::Xor
    ) {
        return None;
    }
    let mut left = value;
    let mut operands = Vec::new();
    while let Expr::Binary(next, a, b) = left {
        if next != op {
            return None;
        }
        if matches!(&**a, Expr::Const(_)) && matches!(&**b, Expr::Register(_)) {
            operands.push(&**a);
            left = b;
            break;
        }
        operands.push(&**b);
        left = a;
    }
    let Expr::Register(source) = left else {
        return None;
    };
    if !same(*source, destination) {
        return None;
    }
    let mut remainder = operands.pop()?.clone();
    while let Some(operand) = operands.pop() {
        remainder = Expr::binary(*op, remainder, operand.clone());
    }
    Some((*op, remainder))
}

// Validate before cloning anything or invoking the slot callback. The original
// AST may come from an untrusted frontend and be much deeper than our walker.
fn validate(value: &Expr) -> Option<()> {
    let mut pending = vec![(value, 1)];
    let mut remaining = MAX_NODES;
    while let Some((expr, depth)) = pending.pop() {
        if depth > MAX_DEPTH {
            return None;
        }
        remaining = remaining.checked_sub(1)?;
        match expr {
            Expr::Const(_) | Expr::Register(_) => {}
            Expr::Unary(_, value) => pending.push((value, depth + 1)),
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
        }
    }
    Some(())
}

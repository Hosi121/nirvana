//! Certified constant division of an explicitly masked, pure u64 value.
//!
//! The complete And operand remains borrowed in the view. Its literal mask is
//! an interval bound; C types, inferred widths, and earlier definitions supply
//! no facts. A checked product bound proves that the IR's low multiply is the
//! full unsigned product before the quotient/error certificate is applied.

use super::reciprocal_bounds::Reciprocal;
use crate::model::ir::{BinaryOp, Expr};

pub const MAX_NODES: usize = 4096;
pub const MAX_DEPTH: usize = 128;
pub const MAX_WORK: usize = 32_768;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct NarrowDivisionEvidence {
    /// The literal mask in the borrowed And expression; 0 <= value <= maximum.
    pub maximum: u64,
    pub multiplier: u64,
    /// The original literal, never a shift count reduced modulo 64.
    pub shift: u32,
    /// multiplier * divisor - 2^shift, in [0, divisor).
    pub excess: u64,
    /// maximum * multiplier, required to fit u64.
    pub product_bound: u128,
    /// floor(maximum/divisor)*excess + multiplier*(divisor-1), below 2^shift.
    pub error_bound: u128,
}

#[derive(Clone, Copy, Debug)]
pub struct NarrowDivisionView<'a> {
    /// The entire original And expression, retaining its mask and dependencies.
    pub value: &'a Expr,
    pub divisor: u64,
    pub evidence: NarrowDivisionEvidence,
}

/// Recognize `(And(tree, constant_mask) * constant) >> literal`, allowing both
/// product/mask operand orders. Load anywhere, invalid certificates, and whole
/// expression budget exhaustion decline. No executable expression is modified.
pub fn recognize(expression: &Expr) -> Option<NarrowDivisionView<'_>> {
    bounded_pure(expression)?;
    let Expr::Binary(BinaryOp::Shr, product, count) = expression else {
        return None;
    };
    let Expr::Const(shift) = **count else {
        return None;
    };
    if shift > 63 {
        return None;
    }
    let Expr::Binary(BinaryOp::Mul, left, right) = &**product else {
        return None;
    };
    let power = 1_u128.checked_shl(shift as u32)?;
    for (value, factor) in [(&**left, &**right), (&**right, &**left)] {
        let Expr::Const(multiplier) = *factor else {
            continue;
        };
        if multiplier == 0 {
            continue;
        }
        let Some(maximum) = explicit_maximum(value) else {
            continue;
        };
        let m = u128::from(multiplier);
        let product_bound = u128::from(maximum).checked_mul(m)?;
        if product_bound > u128::from(u64::MAX) {
            continue;
        }
        let Some(reciprocal) = Reciprocal::infer(m, power) else {
            continue;
        };
        let error_bound = reciprocal.conservative_bound(maximum)?;
        let view = NarrowDivisionView {
            value,
            divisor: reciprocal.divisor,
            evidence: NarrowDivisionEvidence {
                maximum,
                multiplier,
                shift: shift as u32,
                excess: reciprocal.excess,
                product_bound,
                error_bound,
            },
        };
        if validate(expression, &view) {
            return Some(view);
        }
    }
    None
}

/// Reparse independently, bind every field to the raw source, and recompute the
/// bounds with checked u128 arithmetic. Pointer identity binds the whole And;
/// neither its unmasked child nor an equal-looking clone is sufficient.
///
/// For X in [0, maximum], the product bound makes lowMul(M,X) equal M*X.
/// Write X=q*D+r and M*D=P+E. Then M*X=q*P+q*E+M*r; nonnegative E and
/// q*E+M*r <= floor(maximum/D)*E+M*(D-1) < P prove floor(M*X/P)=floor(X/D).
pub fn validate(expression: &Expr, view: &NarrowDivisionView<'_>) -> bool {
    if bounded_pure(expression).is_none() {
        return false;
    }
    let evidence = view.evidence;
    if evidence.shift > 63 || evidence.multiplier == 0 || view.divisor < 2 {
        return false;
    }
    let Expr::Binary(BinaryOp::Shr, product, count) = expression else {
        return false;
    };
    if !matches!(&**count, Expr::Const(s) if *s <= 63 && *s == u64::from(evidence.shift)) {
        return false;
    }
    let Expr::Binary(BinaryOp::Mul, left, right) = &**product else {
        return false;
    };
    let bound_operand = match (&**left, &**right) {
        (value, Expr::Const(m)) if std::ptr::eq(value, view.value) && *m == evidence.multiplier => {
            value
        }
        (Expr::Const(m), value) if std::ptr::eq(value, view.value) && *m == evidence.multiplier => {
            value
        }
        _ => return false,
    };
    // Independent structural parsing rather than trusting the matcher's mask.
    let Expr::Binary(BinaryOp::And, a, b) = bound_operand else {
        return false;
    };
    let maximum = match (&**a, &**b) {
        (_, Expr::Const(mask)) => *mask,
        (Expr::Const(mask), _) => *mask,
        _ => return false,
    };
    if maximum != evidence.maximum {
        return false;
    }
    let m = u128::from(evidence.multiplier);
    let Some(product_bound) = u128::from(maximum).checked_mul(m) else {
        return false;
    };
    if product_bound > u128::from(u64::MAX) || product_bound != evidence.product_bound {
        return false;
    }
    let Some(power) = 1_u128.checked_shl(evidence.shift) else {
        return false;
    };
    let Some(reciprocal) = Reciprocal::check(m, power, view.divisor) else {
        return false;
    };
    let Some(error) = reciprocal.conservative_bound(maximum) else {
        return false;
    };
    reciprocal.excess == evidence.excess && error == evidence.error_bound && error < power
}

fn explicit_maximum(value: &Expr) -> Option<u64> {
    let Expr::Binary(BinaryOp::And, a, b) = value else {
        return None;
    };
    match (&**a, &**b) {
        (_, Expr::Const(mask)) | (Expr::Const(mask), _) => Some(*mask),
        _ => None,
    }
}

fn bounded_pure(expression: &Expr) -> Option<()> {
    let mut pending = vec![(expression, 1usize)];
    let mut nodes = 0usize;
    let mut work = MAX_WORK;
    while let Some((expression, depth)) = pending.pop() {
        work = work.checked_sub(1)?;
        nodes += 1;
        if nodes > MAX_NODES || depth > MAX_DEPTH {
            return None;
        }
        match expression {
            Expr::Const(_) | Expr::Register(_) => {}
            Expr::Load { .. } => return None,
            Expr::Unary(_, value) => pending.push((value, depth + 1)),
            Expr::Binary(_, a, b) => pending.extend([(&**a, depth + 1), (&**b, depth + 1)]),
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => pending.extend([
                (&**condition, depth + 1),
                (&**taken, depth + 1),
                (&**not_taken, depth + 1),
            ]),
        }
    }
    Some(())
}

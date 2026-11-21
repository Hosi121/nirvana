//! Certified, borrowed display views for unsigned constant division.
//!
//! This recognizes only raw, syntactically load-free UMulHigh trees. A view
//! changes neither executable IR nor register dependencies. The sufficient
//! arithmetic certificate covers every u64 value, without source-type or
//! producer assumptions; failing to prove it simply declines the view.

use crate::model::ir::{BinaryOp, Expr};

pub const MAX_NODES: usize = 4096;
pub const MAX_DEPTH: usize = 128;
pub const MAX_WORK: usize = 32_768;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct DivisionEvidence {
    pub multiplier: u64,
    /// The literal right-shift count, in 0..=63. Zero also describes a root
    /// UMulHigh with no explicit shift.
    pub shift: u32,
    /// multiplier * divisor - 2^(64 + shift).
    pub excess: u64,
    /// floor(u64::MAX / divisor) * excess + multiplier * (divisor - 1).
    /// This must be strictly below 2^(64 + shift).
    pub upper_bound: u128,
}

#[derive(Clone, Copy, Debug)]
pub struct DivisionView<'a> {
    /// Borrowed unchanged, including all pure arithmetic, selects, and masks.
    pub value: &'a Expr,
    pub divisor: u64,
    pub evidence: DivisionEvidence,
}

/// Recognize UMulHigh(value, constant) >> literal, with either product operand
/// order and an optional shift. Literal counts outside 0..=63 decline even
/// though the IR masks shift counts. Every syntactic Load, including lazy dead
/// arms, declines before matching or arithmetic. No IR allocation or clone is
/// needed; successful candidates are gated by the independent validator.
pub fn recognize(expression: &Expr) -> Option<DivisionView<'_>> {
    bounded_pure(expression)?;
    let (product, shift) = match expression {
        Expr::Binary(BinaryOp::Shr, product, count) => {
            let Expr::Const(count) = **count else {
                return None;
            };
            if count > 63 {
                return None;
            }
            (&**product, count as u32)
        }
        _ => (expression, 0),
    };
    let Expr::Binary(BinaryOp::UMulHigh, left, right) = product else {
        return None;
    };
    let power = 1_u128.checked_shl(64 + shift)?;
    for (value, factor) in [(&**left, &**right), (&**right, &**left)] {
        let Expr::Const(multiplier) = *factor else {
            continue;
        };
        if multiplier == 0 {
            continue;
        }
        let m = u128::from(multiplier);
        // Quotient/remainder form avoids an unchecked ceil-division sum.
        let divisor = (power / m).checked_add(u128::from(power % m != 0))?;
        let Ok(divisor) = u64::try_from(divisor) else {
            continue;
        };
        if divisor < 2 {
            continue;
        }
        let excess = m.checked_mul(u128::from(divisor))?.checked_sub(power)?;
        if excess >= u128::from(divisor) {
            continue;
        }
        let upper_bound = u128::from(u64::MAX / divisor)
            .checked_mul(excess)?
            .checked_add(m.checked_mul(u128::from(divisor - 1))?)?;
        let candidate = DivisionView {
            value,
            divisor,
            evidence: DivisionEvidence {
                multiplier,
                shift,
                excess: u64::try_from(excess).ok()?,
                upper_bound,
            },
        };
        if validate(expression, &candidate) {
            return Some(candidate);
        }
    }
    None
}

/// Independently validate a view against its original raw tree and recompute
/// every certificate field with checked u128 arithmetic. Borrowed value identity
/// must name the actual product operand; equal-looking clones are insufficient.
///
/// Proof: write x=q*d+r, 0<=r<d. With m*d=P+e, m*x=q*P+q*e+m*r.
/// Nonnegative e prevents underestimation. The strict upper bound on the final
/// two terms prevents overestimation for q<=floor(MAX/d), proving floor(m*x/P)
/// equals floor(x/d). UMulHigh followed by shift S equals floor(m*x/2^(64+S)).
pub fn validate(expression: &Expr, view: &DivisionView<'_>) -> bool {
    if bounded_pure(expression).is_none() {
        return false;
    }
    let evidence = view.evidence;
    if evidence.shift > 63 || evidence.multiplier == 0 || view.divisor < 2 {
        return false;
    }
    // Parse independently of the matcher and bind the evidence to this tree.
    let product = match expression {
        Expr::Binary(BinaryOp::Shr, value, count) => match &**count {
            Expr::Const(count) if *count <= 63 && *count == u64::from(evidence.shift) => &**value,
            _ => return false,
        },
        value if evidence.shift == 0 => value,
        _ => return false,
    };
    let Expr::Binary(BinaryOp::UMulHigh, left, right) = product else {
        return false;
    };
    let matched = match (&**left, &**right) {
        (value, Expr::Const(m)) if std::ptr::eq(value, view.value) && *m == evidence.multiplier => {
            true
        }
        (Expr::Const(m), value) if std::ptr::eq(value, view.value) && *m == evidence.multiplier => {
            true
        }
        _ => false,
    };
    if !matched {
        return false;
    }
    let Some(power) = 1_u128.checked_shl(64 + evidence.shift) else {
        return false;
    };
    let m = u128::from(evidence.multiplier);
    let d = u128::from(view.divisor);
    let Some(ceil_numerator) = power.checked_add(m - 1) else {
        return false;
    };
    if ceil_numerator / m != d {
        return false;
    }
    let Some(product) = m.checked_mul(d) else {
        return false;
    };
    let Some(excess) = product.checked_sub(power) else {
        return false;
    };
    if excess >= d || excess != u128::from(evidence.excess) {
        return false;
    }
    let Some(quotient_error) = (u128::from(u64::MAX) / d).checked_mul(excess) else {
        return false;
    };
    let Some(remainder_error) = m.checked_mul(d - 1) else {
        return false;
    };
    let Some(upper) = quotient_error.checked_add(remainder_error) else {
        return false;
    };
    upper == evidence.upper_bound && upper < power
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
    }
    Some(())
}

//! Source-bound views of signed reciprocal division on arbitrary 64-bit bits.
//!
//! Signedness belongs to the operations, not to an inferred C type. A pure
//! quotient kernel must implement truncation toward zero for every int64 value.
//! The negative domain includes INT64_MIN and permits an error exactly P.
use super::reciprocal_bounds::{Reciprocal, SignedReciprocal};
use crate::model::ir::{BinaryOp as B, Expr};

use super::pure_expression::Work;
pub use super::pure_expression::{MAX_DEPTH, MAX_NODES, MAX_WORK};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SignedDivisionEvidence {
    pub multiplier: u64,
    pub shift: u32,
    pub excess: u64,
    pub positive_bound: u128,
    pub negative_bound: u128,
}

#[derive(Clone, Copy, Debug)]
pub struct SignedDivisionView<'a> {
    pub value: &'a Expr,
    pub divisor: i64,
    pub evidence: SignedDivisionEvidence,
}

#[derive(Clone, Copy, Debug)]
pub struct SignedRemainderView<'a> {
    pub value: &'a Expr,
    pub divisor: i64,
    pub evidence: SignedDivisionEvidence,
}

struct Kernel<'a> {
    value: &'a Expr,
    multiplier: u64,
    shift: u32,
    negate: bool,
}

/// Recognize AShr(SMulHigh(X,M) + optional X,S) - AShr(X,63),
/// or the reversed subtraction for a negative divisor. Adding X is required
/// precisely when M's signed bit is set. S=0 can omit the outer shift.
pub fn recognize(expression: &Expr) -> Option<SignedDivisionView<'_>> {
    if !matches!(expression, Expr::Binary(B::Sub, ..)) {
        return None;
    }
    let mut work = Work::new();
    work.pure(expression)?;
    for kernel in kernels(expression, &mut work)? {
        let power = 1u128.checked_shl(64 + kernel.shift)?;
        let Some(r) = Reciprocal::infer(u128::from(kernel.multiplier), power) else {
            continue;
        };
        let Ok(divisor) = i64::try_from(r.divisor) else {
            continue;
        };
        let divisor = if kernel.negate { -divisor } else { divisor };
        let Some(evidence) = certificate(kernel.multiplier, kernel.shift, divisor) else {
            continue;
        };
        let view = SignedDivisionView {
            value: kernel.value,
            divisor,
            evidence,
        };
        if validate(expression, &view) {
            return Some(view);
        }
    }
    None
}

/// Reparse the actual source and bind the borrowed numerator and all evidence.
/// Checked integer arithmetic is shared with unsigned division; neither source
/// type guesses nor a compiler-specific magic-number table supplies a premise.
pub fn validate(expression: &Expr, view: &SignedDivisionView<'_>) -> bool {
    let mut work = Work::new();
    if work.pure(expression).is_none() {
        return false;
    }
    let Some(expected) = certificate(view.evidence.multiplier, view.evidence.shift, view.divisor)
    else {
        return false;
    };
    if expected != view.evidence {
        return false;
    }
    let Some(kernels) = kernels(expression, &mut work) else {
        return false;
    };
    kernels.into_iter().any(|kernel| {
        std::ptr::eq(kernel.value, view.value)
            && kernel.multiplier == expected.multiplier
            && kernel.shift == expected.shift
            && kernel.negate == (view.divisor < 0)
    })
}

/// For X=q*D+r, M*X=q*P+q*E+M*r. On the positive domain [0,MAX],
/// error<P proves floor(M*X/P)=q. For a negative input -X, X in [1,2^63],
/// 0<error<=P proves floor(-M*X/P)+1=-q. E>0 gives the strict lower bound
/// even at exact multiples. This is why the two endpoint bounds differ.
fn certificate(multiplier: u64, shift: u32, divisor: i64) -> Option<SignedDivisionEvidence> {
    let r = SignedReciprocal::check(multiplier, 64, shift, divisor.unsigned_abs())?;
    Some(SignedDivisionEvidence {
        multiplier,
        shift,
        excess: r.excess,
        positive_bound: r.positive_bound,
        negative_bound: r.negative_bound,
    })
}

pub(crate) fn infer_evidence(multiplier: u64, shift: u32) -> Option<(i64, SignedDivisionEvidence)> {
    let r = SignedReciprocal::infer(multiplier, 64, shift)?;
    let divisor = i64::try_from(r.divisor).ok()?;
    Some((divisor, certificate(multiplier, shift, divisor)?))
}

pub fn recognize_remainder(expression: &Expr) -> Option<SignedRemainderView<'_>> {
    if !matches!(expression, Expr::Binary(B::Sub, ..)) {
        return None;
    }
    let mut work = Work::new();
    work.pure(expression)?;
    let (value, product) = binary(expression, B::Sub)?;
    let (a, b) = binary(product, B::Mul)?;
    for (quotient, factor) in [(a, b), (b, a)] {
        let Some(q) = recognize(quotient) else {
            continue;
        };
        if !matches!(factor, Expr::Const(d) if *d == q.divisor as u64)
            || !work.same(value, q.value)?
        {
            continue;
        }
        let view = SignedRemainderView {
            value,
            divisor: q.divisor,
            evidence: q.evidence,
        };
        if validate_remainder(expression, &view) {
            return Some(view);
        }
    }
    None
}

pub fn validate_remainder(expression: &Expr, view: &SignedRemainderView<'_>) -> bool {
    fn check(expression: &Expr, view: &SignedRemainderView<'_>) -> Option<bool> {
        let mut work = Work::new();
        work.pure(expression)?;
        let (value, product) = binary(expression, B::Sub)?;
        if !std::ptr::eq(value, view.value) {
            return Some(false);
        }
        let (a, b) = binary(product, B::Mul)?;
        for (quotient, factor) in [(a, b), (b, a)] {
            if !matches!(factor,Expr::Const(d) if *d==view.divisor as u64) {
                continue;
            }
            let Some(q) = recognize(quotient) else {
                continue;
            };
            if q.divisor == view.divisor
                && q.evidence == view.evidence
                && work.same(value, q.value)?
            {
                return Some(true);
            }
        }
        Some(false)
    }
    check(expression, view) == Some(true)
}

fn kernels<'a>(expression: &'a Expr, work: &mut Work) -> Option<Vec<Kernel<'a>>> {
    let Some((a, b)) = binary(expression, B::Sub) else {
        return Some(Vec::new());
    };
    let mut result = Vec::new();
    for (estimate, sign, negate) in [(a, b, false), (b, a, true)] {
        let Some((signed_value, count)) = binary(sign, B::AShr) else {
            continue;
        };
        if !matches!(count, Expr::Const(63)) {
            continue;
        }
        let (product, shift) = match binary(estimate, B::AShr) {
            Some((product, Expr::Const(shift @ 0..=63))) => (product, *shift as u32),
            Some(_) => continue,
            None => (estimate, 0),
        };
        let terms = match binary(product, B::Add) {
            Some((x, y)) => vec![(x, Some(y)), (y, Some(x))],
            None => vec![(product, None)],
        };
        for (high, add) in terms {
            let Some((left, right)) = binary(high, B::SMulHigh) else {
                continue;
            };
            for (value, factor) in [(left, right), (right, left)] {
                let Expr::Const(multiplier) = factor else {
                    continue;
                };
                if (*multiplier >> 63 != 0) != add.is_some() || !work.same(value, signed_value)? {
                    continue;
                }
                if let Some(add) = add
                    && !work.same(value, add)?
                {
                    continue;
                }
                result.push(Kernel {
                    value,
                    multiplier: *multiplier,
                    shift,
                    negate,
                });
            }
        }
    }
    Some(result)
}

fn binary(expression: &Expr, expected: B) -> Option<(&Expr, &Expr)> {
    if let Expr::Binary(op, a, b) = expression
        && *op == expected
    {
        Some((a, b))
    } else {
        None
    }
}

// Compatibility exports; the C backend owns portable integer definitions.
pub use crate::codegen::emit::integer::{
    SIGNED_DIVIDE_HELPER as DIVIDE_HELPER, SIGNED_REMAINDER_HELPER as REMAINDER_HELPER,
};

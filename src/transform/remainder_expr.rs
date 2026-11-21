//! Borrowed, certified unsigned-remainder presentation of raw pure trees.
//!
//! No register/dataflow or C-storage equality is assumed. Both occurrences of
//! the dividend must be structurally identical, and an existing independent
//! division certificate must cover the raw quotient expression.
use crate::model::ir::{BinaryOp, Expr};
use crate::{transform::division_expr, transform::narrow_division_expr};

pub const MAX_NODES: usize = 4096;
pub const MAX_DEPTH: usize = 128;
pub const MAX_WORK: usize = 65_536;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum QuotientEvidence {
    High(division_expr::DivisionEvidence),
    Narrow(narrow_division_expr::NarrowDivisionEvidence),
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct RemainderEvidence {
    pub quotient: QuotientEvidence,
    /// Dividend interval bound; this is not a possible-one bitmask.
    pub maximum: u64,
    pub product_mask: Option<u64>,
    pub result_mask: Option<u64>,
}
#[derive(Clone, Copy, Debug)]
pub struct RemainderView<'a> {
    /// Actual subtraction lhs, retaining its complete original pure syntax.
    pub value: &'a Expr,
    pub divisor: u64,
    /// Numeric interval bound, not a bitmask: e.g. bound9 permits bits0..3.
    pub maximum_remainder: u64,
    pub evidence: RemainderEvidence,
}

/// Match X - (certified_quotient(X,d) * d), optionally with one literal And
/// around the product and/or result. Mul/And operands may be commuted. Masks
/// must contain the entire low-bit hull of the corresponding interval bound.
/// Separate quotient registers, all syntactic loads, and exhausted bounds
/// decline without changing any IR, AST, memory operation, or dependency.
pub fn recognize(expression: &Expr) -> Option<RemainderView<'_>> {
    let mut work = Work(MAX_WORK);
    work.pure(expression)?;
    let (difference, result_mask) = clipped(expression);
    let Expr::Binary(BinaryOp::Sub, value, product) = difference else {
        return None;
    };
    let (product, product_mask) = clipped(product);
    let Expr::Binary(BinaryOp::Mul, a, b) = product else {
        return None;
    };
    for (quotient, factor) in [(&**a, &**b), (&**b, &**a)] {
        let Expr::Const(divisor) = *factor else {
            continue;
        };
        if divisor < 2 {
            continue;
        }
        let candidate = if let Some(q) = division_expr::recognize(quotient) {
            if q.divisor != divisor || !work.same(value, q.value)? {
                continue;
            }
            (u64::MAX, QuotientEvidence::High(q.evidence))
        } else if let Some(q) = narrow_division_expr::recognize(quotient) {
            if q.divisor != divisor || !work.same(value, q.value)? {
                continue;
            }
            (q.evidence.maximum, QuotientEvidence::Narrow(q.evidence))
        } else {
            continue;
        };
        let maximum = candidate.0;
        let maximum_remainder = maximum.min(divisor - 1);
        if product_mask.is_some_and(|mask| mask & low_mask(maximum) != low_mask(maximum))
            || result_mask.is_some_and(|mask| {
                mask & low_mask(maximum_remainder) != low_mask(maximum_remainder)
            })
        {
            continue;
        }
        let view = RemainderView {
            value,
            divisor,
            maximum_remainder,
            evidence: RemainderEvidence {
                quotient: candidate.1,
                maximum,
                product_mask,
                result_mask,
            },
        };
        if validate(expression, &view) {
            return Some(view);
        }
    }
    None
}

/// Independently bind the raw subtraction, masks, quotient certificate, factor,
/// structural dividend equality, and interval bounds. Upstream validators
/// recheck the entire division proof rather than trusting a matched quotient.
///
/// If q=floor(X/d), then 0<=q*d<=X<=maximum, so the IR low product and
/// subtraction cannot wrap. Their result is X%d <= min(maximum,d-1). An And
/// wrapper is an identity only if its literal covers every bit of the complete
/// low-bit hull of the relevant bound, including holes in a noncontiguous bound.
pub fn validate(expression: &Expr, view: &RemainderView<'_>) -> bool {
    validate_inner(expression, view).is_some()
}
fn validate_inner(expression: &Expr, view: &RemainderView<'_>) -> Option<()> {
    let mut work = Work(MAX_WORK);
    work.pure(expression)?;
    if view.divisor < 2 {
        return None;
    }
    let (difference, result_mask) = match expression {
        Expr::Binary(BinaryOp::And, a, b) => match (&**a, &**b) {
            (body, Expr::Const(mask)) | (Expr::Const(mask), body) => (body, Some(*mask)),
            _ => (expression, None),
        },
        _ => (expression, None),
    };
    let Expr::Binary(BinaryOp::Sub, value, raw_product) = difference else {
        return None;
    };
    if !std::ptr::eq(&**value, view.value) {
        return None;
    }
    let (product, product_mask) = match &**raw_product {
        Expr::Binary(BinaryOp::And, a, b) => match (&**a, &**b) {
            (body, Expr::Const(mask)) | (Expr::Const(mask), body) => (body, Some(*mask)),
            _ => (&**raw_product, None),
        },
        body => (body, None),
    };
    if result_mask != view.evidence.result_mask || product_mask != view.evidence.product_mask {
        return None;
    }
    let Expr::Binary(BinaryOp::Mul, left, right) = product else {
        return None;
    };
    for (quotient, factor) in [(&**left, &**right), (&**right, &**left)] {
        if !matches!(factor,Expr::Const(d) if *d==view.divisor) {
            continue;
        }
        let (raw_multiply, multiplier, maximum) = match view.evidence.quotient {
            QuotientEvidence::High(evidence) => {
                let multiply = match quotient {
                    Expr::Binary(BinaryOp::Shr, body, _) => &**body,
                    body => body,
                };
                (multiply, evidence.multiplier, u64::MAX)
            }
            QuotientEvidence::Narrow(evidence) => {
                let Expr::Binary(BinaryOp::Shr, body, _) = quotient else {
                    continue;
                };
                (&**body, evidence.multiplier, evidence.maximum)
            }
        };
        let (a, b) = match (view.evidence.quotient, raw_multiply) {
            (QuotientEvidence::High(_), Expr::Binary(BinaryOp::UMulHigh, a, b))
            | (QuotientEvidence::Narrow(_), Expr::Binary(BinaryOp::Mul, a, b)) => (&**a, &**b),
            _ => continue,
        };
        for (quotient_value, magic) in [(a, b), (b, a)] {
            if !matches!(magic,Expr::Const(m) if *m==multiplier) {
                continue;
            }
            let certified = match view.evidence.quotient {
                QuotientEvidence::High(evidence) => division_expr::validate(
                    quotient,
                    &division_expr::DivisionView {
                        value: quotient_value,
                        divisor: view.divisor,
                        evidence,
                    },
                ),
                QuotientEvidence::Narrow(evidence) => narrow_division_expr::validate(
                    quotient,
                    &narrow_division_expr::NarrowDivisionView {
                        value: quotient_value,
                        divisor: view.divisor,
                        evidence,
                    },
                ),
            };
            if !certified || !work.same(value, quotient_value)? {
                continue;
            }
            if maximum != view.evidence.maximum
                || maximum.min(view.divisor - 1) != view.maximum_remainder
            {
                return None;
            }
            // Deliberately recompute the hull independently of the matcher.
            let hull = |mut bound: u64| {
                let mut mask = 0_u64;
                while bound != 0 {
                    mask = (mask << 1) | 1;
                    bound >>= 1;
                }
                mask
            };
            if product_mask.is_some_and(|mask| mask & hull(maximum) != hull(maximum))
                || result_mask.is_some_and(|mask| {
                    mask & hull(view.maximum_remainder) != hull(view.maximum_remainder)
                })
            {
                return None;
            }
            return Some(());
        }
    }
    None
}

fn clipped(expression: &Expr) -> (&Expr, Option<u64>) {
    match expression {
        Expr::Binary(BinaryOp::And, a, b) => match (&**a, &**b) {
            (body, Expr::Const(mask)) | (Expr::Const(mask), body) => (body, Some(*mask)),
            _ => (expression, None),
        },
        _ => (expression, None),
    }
}
fn low_mask(bound: u64) -> u64 {
    if bound == 0 {
        0
    } else {
        u64::MAX >> bound.leading_zeros()
    }
}
struct Work(usize);
impl Work {
    fn spend(&mut self) -> Option<()> {
        self.0 = self.0.checked_sub(1)?;
        Some(())
    }
    fn pure(&mut self, root: &Expr) -> Option<()> {
        let mut pending = vec![(root, 1)];
        let mut nodes = 0;
        while let Some((e, depth)) = pending.pop() {
            self.spend()?;
            nodes += 1;
            if nodes > MAX_NODES || depth > MAX_DEPTH {
                return None;
            }
            match e {
                Expr::Const(_) | Expr::Register(_) => {}
                Expr::Load { .. } => return None,
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
    fn same(&mut self, a: &Expr, b: &Expr) -> Option<bool> {
        let mut pending = vec![(a, b)];
        while let Some((a, b)) = pending.pop() {
            self.spend()?;
            match (a, b) {
                (Expr::Const(a), Expr::Const(b)) if a == b => {}
                (Expr::Register(a), Expr::Register(b)) if a == b => {}
                (Expr::Binary(a, al, ar), Expr::Binary(b, bl, br)) if a == b => {
                    pending.extend([(&**al, &**bl), (&**ar, &**br)])
                }
                (
                    Expr::Select {
                        condition: a,
                        taken: at,
                        not_taken: an,
                    },
                    Expr::Select {
                        condition: b,
                        taken: bt,
                        not_taken: bn,
                    },
                ) => pending.extend([(&**a, &**b), (&**at, &**bt), (&**an, &**bn)]),
                _ => return Some(false),
            }
        }
        Some(true)
    }
}

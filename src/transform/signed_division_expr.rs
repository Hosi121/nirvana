//! Source-bound views of signed reciprocal division on arbitrary 64-bit bits.
//!
//! Signedness belongs to the operations, not to an inferred C type. A pure
//! quotient kernel must implement truncation toward zero for every int64 value.
//! The negative domain includes INT64_MIN and permits an error exactly P.
use super::reciprocal_bounds::Reciprocal;
use crate::model::ir::{BinaryOp as B, Expr};

pub const MAX_NODES: usize = 4096;
pub const MAX_DEPTH: usize = 128;
pub const MAX_WORK: usize = 65_536;

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
    let mut work = Work(MAX_WORK);
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
    let mut work = Work(MAX_WORK);
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
    if shift > 63 || divisor.unsigned_abs() > i64::MAX as u64 {
        return None;
    }
    let power = 1u128.checked_shl(64 + shift)?;
    let r = Reciprocal::check(u128::from(multiplier), power, divisor.unsigned_abs())?;
    if r.excess == 0 {
        return None;
    }
    let positive_bound = r.exact_bound(i64::MAX as u64)?;
    let negative_bound = r.exact_bound(1 << 63)?;
    if positive_bound >= power || negative_bound > power {
        return None;
    }
    Some(SignedDivisionEvidence {
        multiplier,
        shift,
        excess: r.excess,
        positive_bound,
        negative_bound,
    })
}

pub fn recognize_remainder(expression: &Expr) -> Option<SignedRemainderView<'_>> {
    if !matches!(expression, Expr::Binary(B::Sub, ..)) {
        return None;
    }
    let mut work = Work(MAX_WORK);
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
        let mut work = Work(MAX_WORK);
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

struct Work(usize);
impl Work {
    fn spend(&mut self) -> Option<()> {
        self.0 = self.0.checked_sub(1)?;
        Some(())
    }
    fn pure(&mut self, expression: &Expr) -> Option<()> {
        let mut pending = vec![(expression, 1)];
        let mut nodes = 0;
        while let Some((e, depth)) = pending.pop() {
            self.spend()?;
            nodes += 1;
            if nodes > MAX_NODES || depth > MAX_DEPTH {
                return None;
            }
            match e {
                Expr::Load { .. } => return None,
                Expr::Binary(_, a, b) => {
                    pending.extend([(a.as_ref(), depth + 1), (b.as_ref(), depth + 1)])
                }
                Expr::Select {
                    condition,
                    taken,
                    not_taken,
                } => pending.extend([
                    (condition.as_ref(), depth + 1),
                    (taken.as_ref(), depth + 1),
                    (not_taken.as_ref(), depth + 1),
                ]),
                _ => {}
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
                    pending.extend([(al.as_ref(), bl.as_ref()), (ar.as_ref(), br.as_ref())])
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
                ) => pending.extend([
                    (a.as_ref(), b.as_ref()),
                    (at.as_ref(), bt.as_ref()),
                    (an.as_ref(), bn.as_ref()),
                ]),
                _ => return Some(false),
            }
        }
        Some(true)
    }
}

pub const DIVIDE_HELPER: &str = r#"
static inline uint64_t nirvana_sdiv64(uint64_t value, int64_t divisor) {
    uint64_t d = (uint64_t)divisor;
    uint64_t magnitude = (value >> 63) ? UINT64_C(0) - value : value;
    uint64_t denominator = divisor < 0 ? UINT64_C(0) - d : d;
    uint64_t q = magnitude / denominator;
    return ((value >> 63) ^ (d >> 63)) ? UINT64_C(0) - q : q;
}
"#;

pub const REMAINDER_HELPER: &str = r#"
static inline uint64_t nirvana_srem64(uint64_t value, int64_t divisor) {
    return value - nirvana_sdiv64(value,divisor) * (uint64_t)divisor;
}
"#;

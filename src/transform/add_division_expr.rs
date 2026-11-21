//! Certified constant division in the unsigned reciprocal-add kernel.
//!
//! Match ((X - t) >> 1) + t, then >> S, with t=UMulHigh(X,M).
//! Neither X-t nor the compensated sum wraps: 0<=t<=X and
//! t+floor((X-t)/2)<=X. No executable IR or dependency is changed.
use super::reciprocal_bounds::Reciprocal;
use crate::model::ir::{BinaryOp, Expr};
pub const MAX_NODES: usize = 4096;
pub const MAX_DEPTH: usize = 128;
pub const MAX_WORK: usize = 65536;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct AddDivisionEvidence {
    /// Raw multiplier M; the mathematical reciprocal is H=2^64+M.
    pub multiplier: u64,
    /// Original outer literal in 0..=62; inner literal is exactly one.
    pub shift: u32,
    /// H*divisor - 2^(65+shift), in [0,divisor).
    pub excess: u64,
    /// Exact maximum of q*excess+H*r over reachable X=q*divisor+r.
    /// It is below 2^(65+shift); the terminal q interval may be partial.
    pub upper_bound: u128,
}
#[derive(Clone, Copy, Debug)]
pub struct AddDivisionView<'a> {
    /// The actual subtraction dividend, including complete original syntax.
    pub value: &'a Expr,
    pub divisor: u64,
    pub evidence: AddDivisionEvidence,
}

/// Constant-depth syntax hint for callers budgeting optional recognition.
/// Recognition and validation provide the arithmetic proof; this only excludes
/// unrelated shifted sums before their callers reserve more analysis work.
pub fn has_kernel_shape(expression: &Expr) -> bool {
    let Expr::Binary(BinaryOp::Shr, average, count) = expression else {
        return false;
    };
    if !matches!(&**count, Expr::Const(0..=62)) {
        return false;
    }
    let Expr::Binary(BinaryOp::Add, a, b) = &**average else {
        return false;
    };
    [(&**a, &**b), (&**b, &**a)]
        .into_iter()
        .any(|(high, half)| {
            matches!(high, Expr::Binary(BinaryOp::UMulHigh, _, _))
                && half_difference(half)
                    .is_some_and(|(_, high)| matches!(high, Expr::Binary(BinaryOp::UMulHigh, _, _)))
        })
}

/// All loads, even in dead lazy arms, and exhausted whole-tree bounds decline.
/// Both Add and high-product operand orders are accepted. Every dividend must
/// be structurally equal; register names, widths, and earlier writes add no facts.
/// M=0 is allowed when its certificate passes (the power-of-two family).
pub fn recognize(expression: &Expr) -> Option<AddDivisionView<'_>> {
    let mut work = Work(MAX_WORK);
    work.pure(expression)?;
    let Expr::Binary(BinaryOp::Shr, average, count) = expression else {
        return None;
    };
    let Expr::Const(shift) = **count else {
        return None;
    };
    if shift > 62 {
        return None;
    }
    let Expr::Binary(BinaryOp::Add, a, b) = &**average else {
        return None;
    };
    for (t, half) in [(&**a, &**b), (&**b, &**a)] {
        let Some((value, inner_t)) = half_difference(half) else {
            continue;
        };
        let Some(multiplier) = high_factor(t, value, &mut work)? else {
            continue;
        };
        if high_factor(inner_t, value, &mut work)? != Some(multiplier) {
            continue;
        }
        let reciprocal = (1_u128 << 64).checked_add(u128::from(multiplier))?;
        let power = 1_u128.checked_shl(65 + shift as u32)?;
        let Some(reciprocal) = Reciprocal::infer(reciprocal, power) else {
            continue;
        };
        let upper_bound = reciprocal.exact_bound(u64::MAX)?;
        let view = AddDivisionView {
            value,
            divisor: reciprocal.divisor,
            evidence: AddDivisionEvidence {
                multiplier,
                shift: shift as u32,
                excess: reciprocal.excess,
                upper_bound,
            },
        };
        if validate(expression, &view) {
            return Some(view);
        }
    }
    None
}

/// Reparse independently and recompute all certificate fields. Both high
/// products must have the same raw dividend and literal multiplier. Binding
/// the borrowed value to the actual subtraction prevents forged clone views.
///
/// Let B=2^64, H=B+M, P=2^(65+S). The safe kernel equals floor(X*H/P),
/// by nested-floor identities; X*H is a mathematical 129-bit quantity, never
/// evaluated here in u128. For X=q*d+r and H*d=P+e, its numerator is
/// q*P+q*e+H*r. Write Q=MAX/d>=1 and R=MAX%d. For q<Q the largest
/// residual is (Q-1)*e+H*(d-1); for q=Q it is Q*e+H*R. Their maximum
/// is exact because e>=0 and H>0. Its strict bound below P proves quotient q.
pub fn validate(expression: &Expr, view: &AddDivisionView<'_>) -> bool {
    validate_inner(expression, view).is_some()
}
fn validate_inner(expression: &Expr, view: &AddDivisionView<'_>) -> Option<()> {
    let mut work = Work(MAX_WORK);
    work.pure(expression)?;
    let evidence = view.evidence;
    if evidence.shift > 62 || view.divisor < 2 {
        return None;
    }
    let Expr::Binary(BinaryOp::Shr, average, count) = expression else {
        return None;
    };
    if !matches!(&**count,Expr::Const(s)if *s==u64::from(evidence.shift)&&*s<=62) {
        return None;
    }
    let Expr::Binary(BinaryOp::Add, left, right) = &**average else {
        return None;
    };
    let mut bound = false;
    for (other, half) in [(&**left, &**right), (&**right, &**left)] {
        let Expr::Binary(BinaryOp::Shr, difference, inner_count) = half else {
            continue;
        };
        if !matches!(&**inner_count, Expr::Const(1)) {
            continue;
        }
        let Expr::Binary(BinaryOp::Sub, value, inside) = &**difference else {
            continue;
        };
        if !std::ptr::eq(&**value, view.value) {
            continue;
        }
        // Verify the two high products independently of the matcher's factor
        // selection, allowing each product's operands to be commuted.
        let mut products_valid = true;
        for product in [other, &**inside] {
            let Expr::Binary(BinaryOp::UMulHigh, a, b) = product else {
                products_valid = false;
                break;
            };
            let mut matched = false;
            for (x, m) in [(&**a, &**b), (&**b, &**a)] {
                if matches!(m,Expr::Const(m)if *m==evidence.multiplier) && work.same(x, value)? {
                    matched = true;
                    break;
                }
            }
            if !matched {
                products_valid = false;
                break;
            }
        }
        if products_valid {
            bound = true;
            break;
        }
    }
    if !bound {
        return None;
    }
    let h = (1_u128 << 64).checked_add(u128::from(evidence.multiplier))?;
    let p = 1_u128.checked_shl(65 + evidence.shift)?;
    let reciprocal = Reciprocal::check(h, p, view.divisor)?;
    let upper = reciprocal.exact_bound(u64::MAX)?;
    (reciprocal.excess == evidence.excess && upper == evidence.upper_bound && upper < p)
        .then_some(())
}
fn half_difference(e: &Expr) -> Option<(&Expr, &Expr)> {
    let Expr::Binary(BinaryOp::Shr, difference, count) = e else {
        return None;
    };
    if !matches!(&**count, Expr::Const(1)) {
        return None;
    }
    let Expr::Binary(BinaryOp::Sub, x, t) = &**difference else {
        return None;
    };
    Some((x, t))
}
fn high_factor(e: &Expr, value: &Expr, work: &mut Work) -> Option<Option<u64>> {
    let Expr::Binary(BinaryOp::UMulHigh, a, b) = e else {
        return Some(None);
    };
    for (x, m) in [(&**a, &**b), (&**b, &**a)] {
        if let Expr::Const(m) = m
            && work.same(x, value)?
        {
            return Some(Some(*m));
        }
    }
    Some(None)
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
        while let Some((e, d)) = pending.pop() {
            self.spend()?;
            nodes += 1;
            if nodes > MAX_NODES || d > MAX_DEPTH {
                return None;
            }
            match e {
                Expr::Const(_) | Expr::Register(_) => {}
                Expr::Load { .. } => return None,
                Expr::Binary(_, a, b) => pending.extend([(&**a, d + 1), (&**b, d + 1)]),
                Expr::Select {
                    condition,
                    taken,
                    not_taken,
                } => pending.extend([
                    (&**condition, d + 1),
                    (&**taken, d + 1),
                    (&**not_taken, d + 1),
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

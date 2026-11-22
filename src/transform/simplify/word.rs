//! Remove projections inside operations whose low bits depend only on low
//! operand bits. The caller retains the outer projection; right shifts,
//! comparisons, divisions and addresses remain opaque.
use super::{B, Expr, U, simplify_impl};
use crate::model::ir::Width;

pub(super) fn rewrite(value: &Expr, opaque: &dyn Fn(&Expr) -> bool) -> Option<Expr> {
    match value {
        Expr::Unary(op @ (U::Extract { start: 0, width } | U::SignExtend(width)), child) => {
            project(child, *width, opaque).map(|child| Expr::unary(*op, child))
        }
        Expr::Binary(B::And, a, b) => {
            for (child, mask) in [(&**a, super::constant(b)), (&**b, super::constant(a))] {
                if let Some(width) = [Width::U8, Width::U16, Width::U32]
                    .into_iter()
                    .find(|w| mask == Some(w.mask()))
                    && let Some(child) = project(child, width, opaque)
                {
                    return Some(Expr::binary(B::And, child, Expr::Const(width.mask())));
                }
            }
            None
        }
        Expr::Binary(op @ (B::Add | B::Sub), left, right) => {
            let (a, ca) = super::scaled(left);
            let (b, cb) = super::scaled(right);
            if a != b || !super::pure(a) {
                return None;
            }
            Some(match op.evaluate(ca, cb) {
                0 => Expr::Const(0),
                1 => a.clone(),
                n => Expr::binary(B::Mul, a.clone(), Expr::Const(n)),
            })
        }
        _ => None,
    }
}

/// Return a smaller/equal tree with the same low `width` bits. Loads remain
/// once, in order, at their original lazy evaluation sites. Work exhaustion
/// keeps the original expression rather than publishing a partial result.
fn project(value: &Expr, width: Width, opaque: &dyn Fn(&Expr) -> bool) -> Option<Expr> {
    if width == Width::U64 {
        return None;
    }
    let candidate = walk(value, width, &mut 4096, 0, opaque)?;
    (candidate != *value).then(|| simplify_impl(&candidate, true, opaque))
}

fn walk(
    value: &Expr,
    width: Width,
    work: &mut usize,
    depth: usize,
    opaque: &dyn Fn(&Expr) -> bool,
) -> Option<Expr> {
    if *work == 0 || depth > 128 {
        return None;
    }
    *work -= 1;
    if opaque(value) {
        return Some(value.clone());
    }
    let mut child = |value: &Expr| walk(value, width, work, depth + 1, opaque);
    Some(match value {
        Expr::Const(n) => Expr::Const(n & width.mask()),
        Expr::Unary(
            U::Extract {
                start: 0,
                width: from,
            }
            | U::SignExtend(from),
            inner,
        ) if *from >= width => child(inner)?,
        Expr::Binary(B::And, a, b) if matches!(&**b, Expr::Const(mask) if mask & width.mask() == width.mask()) => {
            child(a)?
        }
        Expr::Binary(B::And, a, b) if matches!(&**a, Expr::Const(mask) if mask & width.mask() == width.mask()) => {
            child(b)?
        }
        Expr::Binary(op @ (B::Add | B::Sub | B::Mul | B::And | B::Or | B::Xor), a, b) => {
            Expr::binary(*op, child(a)?, child(b)?)
        }
        // The shift count is observed at full width, with the IR's &63 rule.
        Expr::Binary(B::Shl, a, b) => Expr::binary(B::Shl, child(a)?, (**b).clone()),
        _ => value.clone(),
    })
}

//! Advisory modular-index alignment; source IR and captured load sites stay intact.
use super::*;
use std::borrow::Cow;

fn fits(value: ValueId, mask: u64, caps: &BTreeMap<ValueId, u8>) -> bool {
    caps.get(&value).is_some_and(|&bits| {
        let low = if bits == 64 {
            u64::MAX
        } else if bits < 64 {
            (1u64 << bits) - 1
        } else {
            return false;
        };
        mask & low == low
    })
}
fn modular(term: &PatternExpr) -> Option<(ValueId, u64, u64)> {
    let PatternExpr::Binary(BinaryOp::And, a, b) = term else {
        return None;
    };
    let (inner, mask) = match (&**a, &**b) {
        (inner, PatternExpr::Constant(mask)) | (PatternExpr::Constant(mask), inner) => {
            (inner, *mask)
        }
        _ => return None,
    };
    match inner {
        PatternExpr::Value(value) => Some((*value, 0, mask)),
        PatternExpr::Binary(BinaryOp::Add, a, b) => match (&**a, &**b) {
            (PatternExpr::Value(value), PatternExpr::Constant(offset))
            | (PatternExpr::Constant(offset), PatternExpr::Value(value)) => {
                Some((*value, *offset, mask))
            }
            _ => None,
        },
        _ => None,
    }
}
fn form(value: ValueId, offset: u64, mask: u64) -> PatternExpr {
    PatternExpr::Binary(
        BinaryOp::And,
        Box::new(PatternExpr::Binary(
            BinaryOp::Add,
            Box::new(PatternExpr::Value(value)),
            Box::new(PatternExpr::Constant(offset)),
        )),
        Box::new(PatternExpr::Constant(mask)),
    )
}
pub(super) fn align<'a>(
    terms: &[&'a PatternExpr],
    caps: &BTreeMap<ValueId, u8>,
    budget: &mut Budget,
) -> Option<Vec<Cow<'a, PatternExpr>>> {
    let (value, _, mask) = terms.iter().find_map(|term| modular(term))?;
    if !fits(value, mask, caps) {
        return None;
    }
    budget.spend(terms.len())?;
    let mut result = Vec::new();
    let mut changed = false;
    for &term in terms {
        let offset = if *term == PatternExpr::Value(value) {
            0
        } else {
            let (next, offset, next_mask) = modular(term)?;
            if next != value || next_mask != mask {
                return None;
            }
            offset
        };
        let canonical = form(value, offset, mask);
        if term == &canonical {
            result.push(Cow::Borrowed(term));
        } else {
            budget.spend(5)?;
            for _ in 0..5 {
                budget.node()?;
            }
            changed = true;
            result.push(Cow::Owned(canonical));
        }
    }
    changed.then_some(result)
}
/// Compare proposal terms after bounded pure identities and advisory caps.
/// This creates no proof: the region verifier still sees the original source.
pub(super) fn fold(
    term: &PatternExpr,
    caps: &BTreeMap<ValueId, u8>,
    budget: &mut Budget,
    depth: usize,
) -> Option<PatternExpr> {
    budget.spend(1)?;
    budget.node()?;
    if depth > MAX_DEPTH {
        return None;
    }
    Some(match term {
        PatternExpr::Constant(value) => PatternExpr::Constant(*value),
        PatternExpr::Value(value) => PatternExpr::Value(*value),
        PatternExpr::Accumulator => PatternExpr::Accumulator,
        PatternExpr::Loaded => PatternExpr::Loaded,
        PatternExpr::Lane => PatternExpr::Lane,
        PatternExpr::Unary(op, value) => {
            PatternExpr::Unary(*op, Box::new(fold(value, caps, budget, depth + 1)?))
        }
        PatternExpr::Binary(op, a, b) => {
            let mut a = fold(a, caps, budget, depth + 1)?;
            let mut b = fold(b, caps, budget, depth + 1)?;
            if matches!(op, BinaryOp::Add | BinaryOp::And)
                && matches!(a, PatternExpr::Constant(_))
                && !matches!(b, PatternExpr::Constant(_))
            {
                std::mem::swap(&mut a, &mut b);
            }
            if *op == BinaryOp::Add && b == PatternExpr::Constant(0) {
                return Some(a);
            }
            match (&a, &b) {
                (PatternExpr::Value(value), PatternExpr::Constant(mask))
                    if *op == BinaryOp::And && fits(*value, *mask, caps) =>
                {
                    return Some(PatternExpr::Value(*value));
                }
                _ => PatternExpr::Binary(*op, Box::new(a), Box::new(b)),
            }
        }
        PatternExpr::Select(a, b, c) => PatternExpr::Select(
            Box::new(fold(a, caps, budget, depth + 1)?),
            Box::new(fold(b, caps, budget, depth + 1)?),
            Box::new(fold(c, caps, budget, depth + 1)?),
        ),
    })
}

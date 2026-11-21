//! One word-level proof matcher for syntax trees and immutable value graphs.
use super::source::{Node, Source};
use super::*;

#[derive(Clone, Copy)]
struct Kernel<K> {
    value: K,
    product: K,
    multiplier: u64,
    shift: u32,
    negate: bool,
}

pub(super) fn recognize<S: Source>(s: &S, e: S::Key, work: &mut Work) -> Option<WordView<S::Key>> {
    let (width, low) = root(s, e)?;
    s.pure(e, work)?;
    candidates(s, low, width, work)?.into_iter().next()
}
pub(super) fn validate<S: Source>(s: &S, e: S::Key, v: &WordView<S::Key>, work: &mut Work) -> bool {
    let Some((width, low)) = root(s, e) else {
        return false;
    };
    if width != v.width || s.pure(e, work).is_none() {
        return false;
    }
    candidates(s, low, width, work).is_some_and(|all| {
        all.into_iter().any(|a| {
            s.identical(a.value, v.value)
                && s.identical(a.product, v.product)
                && a.divisor == v.divisor
                && a.operation == v.operation
                && a.evidence == v.evidence
        })
    })
}
fn root<S: Source>(s: &S, e: S::Key) -> Option<(Width, S::Key)> {
    if let Node::Unary(U::Extract { start: 0, width }, low) = s.node(e)?
        && width != Width::U64
    {
        return Some((width, low));
    }
    let (a, b) = binary(s, e, B::And)?;
    for (low, mask) in [(a, b), (b, a)] {
        for width in [Width::U8, Width::U16, Width::U32] {
            if number(s, mask) == Some(width.mask()) {
                return Some((width, low));
            }
        }
    }
    None
}
fn certified<K: Copy>(k: Kernel<K>, width: Width) -> Option<WordView<K>> {
    let proof = SignedReciprocal::infer(k.multiplier, width.bits(), k.shift)?;
    let d = i64::try_from(proof.divisor).ok()?;
    Some(WordView {
        value: k.value,
        product: k.product,
        width,
        divisor: if k.negate { -d } else { d },
        operation: Operation::Quotient,
        evidence: Evidence {
            multiplier: k.multiplier,
            shift: k.shift,
            excess: proof.excess,
            positive_bound: proof.positive_bound,
            negative_bound: proof.negative_bound,
        },
    })
}
fn candidates<S: Source>(
    s: &S,
    low: S::Key,
    width: Width,
    work: &mut Work,
) -> Option<Vec<WordView<S::Key>>> {
    let mut result = Vec::new();
    for k in quotients(s, low, width, work)? {
        result.extend(certified(k, width));
    }
    let Some((value, product)) = binary(s, project(s, low, width, work)?, B::Sub) else {
        return Some(result);
    };
    let mut pending = vec![product];
    while let Some(e) = pending.pop() {
        work.spend()?;
        for k in quotients(s, e, width, work)? {
            let Some(mut view) = certified(k, width) else {
                continue;
            };
            if same_word(s, value, view.value, width, work)?
                && coefficient(s, product, e, width, work)?
                    == Some(view.divisor as u64 & width.mask())
            {
                view.value = project(s, value, width, work)?;
                view.operation = Operation::Remainder;
                result.push(view);
            }
        }
        match s.node(e)? {
            Node::Unary(_, v) => pending.push(v),
            Node::Binary(_, a, b) => pending.extend([a, b]),
            _ => {}
        }
    }
    Some(result)
}
fn quotients<S: Source>(
    s: &S,
    e: S::Key,
    width: Width,
    work: &mut Work,
) -> Option<Vec<Kernel<S::Key>>> {
    work.spend()?;
    let Some((a, b)) = binary(s, project(s, e, width, work)?, B::Sub) else {
        return Some(Vec::new());
    };
    let mut result = Vec::new();
    for (estimate, sign, negate) in [(a, b, false), (b, a, true)] {
        let Some((signed, count)) = binary(s, project(s, sign, width, work)?, B::AShr) else {
            continue;
        };
        if !number(s, count).is_some_and(|n| n == u64::from(width.bits() - 1) || n == 63) {
            continue;
        }
        let Some(sign_value) = signed_input(s, signed, width, work)? else {
            continue;
        };
        for mut k in estimates(s, estimate, width, work)? {
            if same_word(s, k.value, sign_value, width, work)? {
                k.negate = negate;
                result.push(k);
            }
        }
    }
    Some(result)
}
fn estimates<S: Source>(
    s: &S,
    e: S::Key,
    width: Width,
    work: &mut Work,
) -> Option<Vec<Kernel<S::Key>>> {
    let e = project(s, e, width, work)?;
    let mut result = Vec::new();
    if let Some(k) = high_product(s, e, width, work)?
        && k.multiplier >> (width.bits() - 1) == 0
    {
        result.push(k);
    }
    let (core, shift) = match binary(s, e, B::AShr) {
        Some((signed, n)) if number(s, n).is_some_and(|n| n < u64::from(width.bits())) => {
            let Some(core) = signed_input(s, signed, width, work)? else {
                return Some(result);
            };
            (core, number(s, n)? as u32)
        }
        _ => (e, 0),
    };
    let core = project(s, core, width, work)?;
    let terms = match binary(s, core, B::Add) {
        Some((a, b)) => vec![(a, Some(b)), (b, Some(a))],
        None => vec![(core, None)],
    };
    for (high, add) in terms {
        let Some(mut k) = high_product(s, project(s, high, width, work)?, width, work)? else {
            continue;
        };
        if k.shift != 0 || (k.multiplier >> (width.bits() - 1) != 0) != add.is_some() {
            continue;
        }
        if let Some(add) = add
            && !same_word(s, add, k.value, width, work)?
        {
            continue;
        }
        k.shift = shift;
        result.push(k);
    }
    Some(result)
}
fn high_product<S: Source>(
    s: &S,
    e: S::Key,
    width: Width,
    work: &mut Work,
) -> Option<Option<Kernel<S::Key>>> {
    work.spend()?;
    let (product, shift) = match s.node(e)? {
        Node::Binary(op @ (B::Shr | B::AShr), product, count) => {
            let Some(n) = number(s, count) else {
                return Some(None);
            };
            let bits = u64::from(width.bits());
            // Logical sign fill may differ only above the observed word.
            if n < bits || n >= 2 * bits || (op == B::Shr && n > 64 - bits) {
                return Some(None);
            }
            (product, (n - bits) as u32)
        }
        _ => return Some(None),
    };
    let Some((a, b)) = binary(s, product, B::Mul) else {
        return Some(None);
    };
    for (value, factor) in [(a, b), (b, a)] {
        let Some(factor) = number(s, factor) else {
            continue;
        };
        let m = factor & width.mask();
        if U::SignExtend(width).evaluate(m) != factor {
            continue;
        }
        let Some(value) = signed_input(s, value, width, work)? else {
            continue;
        };
        return Some(Some(Kernel {
            value: project(s, value, width, work)?,
            product,
            multiplier: m,
            shift,
            negate: false,
        }));
    }
    Some(None)
}
fn signed_input<S: Source>(
    s: &S,
    mut e: S::Key,
    width: Width,
    work: &mut Work,
) -> Option<Option<S::Key>> {
    loop {
        work.spend()?;
        match s.node(e)? {
            Node::Unary(U::SignExtend(Width::U64), v) => e = v,
            Node::Binary(B::And, a, b) if number(s, a) == Some(u64::MAX) => e = b,
            Node::Binary(B::And, a, b) if number(s, b) == Some(u64::MAX) => e = a,
            Node::Unary(U::SignExtend(w), v) if w == width => return Some(Some(v)),
            _ => return Some(None),
        }
    }
}
fn project<S: Source>(s: &S, mut e: S::Key, width: Width, work: &mut Work) -> Option<S::Key> {
    loop {
        work.spend()?;
        e = match s.node(e)? {
            Node::Binary(B::Insert { start: 0, width: w }, _, value)
                if w.bits() >= width.bits() =>
            {
                value
            }
            Node::Binary(B::Insert { start, .. }, base, _) if u32::from(start) >= width.bits() => {
                base
            }
            Node::Unary(U::SignExtend(w), v) if w.bits() >= width.bits() => v,
            Node::Unary(U::Extract { start: 0, width: w }, v) if w.bits() >= width.bits() => v,
            Node::Binary(B::And, a, b)
                if number(s, b).is_some_and(|n| n & width.mask() == width.mask()) =>
            {
                a
            }
            Node::Binary(B::And, a, b)
                if number(s, a).is_some_and(|n| n & width.mask() == width.mask()) =>
            {
                b
            }
            _ => return Some(e),
        };
    }
}
pub(super) fn same_word<S: Source>(
    s: &S,
    a: S::Key,
    b: S::Key,
    width: Width,
    work: &mut Work,
) -> Option<bool> {
    let a = project(s, a, width, work)?;
    let b = project(s, b, width, work)?;
    s.same(a, b, work)
}
fn coefficient<S: Source>(
    s: &S,
    e: S::Key,
    q: S::Key,
    width: Width,
    work: &mut Work,
) -> Option<Option<u64>> {
    let e = project(s, e, width, work)?;
    if same_word(s, e, q, width, work)? {
        return Some(Some(1));
    }
    let value = match s.node(e)? {
        Node::Constant(0) => Some(0),
        Node::Binary(op @ (B::Add | B::Sub), a, b) => match (
            coefficient(s, a, q, width, work)?,
            coefficient(s, b, q, width, work)?,
        ) {
            (Some(a), Some(b)) => Some(op.evaluate(a, b)),
            _ => None,
        },
        Node::Binary(B::Mul, a, b) => match (number(s, a), number(s, b)) {
            (_, Some(n)) => coefficient(s, a, q, width, work)?.map(|v| v.wrapping_mul(n)),
            (Some(n), _) => coefficient(s, b, q, width, work)?.map(|v| v.wrapping_mul(n)),
            _ => None,
        },
        Node::Binary(B::And, a, b) => {
            let term = match (number(s, a), number(s, b)) {
                (_, Some(m)) => Some((a, m)),
                (Some(m), _) => Some((b, m)),
                _ => None,
            };
            if let Some((v, mask)) = term {
                coefficient(s, v, q, width, work)?.filter(|n| {
                    let zeros = if *n == 0 {
                        width.mask()
                    } else {
                        (1u64 << n.trailing_zeros()) - 1
                    };
                    (!mask & width.mask() & !zeros) == 0
                })
            } else {
                None
            }
        }
        Node::Binary(B::Shl, v, n) => match number(s, n) {
            Some(n) if n < 64 => {
                coefficient(s, v, q, width, work)?.map(|v| v.wrapping_shl(n as u32))
            }
            _ => None,
        },
        _ => None,
    };
    Some(value.map(|n| n & width.mask()))
}
fn binary<S: Source>(s: &S, e: S::Key, op: B) -> Option<(S::Key, S::Key)> {
    if let Node::Binary(actual, a, b) = s.node(e)?
        && actual == op
    {
        Some((a, b))
    } else {
        None
    }
}
fn number<S: Source>(s: &S, e: S::Key) -> Option<u64> {
    if let Node::Constant(n) = s.node(e)? {
        Some(n)
    } else {
        None
    }
}

//! LLVM-style rounding toward zero: arithmetic estimate plus its logical
//! sign bit. The sign may be taken before or after the arithmetic postshift.
use super::*;

pub(super) fn quotients<S: Source>(
    s: &S,
    e: S::Key,
    width: Width,
    work: &mut Work,
) -> Option<Vec<Kernel<S::Key>>> {
    let Some((a, b)) = binary(s, project(s, e, width, work)?, B::Add) else {
        return Some(Vec::new());
    };
    let mut result = Vec::new();
    for (estimate, sign) in [(a, b), (b, a)] {
        let estimate = project(s, estimate, width, work)?;
        let (core, shift) = match binary(s, estimate, B::AShr) {
            Some((signed, count))
                if number(s, count).is_some_and(|n| n < u64::from(width.bits())) =>
            {
                let Some(core) = signed_input(s, signed, width, work)? else {
                    continue;
                };
                (project(s, core, width, work)?, number(s, count)? as u32)
            }
            _ => (estimate, 0),
        };
        if !sign_of(s, sign, core, estimate, width, work)? {
            continue;
        }
        let terms = super::super::ring::form(s, core, width, work)?;
        for (high, _) in terms.terms {
            let Some(base) = high_product(s, high, width, work)? else {
                continue;
            };
            if base.shift != 0 && (shift != 0 || !same_word(s, core, high, width, work)?) {
                continue;
            }
            let negative_magic = base.multiplier >> (width.bits() - 1) != 0;
            for negative in [false, true] {
                let mut kernel = base;
                let coefficient = match (negative, negative_magic) {
                    (false, false) | (true, true) => 0,
                    (false, true) => 1,
                    (true, false) => u64::MAX,
                };
                if !super::super::ring::matches(
                    s,
                    core,
                    &[(high, 1), (kernel.value, coefficient)],
                    width,
                    work,
                )? {
                    continue;
                }
                if negative {
                    kernel.multiplier = kernel.multiplier.wrapping_neg() & width.mask();
                }
                kernel.shift += shift;
                kernel.negate = negative;
                kernel.reversed = negative;
                result.push(kernel);
            }
        }
    }
    Some(result)
}

fn sign_of<S: Source>(
    s: &S,
    sign: S::Key,
    core: S::Key,
    estimate: S::Key,
    width: Width,
    work: &mut Work,
) -> Option<bool> {
    let Some((input, count)) = binary(s, project(s, sign, width, work)?, B::Shr) else {
        return Some(false);
    };
    let value = if number(s, count) == Some(u64::from(width.bits() - 1))
        && word_bounded(s, input, width)?
    {
        input
    } else if number(s, count) == Some(63) {
        let Some(value) = signed_input(s, input, width, work)? else {
            return Some(false);
        };
        value
    } else {
        return Some(false);
    };
    Some(same_word(s, value, core, width, work)? || same_word(s, value, estimate, width, work)?)
}

fn word_bounded<S: Source>(s: &S, input: S::Key, width: Width) -> Option<bool> {
    Some(match s.node(input)? {
        Node::Unary(U::Extract { start: 0, width: w }, _) => w.bits() <= width.bits(),
        Node::Binary(B::And, a, b) => [a, b]
            .into_iter()
            .any(|n| number(s, n).is_some_and(|m| m <= width.mask())),
        Node::Constant(n) => n <= width.mask(),
        _ => false,
    })
}

//! Match n - q*d as a word equation after add/sub/LEA distribution, while
//! preserving the exact signed full product that certifies q.
use super::*;

pub(super) fn distributed<S: Source>(
    s: &S,
    low: S::Key,
    width: Width,
    work: &mut Work,
) -> Option<Vec<WordView<S::Key>>> {
    let mut pending = vec![low];
    let mut seen = Vec::new();
    let mut result = Vec::new();
    while let Some(e) = pending.pop() {
        work.spend()?;
        if seen.iter().any(|old| s.identical(*old, e)) {
            continue;
        }
        if seen.len() >= MAX_NODES {
            return None;
        }
        seen.push(e);
        for kernel in quotients(s, e, width, work)? {
            let Some(mut view) = certified(kernel, width) else {
                continue;
            };
            if super::super::ring::matches(
                s,
                low,
                &[(view.value, 1), (e, (view.divisor as u64).wrapping_neg())],
                width,
                work,
            )? {
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

//! Bounded affine equality modulo the observed word. Right shifts, narrower
//! masks and captured loads are opaque atoms; only ring homomorphisms expand.
use super::source::{Node, Source};
use super::*;

pub(super) struct Form<K> {
    pub constant: u64,
    pub terms: Vec<(K, u64)>,
}

pub(super) fn form<S: Source>(
    s: &S,
    key: S::Key,
    width: Width,
    work: &mut Work,
) -> Option<Form<S::Key>> {
    let mut result = Form {
        constant: 0,
        terms: Vec::new(),
    };
    add(s, &mut result, key, 1, width, work, 0)?;
    Some(result)
}

fn add<S: Source>(
    s: &S,
    out: &mut Form<S::Key>,
    key: S::Key,
    scale: u64,
    width: Width,
    work: &mut Work,
    depth: usize,
) -> Option<()> {
    work.spend()?;
    if depth > MAX_DEPTH {
        return None;
    }
    let key = super::matcher::project(s, key, width, work)?;
    let scale = scale & width.mask();
    if scale == 0 {
        return Some(());
    }
    let mut child = |out: &mut Form<S::Key>, k, c| add(s, out, k, c, width, work, depth + 1);
    match s.node(key)? {
        Node::Constant(n) => {
            out.constant = out.constant.wrapping_add(n.wrapping_mul(scale)) & width.mask()
        }
        Node::Binary(B::Add, a, b) => {
            child(out, a, scale)?;
            child(out, b, scale)?;
        }
        Node::Binary(B::Sub, a, b) => {
            child(out, a, scale)?;
            child(out, b, scale.wrapping_neg())?;
        }
        Node::Binary(B::Mul, a, b) => {
            if let Node::Constant(n) = s.node(b)? {
                child(out, a, scale.wrapping_mul(n))?;
            } else if let Node::Constant(n) = s.node(a)? {
                child(out, b, scale.wrapping_mul(n))?;
            } else {
                atom(s, out, key, scale, width, work)?;
            }
        }
        Node::Binary(B::Shl, a, b) => {
            if let Node::Constant(n) = s.node(b)? {
                child(out, a, scale.wrapping_shl((n & 63) as u32))?;
            } else {
                atom(s, out, key, scale, width, work)?;
            }
        }
        _ => atom(s, out, key, scale, width, work)?,
    }
    Some(())
}

fn atom<S: Source>(
    s: &S,
    out: &mut Form<S::Key>,
    key: S::Key,
    scale: u64,
    width: Width,
    work: &mut Work,
) -> Option<()> {
    for (old, coefficient) in &mut out.terms {
        if s.same(*old, key, work)? {
            *coefficient = coefficient.wrapping_add(scale) & width.mask();
            return Some(());
        }
    }
    if out.terms.len() >= 64 {
        return None;
    }
    out.terms.push((key, scale));
    Some(())
}

pub(super) fn matches<S: Source>(
    s: &S,
    actual: S::Key,
    expected: &[(S::Key, u64)],
    width: Width,
    work: &mut Work,
) -> Option<bool> {
    let mut difference = form(s, actual, width, work)?;
    for &(key, scale) in expected {
        add(
            s,
            &mut difference,
            key,
            scale.wrapping_neg(),
            width,
            work,
            0,
        )?;
    }
    Some(difference.constant == 0 && difference.terms.iter().all(|(_, n)| *n == 0))
}

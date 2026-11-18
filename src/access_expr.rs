//! Borrowed indexed-address presentation for bounded, pure current syntax.
//!
//! The expression remains executable IR. No register producer is consulted and
//! no register occurrence is folded, substituted, cloned, or dropped. Arithmetic
//! is modulo 2^64; a view means `base + index * stride + offset`.

use crate::ir::{BinaryOp, Expr};

pub const MAX_NODES: usize = 4096;
pub const MAX_DEPTH: usize = 128;

#[derive(Clone, Copy, Debug)]
pub struct IndexedAddress<'a> {
    pub base: &'a Expr,
    pub index: &'a Expr,
    pub stride: u64,
    pub offset: u64,
}

/// Recognize one base and one explicitly scaled index, with literal offsets.
///
/// Additions and subtractions of a literal are peeled; other base/index syntax
/// stays opaque and borrowed. Multiplication accepts the literal on either side,
/// and left shifts mask their literal count with 63. Nested literal scales may
/// combine, but a resulting stride of zero or one declines. Both operands must
/// contain a register read. Multiple unscaled or scaled terms are ambiguous and
/// decline, including duplicate register occurrences which could be combined
/// algebraically. Constant bases, negated dynamic terms, and producer expansion
/// are outside this conservative slice.
pub fn recognize(address: &Expr) -> Option<IndexedAddress<'_>> {
    bounded_pure(address)?;
    let mut pending = vec![address];
    let mut terms = Vec::new();
    let mut offset = 0_u64;
    while let Some(expression) = pending.pop() {
        match expression {
            Expr::Binary(BinaryOp::Add, left, right) => {
                pending.extend([&**right, &**left]);
            }
            Expr::Binary(BinaryOp::Sub, left, right) => {
                if let Expr::Const(value) = &**right {
                    offset = offset.wrapping_sub(*value);
                    pending.push(left);
                } else {
                    terms.push(expression);
                }
            }
            Expr::Const(value) => offset = offset.wrapping_add(*value),
            _ => terms.push(expression),
        }
        // Peeling cannot remove a nonliteral term later. Decline without
        // enumerating combinations or using register-name equality.
        if terms.len() > 2 {
            return None;
        }
    }
    let [first, second] = terms.as_slice() else {
        return None;
    };
    let (base, index, stride) = match (literal_scale(first), literal_scale(second)) {
        (None, Some((index, stride))) => (*first, index, stride),
        (Some((index, stride)), None) => (*second, index, stride),
        _ => return None,
    };
    if stride < 2 || !has_register(base) || !has_register(index) {
        return None;
    }
    let view = IndexedAddress {
        base,
        index,
        stride,
        offset,
    };
    validate(address, &view).then_some(view)
}

/// Independently certify exact modular identity and the original read operands.
///
/// Pointer identity, rather than structural or register-name equality, binds
/// each operand exactly once. Every other leaf must be a literal, so an omitted
/// register read (even a cancelling one) cannot validate. A lazy expression can
/// only occur inside a complete borrowed operand. Whole-tree purity and bounds
/// are checked before inspecting a possibly forged view's operands.
pub fn validate(address: &Expr, view: &IndexedAddress<'_>) -> bool {
    if bounded_pure(address).is_none() || view.stride < 2 || std::ptr::eq(view.base, view.index) {
        return false;
    }
    let mut bindings = Bindings::default();
    let Some(identity) = certify(address, view, false, &mut bindings) else {
        return false;
    };
    bindings.base == 1
        && bindings.index == 1
        && bindings.explicit_scale
        && identity.base == 1
        && identity.index == view.stride
        && identity.offset == view.offset
        // These references have now been pointer-bound inside the bounded tree.
        && has_register(view.base)
        && has_register(view.index)
}

/// Iterative preflight also visits every lazy arm. There is no recursive Expr
/// equality/clone anywhere in this module, including on failed/forged views.
fn bounded_pure(expression: &Expr) -> Option<()> {
    let mut pending = vec![(expression, 1_usize)];
    let mut nodes = 0;
    while let Some((expression, depth)) = pending.pop() {
        nodes += 1;
        if nodes > MAX_NODES || depth > MAX_DEPTH {
            return None;
        }
        match expression {
            Expr::Const(_) | Expr::Register(_) => {}
            Expr::Load { .. } => return None,
            Expr::Binary(_, left, right) => {
                pending.extend([(&**left, depth + 1), (&**right, depth + 1)]);
            }
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

fn has_register(expression: &Expr) -> bool {
    let mut pending = vec![expression];
    while let Some(expression) = pending.pop() {
        match expression {
            Expr::Register(_) => return true,
            Expr::Const(_) => {}
            Expr::Binary(_, left, right) => pending.extend([&**left, &**right]),
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => pending.extend([&**condition, &**taken, &**not_taken]),
            Expr::Load { .. } => return false, // Preflight excludes this case.
        }
    }
    false
}

fn literal_scale(mut expression: &Expr) -> Option<(&Expr, u64)> {
    let mut stride = 1_u64;
    let mut explicit = false;
    loop {
        let (value, factor) = match expression {
            Expr::Binary(BinaryOp::Mul, left, right) => match (&**left, &**right) {
                (Expr::Const(factor), value) | (value, Expr::Const(factor)) => (value, *factor),
                _ => break,
            },
            Expr::Binary(BinaryOp::Shl, value, count) => {
                let Expr::Const(count) = &**count else {
                    break;
                };
                (&**value, 1_u64 << (count & 63))
            }
            _ => break,
        };
        explicit = true;
        stride = stride.wrapping_mul(factor);
        expression = value;
    }
    explicit.then_some((expression, stride))
}

#[derive(Default)]
struct Bindings {
    base: usize,
    index: usize,
    explicit_scale: bool,
}

struct Identity {
    base: u64,
    index: u64,
    offset: u64,
}

impl Identity {
    fn scale(self, factor: u64) -> Self {
        Self {
            base: self.base.wrapping_mul(factor),
            index: self.index.wrapping_mul(factor),
            offset: self.offset.wrapping_mul(factor),
        }
    }
}

// Recursion is at most MAX_DEPTH after iterative preflight. This verifier uses
// affine arithmetic, independently of the recognizer's term/scale selection.
fn certify(
    expression: &Expr,
    view: &IndexedAddress<'_>,
    scaled: bool,
    bindings: &mut Bindings,
) -> Option<Identity> {
    if std::ptr::eq(expression, view.base) {
        bindings.base += 1;
        return Some(Identity {
            base: 1,
            index: 0,
            offset: 0,
        });
    }
    if std::ptr::eq(expression, view.index) {
        bindings.index += 1;
        bindings.explicit_scale |= scaled;
        return Some(Identity {
            base: 0,
            index: 1,
            offset: 0,
        });
    }
    match expression {
        Expr::Const(value) => Some(Identity {
            base: 0,
            index: 0,
            offset: *value,
        }),
        Expr::Binary(op @ (BinaryOp::Add | BinaryOp::Sub), left, right) => {
            let left = certify(left, view, scaled, bindings)?;
            let right = certify(right, view, scaled, bindings)?;
            let sign = if *op == BinaryOp::Add { 1 } else { u64::MAX };
            let right = right.scale(sign);
            Some(Identity {
                base: left.base.wrapping_add(right.base),
                index: left.index.wrapping_add(right.index),
                offset: left.offset.wrapping_add(right.offset),
            })
        }
        Expr::Binary(BinaryOp::Mul, left, right) => {
            // Deliberately reparse the literal side here, rather than trusting
            // the matcher's scale extraction or any stored certificate fields.
            match (&**left, &**right) {
                (Expr::Const(factor), value) | (value, Expr::Const(factor)) => {
                    Some(certify(value, view, scaled || *factor != 1, bindings)?.scale(*factor))
                }
                _ => None,
            }
        }
        Expr::Binary(BinaryOp::Shl, value, count) => {
            let Expr::Const(count) = &**count else {
                return None;
            };
            let factor = 1_u64 << (count & 63);
            Some(certify(value, view, scaled || factor != 1, bindings)?.scale(factor))
        }
        _ => None,
    }
}

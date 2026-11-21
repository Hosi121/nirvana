//! Conservative syntax recovery for one input-origin base and one index term.
//!
//! This describes modular guest addresses, not array lengths, bounds, element
//! types, ownership, or non-aliasing. The caller supplies facts at the original
//! evaluation point; the returned index must still be evaluated at that point.

use crate::model::ir::{BinaryOp, Expr, Reg};

const MAX_NODES: usize = 4096;
const MAX_DEPTH: usize = 128;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct IndexedAddress {
    pub register: Reg,
    pub offset: i64,
    pub index: Expr,
    pub stride: u64,
}

/// Recover `entry(register) + offset + index * stride`, modulo 2^64.
///
/// `origin(expr)` must mean that `expr` equals the named entry register plus
/// its offset at the current point. A positive coefficient-one resolved subtree
/// at the additive top level is one base candidate; its descendants are not
/// additional candidates. Multiple such candidates reject recovery. A scaled
/// or opaque index can contain input-origin registers, including aliased bases.
/// Loads and selects are rejected before querying facts, even in a subtree the
/// callback would resolve. No evaluation may be hoisted across assignments.
pub fn recover_indexed(
    address: &Expr,
    origin: impl Fn(&Expr) -> Option<(Reg, i64)>,
) -> Option<IndexedAddress> {
    let mut remaining = MAX_NODES;
    validate(address, &mut remaining, 0)?;
    let mut parts = Parts {
        base: None,
        offset: 0,
        index: None,
    };
    collect(address, false, &origin, &mut parts)?;
    let (register, base_offset) = parts.base?;
    let (index, stride) = parts.index?;
    Some(IndexedAddress {
        register,
        offset: (base_offset as u64).wrapping_add(parts.offset) as i64,
        index,
        stride,
    })
}

fn validate(expression: &Expr, remaining: &mut usize, depth: usize) -> Option<()> {
    if depth > MAX_DEPTH {
        return None;
    }
    *remaining = remaining.checked_sub(1)?;
    match expression {
        Expr::Const(_) | Expr::Register(_) => Some(()),
        Expr::Binary(_, left, right) => {
            validate(left, remaining, depth + 1)?;
            validate(right, remaining, depth + 1)
        }
        Expr::Load { .. } | Expr::Select { .. } => None,
    }
}

struct Parts {
    base: Option<(Reg, i64)>,
    offset: u64,
    index: Option<(Expr, u64)>,
}

fn collect(
    expression: &Expr,
    negative: bool,
    origin: &impl Fn(&Expr) -> Option<(Reg, i64)>,
    parts: &mut Parts,
) -> Option<()> {
    if let Expr::Const(value) = expression {
        parts.offset = if negative {
            parts.offset.wrapping_sub(*value)
        } else {
            parts.offset.wrapping_add(*value)
        };
        return Some(());
    }
    if let Some(base) = origin(expression) {
        if negative || parts.base.is_some() {
            return None;
        }
        parts.base = Some(base);
        return Some(());
    }
    match expression {
        Expr::Binary(BinaryOp::Add, left, right) => {
            collect(left, negative, origin, parts)?;
            collect(right, negative, origin, parts)
        }
        Expr::Binary(BinaryOp::Sub, left, right) => {
            collect(left, negative, origin, parts)?;
            collect(right, !negative, origin, parts)
        }
        _ => {
            let (index, stride, scaled) = match expression {
                Expr::Binary(BinaryOp::Mul, left, right) => match (&**left, &**right) {
                    (Expr::Const(scale), index) | (index, Expr::Const(scale)) => {
                        (index, *scale, true)
                    }
                    _ => return None,
                },
                Expr::Binary(BinaryOp::Shl, index, count) => {
                    let Expr::Const(count) = &**count else {
                        return None;
                    };
                    (&**index, 1_u64 << (count & 63), true)
                }
                _ => (expression, 1, false),
            };
            if stride == 0 || !has_register(index) {
                return None;
            }
            let stride = if negative {
                stride.wrapping_neg()
            } else {
                stride
            };
            // An identity scale is still a coefficient-one base candidate.
            if scaled && stride == 1 {
                return collect(index, false, origin, parts);
            }
            if parts.index.is_some() {
                return None;
            }
            parts.index = Some((index.clone(), stride));
            Some(())
        }
    }
}

fn has_register(expression: &Expr) -> bool {
    match expression {
        Expr::Register(_) => true,
        Expr::Binary(_, left, right) => has_register(left) || has_register(right),
        _ => false,
    }
}

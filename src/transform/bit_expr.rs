//! Borrowed, exact pure-expression idioms for C helper presentation.
//!
//! No executable IR operation or dependency is rewritten. Every candidate is
//! bounded and syntactically load-free before matching; common values require
//! identical raw subtrees. Narrow rotate and context-only truncation are outside
//! this slice. Failed/oversized matches leave the renderer's original path.

use crate::model::ir::{BinaryOp, Expr};

pub const MAX_NODES: usize = 4096;
pub const MAX_DEPTH: usize = 128;
pub const MAX_WORK: usize = 32_768;

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum BitKind {
    Rol64,
    Ror64,
    Bswap32,
    Bswap64,
}

impl BitKind {
    pub const fn helper_name(self) -> &'static str {
        match self {
            Self::Rol64 => "nirvana_rol64",
            Self::Ror64 => "nirvana_ror64",
            Self::Bswap32 => "nirvana_bswap32",
            Self::Bswap64 => "nirvana_bswap64",
        }
    }

    /// Portable C11, requiring the caller's existing <stdint.h> include.
    /// Every operand/result is uint64_t; Bswap32 swaps only the low 32 bits.
    pub const fn c_helper(self) -> &'static str {
        match self {
            Self::Rol64 => {
                r#"
static inline uint64_t nirvana_rol64(uint64_t value, uint64_t count) {
    unsigned n = (unsigned)(count & UINT64_C(63));
    return (value << n) | (value >> ((0u - n) & 63u));
}
"#
            }
            Self::Ror64 => {
                r#"
static inline uint64_t nirvana_ror64(uint64_t value, uint64_t count) {
    unsigned n = (unsigned)(count & UINT64_C(63));
    return (value >> n) | (value << ((0u - n) & 63u));
}
"#
            }
            Self::Bswap32 => {
                r#"
static inline uint64_t nirvana_bswap32(uint64_t value) {
    value &= UINT64_C(0xffffffff);
    value = ((value & UINT64_C(0x00ff00ff)) << 8) | ((value >> 8) & UINT64_C(0x00ff00ff));
    return ((value & UINT64_C(0xffff)) << 16) | (value >> 16);
}
"#
            }
            Self::Bswap64 => {
                r#"
static inline uint64_t nirvana_bswap64(uint64_t value) {
    value = ((value & UINT64_C(0x00ff00ff00ff00ff)) << 8) | ((value >> 8) & UINT64_C(0x00ff00ff00ff00ff));
    value = ((value & UINT64_C(0x0000ffff0000ffff)) << 16) | ((value >> 16) & UINT64_C(0x0000ffff0000ffff));
    return (value << 32) | (value >> 32);
}
"#
            }
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct BitView<'a> {
    pub kind: BitKind,
    pub value: &'a Expr,
    pub count: Option<&'a Expr>,
}

/// Recognize a whole expression. A renderer may call this on pure subexpressions
/// too, preserving the untouched parent operation and every memory access.
pub fn recognize(expression: &Expr) -> Option<BitView<'_>> {
    let mut matcher = Matcher { work: MAX_WORK };
    matcher.bounded_pure(expression)?;
    if let Some(value) = matcher.swap(expression, true) {
        return Some(BitView {
            kind: BitKind::Bswap64,
            value,
            count: None,
        });
    }
    if let Some(value) = matcher.swap(expression, false) {
        return Some(BitView {
            kind: BitKind::Bswap32,
            value,
            count: None,
        });
    }
    let Expr::Binary(BinaryOp::Or, a, b) = expression else {
        return None;
    };
    matcher.rotate(a, b).or_else(|| matcher.rotate(b, a))
}

struct Matcher {
    work: usize,
}
impl Matcher {
    fn spend(&mut self) -> Option<()> {
        self.work = self.work.checked_sub(1)?;
        Some(())
    }
    fn bounded_pure(&mut self, expression: &Expr) -> Option<()> {
        let mut pending = vec![(expression, 1usize)];
        let mut nodes = 0;
        while let Some((expression, depth)) = pending.pop() {
            self.spend()?;
            nodes += 1;
            if nodes > MAX_NODES || depth > MAX_DEPTH {
                return None;
            }
            match expression {
                Expr::Const(_) | Expr::Register(_) => {}
                Expr::Load { .. } => return None,
                Expr::Unary(_, value) => pending.push((value, depth + 1)),
                Expr::Binary(_, a, b) => pending.extend([(&**a, depth + 1), (&**b, depth + 1)]),
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
    fn same(&mut self, a: &Expr, b: &Expr) -> Option<()> {
        let mut pending = vec![(a, b)];
        while let Some((a, b)) = pending.pop() {
            self.spend()?;
            match (a, b) {
                (Expr::Const(a), Expr::Const(b)) if a == b => {}
                (Expr::Register(a), Expr::Register(b)) if a == b => {}
                (Expr::Unary(a, x), Expr::Unary(b, y)) if a == b => pending.push((x, y)),
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
                _ => return None,
            }
        }
        Some(())
    }
    fn complement(&mut self, count: &Expr, complement: &Expr) -> Option<()> {
        self.spend()?;
        if let (Expr::Const(a), Expr::Const(b)) = (count, complement) {
            return (a.wrapping_add(*b) & 63 == 0).then_some(());
        }
        let complement = and_mask(complement, 63).unwrap_or(complement);
        let Expr::Binary(BinaryOp::Sub, zero, value) = complement else {
            return None;
        };
        if !matches!(&**zero, Expr::Const(0)) {
            return None;
        }
        if self.same(count, value).is_some() {
            return Some(());
        }
        // IR shifts already mask their counts with 63. Presentation may have
        // removed that mask on the primary shift but kept it under negation.
        // Compare only the identical raw count below these exact wrappers.
        self.same(
            and_mask(count, 63).unwrap_or(count),
            and_mask(value, 63).unwrap_or(value),
        )
    }
    fn rotate<'a>(&mut self, first: &'a Expr, second: &'a Expr) -> Option<BitView<'a>> {
        self.spend()?;
        let Expr::Binary(op @ (BinaryOp::Shl | BinaryOp::Shr), value, count) = first else {
            return None;
        };
        let Expr::Binary(other, other_value, complement) = second else {
            return None;
        };
        if !matches!(
            (op, other),
            (BinaryOp::Shl, BinaryOp::Shr) | (BinaryOp::Shr, BinaryOp::Shl)
        ) {
            return None;
        }
        self.same(value, other_value)?;
        self.complement(count, complement)?;
        Some(BitView {
            kind: if *op == BinaryOp::Shl {
                BitKind::Rol64
            } else {
                BitKind::Ror64
            },
            value,
            count: Some(count),
        })
    }
    fn stage<'a>(
        &mut self,
        expression: &'a Expr,
        count: u64,
        mask: u64,
        bare_right: bool,
        input_mask: bool,
    ) -> Option<&'a Expr> {
        self.spend()?;
        let Expr::Binary(BinaryOp::Or, a, b) = expression else {
            return None;
        };
        for (a, b) in [(&**a, &**b), (&**b, &**a)] {
            let Some(left) = shift(a, BinaryOp::Shl, count) else {
                continue;
            };
            let Some(value) = and_mask(left, mask) else {
                continue;
            };
            let right = match and_mask(b, mask) {
                Some(right) => right,
                None if bare_right => b,
                None => continue,
            };
            let Some(other) = shift(right, BinaryOp::Shr, count) else {
                continue;
            };
            if self.same(value, other).is_some() {
                return Some(value);
            }
            // In the 32-bit first stage, this explicit input mask on the
            // right is redundant under the following 00ff00ff mask. The raw
            // common subtree inside that exact wrapper must still be equal.
            if input_mask
                && let Some(other) = and_mask(other, 0xffff_ffff)
                && self.same(value, other).is_some()
            {
                return Some(value);
            }
        }
        None
    }
    fn swap<'a>(&mut self, expression: &'a Expr, wide: bool) -> Option<&'a Expr> {
        let expression = if wide {
            self.stage(expression, 32, 0xffff_ffff, true, false)?
        } else {
            expression
        };
        let expression = self.stage(
            expression,
            16,
            if wide { 0x0000_ffff_0000_ffff } else { 0xffff },
            !wide,
            false,
        )?;
        self.stage(
            expression,
            8,
            if wide {
                0x00ff_00ff_00ff_00ff
            } else {
                0x00ff_00ff
            },
            false,
            !wide,
        )
    }
}
fn and_mask(expression: &Expr, mask: u64) -> Option<&Expr> {
    let Expr::Binary(BinaryOp::And, a, b) = expression else {
        return None;
    };
    match (&**a, &**b) {
        (Expr::Const(value), base) | (base, Expr::Const(value)) if *value == mask => Some(base),
        _ => None,
    }
}
fn shift(expression: &Expr, operator: BinaryOp, count: u64) -> Option<&Expr> {
    let Expr::Binary(op, value, amount) = expression else {
        return None;
    };
    (*op == operator && matches!(&**amount, Expr::Const(value) if *value == count))
        .then_some(&**value)
}

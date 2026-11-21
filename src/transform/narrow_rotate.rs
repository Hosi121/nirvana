//! Exact, borrowed narrow rotates for C presentation, independent of C storage.
//!
//! Both data shifts need an explicit width mask and the complete result needs
//! the same mask. No input-width fact, source identity, or truncated assignment
//! context is assumed. A successful view equals the whole original u64 value.
//! Loads anywhere (including lazy arms) and exhausted budgets decline the view.

use crate::model::ir::{BinaryOp, Expr};

pub const MAX_NODES: usize = 4096;
pub const MAX_DEPTH: usize = 128;
pub const MAX_WORK: usize = 32_768;

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum NarrowWidth {
    U8,
    U16,
    U32,
}
impl NarrowWidth {
    pub const fn bits(self) -> u32 {
        match self {
            Self::U8 => 8,
            Self::U16 => 16,
            Self::U32 => 32,
        }
    }
    pub const fn mask(self) -> u64 {
        u64::MAX >> (64 - self.bits())
    }
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Direction {
    Left,
    Right,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct NarrowRotate<'a> {
    pub width: NarrowWidth,
    pub direction: Direction,
    pub value: &'a Expr,
    /// The original primary count, either a literal below width or explicitly
    /// masked by width - 1. The helper masks it again, including zero counts.
    pub count: &'a Expr,
}

impl NarrowRotate<'_> {
    pub const fn helper_name(self) -> &'static str {
        match (self.width, self.direction) {
            (NarrowWidth::U8, Direction::Left) => "nirvana_rol8",
            (NarrowWidth::U8, Direction::Right) => "nirvana_ror8",
            (NarrowWidth::U16, Direction::Left) => "nirvana_rol16",
            (NarrowWidth::U16, Direction::Right) => "nirvana_ror16",
            (NarrowWidth::U32, Direction::Left) => "nirvana_rol32",
            (NarrowWidth::U32, Direction::Right) => "nirvana_ror32",
        }
    }

    /// Portable C11, requiring <stdint.h>. All shifts use uint64_t and a count
    /// below 32. The explicit result mask is part of the whole-u64 contract.
    pub const fn c_helper(self) -> &'static str {
        match (self.width, self.direction) {
            (NarrowWidth::U8, Direction::Left) => {
                r#"
static inline uint64_t nirvana_rol8(uint64_t value, uint64_t count) {
    unsigned n = (unsigned)(count & UINT64_C(7));
    value &= UINT64_C(0xff);
    return ((value << n) | (value >> ((0u - n) & 7u))) & UINT64_C(0xff);
}
"#
            }
            (NarrowWidth::U8, Direction::Right) => {
                r#"
static inline uint64_t nirvana_ror8(uint64_t value, uint64_t count) {
    unsigned n = (unsigned)(count & UINT64_C(7));
    value &= UINT64_C(0xff);
    return ((value >> n) | (value << ((0u - n) & 7u))) & UINT64_C(0xff);
}
"#
            }
            (NarrowWidth::U16, Direction::Left) => {
                r#"
static inline uint64_t nirvana_rol16(uint64_t value, uint64_t count) {
    unsigned n = (unsigned)(count & UINT64_C(15));
    value &= UINT64_C(0xffff);
    return ((value << n) | (value >> ((0u - n) & 15u))) & UINT64_C(0xffff);
}
"#
            }
            (NarrowWidth::U16, Direction::Right) => {
                r#"
static inline uint64_t nirvana_ror16(uint64_t value, uint64_t count) {
    unsigned n = (unsigned)(count & UINT64_C(15));
    value &= UINT64_C(0xffff);
    return ((value >> n) | (value << ((0u - n) & 15u))) & UINT64_C(0xffff);
}
"#
            }
            (NarrowWidth::U32, Direction::Left) => {
                r#"
static inline uint64_t nirvana_rol32(uint64_t value, uint64_t count) {
    unsigned n = (unsigned)(count & UINT64_C(31));
    value &= UINT64_C(0xffffffff);
    return ((value << n) | (value >> ((0u - n) & 31u))) & UINT64_C(0xffffffff);
}
"#
            }
            (NarrowWidth::U32, Direction::Right) => {
                r#"
static inline uint64_t nirvana_ror32(uint64_t value, uint64_t count) {
    unsigned n = (unsigned)(count & UINT64_C(31));
    value &= UINT64_C(0xffffffff);
    return ((value >> n) | (value << ((0u - n) & 31u))) & UINT64_C(0xffffffff);
}
"#
            }
        }
    }
}

pub fn recognize_masked(expression: &Expr) -> Option<NarrowRotate<'_>> {
    let mut matcher = Matcher { work: MAX_WORK };
    matcher.bounded_pure(expression)?;
    for width in [NarrowWidth::U8, NarrowWidth::U16, NarrowWidth::U32] {
        if let Some(body) = and_mask(expression, width.mask()) {
            if let Some(view) = matcher.rotate(body, width) {
                return Some(view);
            }
            if let Expr::Binary(
                BinaryOp::Insert {
                    start: 0,
                    width: field,
                },
                base,
                value,
            ) = body
                && field.bits() >= width.bits()
                && let Some(view) =
                    matcher.rotate(and_mask(value, width.mask()).unwrap_or(value), width)
                && matcher.same(base, view.value).is_some()
            {
                return Some(view);
            }
            // x86 partial-register writes may preserve high bits immediately
            // before this outer mask. Require the same raw base, so removing
            // that dead high term cannot drop an unrelated register dependency.
            if let Expr::Binary(BinaryOp::Or, a, b) = body {
                for (high, low) in [(&**a, &**b), (&**b, &**a)] {
                    if let Some(high) = and_mask(high, !width.mask())
                        && let Some(low) = and_mask(low, width.mask())
                        && let Some(view) = matcher.rotate(low, width)
                        && matcher.same(high, view.value).is_some()
                    {
                        return Some(view);
                    }
                }
            }
        }
    }
    None
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
    fn complement(&mut self, primary: &Expr, other: &Expr, width: NarrowWidth) -> Option<()> {
        self.spend()?;
        let bits = u64::from(width.bits());
        let mask = bits - 1;
        if let Expr::Const(n) = primary {
            return (*n < bits
                && matches!(other, Expr::Const(k) if *k == bits - n || (*n == 0 && *k == 0)))
            .then_some(());
        }
        let base = and_mask(primary, mask)?;
        if let Some(other) = and_mask(other, mask) {
            let Expr::Binary(BinaryOp::Sub, from, value) = other else {
                return None;
            };
            if !matches!(&**from, Expr::Const(n) if *n == 0 || *n == bits) {
                return None;
            }
            if self.same(primary, value).is_some() {
                return Some(());
            }
            return self.same(base, value);
        }
        // Width - masked_count is also exact; at count zero its shift is width,
        // which is legal in u64 and disappears under the explicit output mask.
        let Expr::Binary(BinaryOp::Sub, from, value) = other else {
            return None;
        };
        if !matches!(&**from, Expr::Const(n) if *n == bits) {
            return None;
        }
        self.same(primary, value)
    }
    fn rotate<'a>(&mut self, body: &'a Expr, width: NarrowWidth) -> Option<NarrowRotate<'a>> {
        self.spend()?;
        let Expr::Binary(BinaryOp::Or, a, b) = body else {
            return None;
        };
        for (first, second) in [(&**a, &**b), (&**b, &**a)] {
            let Expr::Binary(op @ (BinaryOp::Shl | BinaryOp::Shr), value, count) = first else {
                continue;
            };
            let Expr::Binary(other, other_value, complement) = second else {
                continue;
            };
            if !matches!(
                (op, other),
                (BinaryOp::Shl, BinaryOp::Shr) | (BinaryOp::Shr, BinaryOp::Shl)
            ) {
                continue;
            }
            if let Some(value) = and_mask(value, width.mask())
                && let Some(other_value) = and_mask(other_value, width.mask())
                && self.same(value, other_value).is_some()
                && self.complement(count, complement, width).is_some()
            {
                return Some(NarrowRotate {
                    width,
                    direction: if *op == BinaryOp::Shl {
                        Direction::Left
                    } else {
                        Direction::Right
                    },
                    value,
                    count,
                });
            }
        }
        None
    }
}

fn and_mask(expression: &Expr, mask: u64) -> Option<&Expr> {
    if let Expr::Unary(crate::model::ir::UnaryOp::Extract { start: 0, width }, base) = expression
        && width.mask() == mask
    {
        return Some(base);
    }
    let Expr::Binary(BinaryOp::And, a, b) = expression else {
        return None;
    };
    match (&**a, &**b) {
        (Expr::Const(value), base) | (base, Expr::Const(value)) if *value == mask => Some(base),
        _ => None,
    }
}

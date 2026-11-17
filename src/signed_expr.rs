//! Exact, borrowed signed-order views of pure 64-bit subtraction flags.
//!
//! The helper compares unsigned bit patterns with their sign bit biased. No C
//! signed conversion, source signed type, or producer relation is assumed. A
//! separately materialized subtraction result is deliberately not recognized.

use crate::ir::{BinaryOp, Expr};

pub const MAX_NODES: usize = 4096;
pub const MAX_DEPTH: usize = 128;
pub const MAX_WORK: usize = 32_768;
const SIGN: u64 = 1 << 63;

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum SignedKind {
    Slt64,
    Sle64,
}

impl SignedKind {
    pub const fn helper_name(self) -> &'static str {
        match self {
            Self::Slt64 => "nirvana_slt64",
            Self::Sle64 => "nirvana_sle64",
        }
    }

    /// Portable C11, requiring <stdint.h>. Inputs are arbitrary u64 bit
    /// patterns, and the uint64_t result is exactly zero or one.
    pub const fn c_helper(self) -> &'static str {
        match self {
            Self::Slt64 => {
                r#"
static inline uint64_t nirvana_slt64(uint64_t left, uint64_t right) {
    return (left ^ UINT64_C(0x8000000000000000)) < (right ^ UINT64_C(0x8000000000000000));
}
"#
            }
            Self::Sle64 => {
                r#"
static inline uint64_t nirvana_sle64(uint64_t left, uint64_t right) {
    return (left ^ UINT64_C(0x8000000000000000)) <= (right ^ UINT64_C(0x8000000000000000));
}
"#
            }
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SignedView<'a> {
    pub kind: SignedKind,
    pub left: &'a Expr,
    pub right: &'a Expr,
}

/// Match SF^OF, or ZF|(SF^OF), for the same explicit raw `left-right` u64
/// subtraction. SF uses bit 63, OF the exact 64-bit sign mask, and ZF exact
/// operand equality (or equality of the same subtraction with zero).
///
/// All loads, including lazy unselected arms, are rejected before matching.
/// Operands must be identical raw subtrees; storage names and previous writes
/// do not establish equality. No expression or register dependency is rewritten.
pub fn recognize(expression: &Expr) -> Option<SignedView<'_>> {
    let mut matcher = Matcher { work: MAX_WORK };
    matcher.bounded_pure(expression)?;
    if let Some((left, right)) = matcher.less(expression) {
        return Some(SignedView {
            kind: SignedKind::Slt64,
            left,
            right,
        });
    }
    let (a, b) = binary(expression, BinaryOp::Or)?;
    for (zero, less) in [(a, b), (b, a)] {
        if let Some((left, right)) = matcher.less(less)
            && matcher.zero_equal(zero, left, right).is_some()
        {
            return Some(SignedView {
                kind: SignedKind::Sle64,
                left,
                right,
            });
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
        let mut count = 0;
        while let Some((expression, depth)) = pending.pop() {
            self.spend()?;
            count += 1;
            if count > MAX_NODES || depth > MAX_DEPTH {
                return None;
            }
            match expression {
                Expr::Const(_) | Expr::Register(_) => {}
                Expr::Load { .. } => return None,
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
                (Expr::Binary(a, al, ar), Expr::Binary(b, bl, br)) if a == b => {
                    pending.extend([(&**al, &**bl), (&**ar, &**br)]);
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

    fn xor_equal(&mut self, expression: &Expr, a: &Expr, b: &Expr) -> Option<()> {
        self.spend()?;
        let (left, right) = binary(expression, BinaryOp::Xor)?;
        if self.same(left, a).is_some() && self.same(right, b).is_some() {
            return Some(());
        }
        self.same(left, b)?;
        self.same(right, a)
    }

    fn less<'a>(&mut self, expression: &'a Expr) -> Option<(&'a Expr, &'a Expr)> {
        self.spend()?;
        let (a, b) = binary(expression, BinaryOp::Xor)?;
        self.flags(a, b).or_else(|| self.flags(b, a))
    }

    fn flags<'a>(&mut self, sign: &'a Expr, overflow: &Expr) -> Option<(&'a Expr, &'a Expr)> {
        self.spend()?;
        let (result, count) = binary(sign, BinaryOp::Shr)?;
        if !constant(count, 63) {
            return None;
        }
        let (left, right) = binary(result, BinaryOp::Sub)?;
        let (a, b) = binary(overflow, BinaryOp::Ne)?;
        let bits = if constant(b, 0) {
            a
        } else if constant(a, 0) {
            b
        } else {
            return None;
        };
        let (a, b) = binary(bits, BinaryOp::And)?;
        let pair = if constant(b, SIGN) {
            a
        } else if constant(a, SIGN) {
            b
        } else {
            return None;
        };
        let (a, b) = binary(pair, BinaryOp::And)?;
        for (signs, difference) in [(a, b), (b, a)] {
            if self.xor_equal(signs, left, right).is_some()
                && self.xor_equal(difference, left, result).is_some()
            {
                return Some((left, right));
            }
        }
        None
    }

    fn zero_equal(&mut self, expression: &Expr, left: &Expr, right: &Expr) -> Option<()> {
        self.spend()?;
        let (a, b) = binary(expression, BinaryOp::Eq)?;
        if self.same(a, left).is_some() && self.same(b, right).is_some()
            || self.same(a, right).is_some() && self.same(b, left).is_some()
        {
            return Some(());
        }
        let result = if constant(b, 0) {
            a
        } else if constant(a, 0) {
            b
        } else {
            return None;
        };
        let (a, b) = binary(result, BinaryOp::Sub)?;
        self.same(a, left)?;
        self.same(b, right)
    }
}

fn binary(expression: &Expr, operator: BinaryOp) -> Option<(&Expr, &Expr)> {
    let Expr::Binary(op, a, b) = expression else {
        return None;
    };
    (*op == operator).then_some((a, b))
}

fn constant(expression: &Expr, number: u64) -> bool {
    matches!(expression, Expr::Const(value) if *value == number)
}

//! Unsigned interval operators shared by independent checkers, not inference.
//! Inputs and outputs are in [0, 2^64-1]; u128 keeps products and shifts exact
//! before a conservative cap accounts for the IR's wrapping arithmetic.
use crate::model::ir::{BinaryOp, UnaryOp, Width};

pub(crate) const WORD_MAX: u128 = (1u128 << 64) - 1;
const SIGN_BIT: u128 = 1u128 << 63;

pub(crate) fn from_bits(bits: u8) -> Option<u128> {
    (bits <= 64).then(|| (1u128 << bits) - 1)
}

pub(crate) fn width(width: Width) -> u32 {
    match width {
        Width::U8 => 8,
        Width::U16 => 16,
        Width::U32 => 32,
        Width::U64 => 64,
    }
}

pub(crate) fn load(w: Width) -> u128 {
    (1u128 << width(w)) - 1
}

/// Every possible bit in [0, upper], including bits absent from upper itself.
pub(crate) fn hull(upper: u128) -> u128 {
    (upper + 1).next_power_of_two() - 1
}

pub(crate) fn unary(operation: UnaryOp, value: u128) -> u128 {
    match operation {
        UnaryOp::SignExtend(w) => {
            if value < (1u128 << (width(w) - 1)) {
                value
            } else {
                WORD_MAX
            }
        }
        UnaryOp::Extract { start, width } => {
            if start >= 64 {
                0
            } else {
                (value >> start).min(load(width))
            }
        }
    }
}

/// literal must come directly from the source RHS, not inferred metadata.
pub(crate) fn binary(operation: BinaryOp, a: u128, b: u128, literal: Option<u64>) -> u128 {
    match operation {
        BinaryOp::Add => (a + b).min(WORD_MAX),
        BinaryOp::Sub => {
            if b == 0 {
                a
            } else {
                WORD_MAX
            }
        }
        BinaryOp::Mul => (a * b).min(WORD_MAX),
        BinaryOp::And => a.min(b),
        BinaryOp::Or | BinaryOp::Xor => hull(a) | hull(b),
        BinaryOp::Shl => match literal {
            Some(count) => (a << (count & 63)).min(WORD_MAX),
            None if b == 0 => a,
            None if a == 0 => 0,
            None => WORD_MAX,
        },
        BinaryOp::AShr if a >= SIGN_BIT => WORD_MAX,
        BinaryOp::Shr | BinaryOp::AShr => match literal {
            Some(count) => a >> (count & 63),
            None => a,
        },
        BinaryOp::UMulHigh => (a * b) >> 64,
        BinaryOp::SMulHigh => WORD_MAX,
        BinaryOp::UDiv => match literal {
            Some(divisor) if divisor != 0 => a / u128::from(divisor),
            _ => WORD_MAX,
        },
        BinaryOp::URem => a,
        // Negative remainders can have a larger unsigned pattern than a.
        BinaryOp::SRem => {
            if a < SIGN_BIT {
                a
            } else {
                WORD_MAX
            }
        }
        BinaryOp::SDiv => WORD_MAX,
        BinaryOp::Eq | BinaryOp::Ne | BinaryOp::Ult | BinaryOp::Ule => 1,
        BinaryOp::Insert { start, width } => {
            if start >= 64 {
                a
            } else {
                let field = (load(width) << start) & WORD_MAX;
                (hull(a) & (WORD_MAX ^ field)) | ((hull(b) << start) & field)
            }
        }
    }
}

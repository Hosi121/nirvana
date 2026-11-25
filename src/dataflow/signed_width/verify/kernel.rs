//! A signed-i128 interpretation of raw 64-bit values, independent of inference.
//! Intervals describe the two's-complement decoding of a complete word. Exact
//! operations use wider integers, rather than the executable IR evaluators.

use crate::model::ir::{BinaryOp as B, UnaryOp as U, Width};

const WORD: u128 = 1u128 << 64;
const MASK: u128 = WORD - 1;
const MIN: i128 = -(1i128 << 63);
const MAX: i128 = (1i128 << 63) - 1;

pub(super) fn bits(width: Width) -> u32 {
    match width {
        Width::U8 => 8,
        Width::U16 => 16,
        Width::U32 => 32,
        Width::U64 => 64,
    }
}

fn word(value: i128) -> u64 {
    (value & MASK as i128) as u64
}

fn signed(value: u64) -> i128 {
    if u128::from(value) < WORD / 2 {
        i128::from(value)
    } else {
        i128::from(value) - WORD as i128
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct Range {
    pub lo: i128,
    pub hi: i128,
}

impl Range {
    pub const FULL: Self = Self { lo: MIN, hi: MAX };

    pub fn exact(value: u64) -> Self {
        let value = signed(value);
        Self {
            lo: value,
            hi: value,
        }
    }

    pub fn storage(width: Width) -> Self {
        let limit = 1i128 << (bits(width) - 1);
        Self {
            lo: -limit,
            hi: limit - 1,
        }
    }

    pub fn contains(self, other: Self) -> bool {
        self.lo <= other.lo && other.hi <= self.hi
    }

    pub fn constant(self) -> Option<u64> {
        (self.lo == self.hi).then(|| word(self.lo))
    }

    pub fn union(self, other: Self) -> Self {
        Self {
            lo: self.lo.min(other.lo),
            hi: self.hi.max(other.hi),
        }
    }
}

pub(super) fn constant_unary(op: U, value: u64) -> u64 {
    let value = u128::from(value);
    match op {
        U::SignExtend(width) => {
            let size = bits(width);
            let low = value & ((1u128 << size) - 1);
            if low & (1u128 << (size - 1)) == 0 {
                low as u64
            } else {
                word(low as i128 - (1i128 << size))
            }
        }
        U::Extract { start, width } => {
            if start >= 64 {
                0
            } else {
                ((value >> start) & ((1u128 << bits(width)) - 1)) as u64
            }
        }
    }
}

pub(super) fn constant_binary(op: B, a: u64, b: u64) -> u64 {
    let (x, y) = (u128::from(a), u128::from(b));
    let count = (y % 64) as u32;
    let value = match op {
        B::Add => (x + y) & MASK,
        B::Sub => (x + WORD - y) & MASK,
        B::Mul => (x * y) & MASK,
        B::And => x & y,
        B::Or => x | y,
        B::Xor => x ^ y,
        B::Shl => (x << count) & MASK,
        B::Shr => x >> count,
        B::AShr => return word(signed(a) >> count),
        B::Eq => u128::from(x == y),
        B::Ne => u128::from(x != y),
        B::Ult => u128::from(x < y),
        B::Ule => u128::from(x <= y),
        B::UMulHigh => (x * y) >> 64,
        B::SMulHigh => return word((signed(a) * signed(b)) >> 64),
        B::UDiv => x.checked_div(y).unwrap_or(MASK),
        B::URem => x.checked_rem(y).unwrap_or(x),
        B::SDiv => {
            if y == 0 {
                if signed(a) < 0 { 1 } else { MASK }
            } else {
                return word(signed(a) / signed(b));
            }
        }
        B::SRem => {
            if y == 0 {
                x
            } else {
                return word(signed(a) % signed(b));
            }
        }
        B::Insert { start, width } => {
            if start >= 64 {
                x
            } else {
                let field = (((1u128 << bits(width)) - 1) << start) & MASK;
                (x & (MASK ^ field)) | ((y << start) & field)
            }
        }
    };
    value as u64
}

pub(super) fn unary(op: U, value: Range) -> Range {
    if let Some(value) = value.constant() {
        return Range::exact(constant_unary(op, value));
    }
    match op {
        U::SignExtend(width) => {
            let result = Range::storage(width);
            if result.contains(value) {
                value
            } else {
                result
            }
        }
        U::Extract { start, .. } if start >= 64 => Range::exact(0),
        U::Extract {
            start: 0,
            width: Width::U64,
        } => value,
        U::Extract { start, width } => {
            let count = bits(width).min(64 - u32::from(start));
            // The identity64 case above is the only extraction which can
            // retain a sign bit. Every other result is a nonnegative integer.
            Range {
                lo: 0,
                hi: (1i128 << count) - 1,
            }
        }
    }
}

pub(super) fn load(width: Width) -> Range {
    if width == Width::U64 {
        Range::FULL
    } else {
        Range {
            lo: 0,
            hi: (1i128 << bits(width)) - 1,
        }
    }
}

/// Bit operations preserve a common sign prefix. Compute its signed numeric
/// envelope from endpoints rather than the producer's width-state lattice.
fn bit_envelope(a: Range, b: Range) -> Range {
    let negative = (-a.lo.min(0)).max(-b.lo.min(0)) as u128;
    let positive = (a.hi.max(0) + 1).max(b.hi.max(0) + 1) as u128;
    let extent = negative.max(positive).next_power_of_two() as i128;
    Range {
        lo: -extent,
        hi: extent - 1,
    }
}

pub(super) fn binary(op: B, a: Range, b: Range) -> Range {
    if let (Some(a), Some(b)) = (a.constant(), b.constant()) {
        return Range::exact(constant_binary(op, a, b));
    }
    match op {
        B::And | B::Or | B::Xor => bit_envelope(a, b),
        B::Eq | B::Ne | B::Ult | B::Ule => Range { lo: 0, hi: 1 },
        B::AShr => {
            if let Some(count) = b.constant() {
                let count = count % 64;
                Range {
                    lo: a.lo >> count,
                    hi: a.hi >> count,
                }
            } else {
                Range {
                    lo: a.lo.min(a.lo >> 63),
                    hi: a.hi.max(a.hi >> 63),
                }
            }
        }
        B::SDiv | B::SRem => {
            let Some(divisor) = b.constant().map(signed) else {
                return Range::FULL;
            };
            if divisor == 0 {
                return if op == B::SRem {
                    a
                } else if a.hi < 0 {
                    Range::exact(1)
                } else if a.lo >= 0 {
                    Range::exact(u64::MAX)
                } else {
                    Range { lo: -1, hi: 1 }
                };
            }
            if op == B::SDiv {
                if divisor == -1 && a.lo == MIN {
                    return Range::FULL;
                }
                let (p, q) = (a.lo / divisor, a.hi / divisor);
                Range {
                    lo: p.min(q),
                    hi: p.max(q),
                }
            } else {
                let magnitude = divisor.abs() - 1;
                Range {
                    lo: a.lo.min(0).max(-magnitude),
                    hi: a.hi.max(0).min(magnitude),
                }
            }
        }
        _ => Range::FULL,
    }
}

pub(super) fn select(condition: Range, taken: Range, not_taken: Range) -> Range {
    match condition.constant() {
        Some(0) => not_taken,
        Some(_) => taken,
        None => taken.union(not_taken),
    }
}

#[cfg(test)]
mod tests;

//! Numeric proof rules, separate from the producer's transfer implementation.
//! A bit cube's lower-prefix extrema determine each arithmetic carry/borrow;
//! bit projections instead map the cube's two mask endpoints directly.
use super::super::KnownBits;
use crate::model::ir::{BinaryOp as B, UnaryOp};

const WORD: u128 = 1u128 << 64;

fn low(bits: u32) -> u64 {
    ((1u128 << bits.min(64)) - 1) as u64
}

fn signed(word: u64) -> i128 {
    i128::from(word)
        - if word & (1 << 63) != 0 {
            WORD as i128
        } else {
            0
        }
}

fn insert(left: u64, right: u64, start: u8, bits: u32) -> u64 {
    if start >= 64 {
        return left;
    }
    let count = bits.min(64 - u32::from(start));
    let field = low(count) << start;
    (left & !field) | ((right & low(count)) << start)
}

fn shift(op: B, word: u64, count: u64) -> u64 {
    let count = (count & 63) as u32;
    match op {
        B::Shl => (u128::from(word) << count) as u64,
        B::Shr => (u128::from(word) >> count) as u64,
        B::AShr => (signed(word) >> count) as u64,
        _ => unreachable!(),
    }
}

fn unary_word(op: UnaryOp, word: u64) -> u64 {
    match op {
        UnaryOp::Extract { start, width } => {
            if start >= 64 {
                0
            } else {
                ((u128::from(word) >> u32::from(start)) & u128::from(low(width.bits()))) as u64
            }
        }
        UnaryOp::SignExtend(width) => {
            let bits = width.bits();
            let value = word & low(bits);
            if value & (1 << (bits - 1)) == 0 {
                value
            } else {
                value | !low(bits)
            }
        }
    }
}

// Own total word arithmetic, including signed interpretations and zero divisors.
// No IR evaluator or producer rule participates in runtime checking.
fn binary_word(op: B, left: u64, right: u64) -> u64 {
    let a = u128::from(left);
    let b = u128::from(right);
    match op {
        B::Add => (a + b) as u64,
        B::Sub => (WORD + a - b) as u64,
        B::Mul => (a * b) as u64,
        B::UMulHigh => ((a * b) >> 64) as u64,
        B::SMulHigh => ((signed(left) * signed(right)) >> 64) as u64,
        B::And => left & right,
        B::Or => left | right,
        B::Xor => left ^ right,
        B::Shl | B::Shr | B::AShr => shift(op, left, right),
        B::Eq => u64::from(a == b),
        B::Ne => u64::from(a != b),
        B::Ult => u64::from(a < b),
        B::Ule => u64::from(a <= b),
        B::UDiv => a.checked_div(b).unwrap_or(WORD - 1) as u64,
        B::URem => a.checked_rem(b).unwrap_or(a) as u64,
        B::SDiv if b == 0 => {
            if signed(left) < 0 {
                1
            } else {
                u64::MAX
            }
        }
        B::SDiv => (signed(left) / signed(right)) as u64,
        B::SRem if b == 0 => left,
        B::SRem => (signed(left) % signed(right)) as u64,
        B::Insert { start, width } => insert(left, right, start, width.bits()),
    }
}

pub(super) fn unary(op: UnaryOp, value: KnownBits) -> KnownBits {
    // Both unary operators copy input bits or supply zero bits. Applying that
    // projection to the cube endpoints also accounts for repeated sign bits.
    KnownBits {
        zero: !unary_word(op, !value.zero),
        one: unary_word(op, value.one),
    }
}

fn interval(lo: u64, hi: u64) -> KnownBits {
    debug_assert!(lo <= hi);
    let free = low(64 - (lo ^ hi).leading_zeros());
    KnownBits {
        zero: !(hi | free),
        one: lo & !free,
    }
}

fn sign(value: KnownBits) -> Option<bool> {
    if value.zero & (1 << 63) != 0 {
        Some(false)
    } else if value.one & (1 << 63) != 0 {
        Some(true)
    } else {
        None
    }
}

fn boolean(value: Option<bool>) -> KnownBits {
    value.map_or(KnownBits { zero: !1, one: 0 }, |v| {
        KnownBits::constant(u64::from(v))
    })
}

fn arithmetic(left: KnownBits, right: KnownBits, subtract: bool) -> KnownBits {
    if left == KnownBits::UNKNOWN || right == KnownBits::UNKNOWN {
        return KnownBits::UNKNOWN;
    }
    let mut result = KnownBits::UNKNOWN;
    let fixed = (left.zero | left.one) & (right.zero | right.one);
    for bit in 0..64 {
        let place = 1u64 << bit;
        if fixed & place == 0 {
            continue;
        }
        let prefix = u128::from(low(bit));
        let (amin, amax) = (
            u128::from(left.one) & prefix,
            u128::from(!left.zero) & prefix,
        );
        let (bmin, bmax) = (
            u128::from(right.one) & prefix,
            u128::from(!right.zero) & prefix,
        );
        let incoming = if subtract {
            // A borrow is possible exactly when some lower prefix A < B.
            if amax < bmin {
                Some(true)
            } else if amin >= bmax {
                Some(false)
            } else {
                None
            }
        } else {
            let boundary = 1u128 << bit;
            if amin + bmin >= boundary {
                Some(true)
            } else if amax + bmax < boundary {
                Some(false)
            } else {
                None
            }
        };
        if let Some(incoming) = incoming {
            if ((left.one ^ right.one) & place != 0) ^ incoming {
                result.one |= place;
            } else {
                result.zero |= place;
            }
        }
    }
    result
}

fn shift_cube(op: B, value: KnownBits, counts: KnownBits) -> KnownBits {
    if let Some(count) = counts.number() {
        return fixed_shift(op, value, (count & 63) as u32);
    }
    let mut result: Option<KnownBits> = None;
    // Only the low six count bits are observed, even if upper bits are known.
    for count in 0..64u64 {
        if (count & counts.zero & 63) != 0 || (count & counts.one & 63) != counts.one & 63 {
            continue;
        }
        let next = KnownBits {
            zero: !shift(op, !value.zero, count),
            one: shift(op, value.one, count),
        };
        result = Some(result.map_or(next, |old| old.join(next)));
    }
    result.unwrap_or(KnownBits::UNKNOWN)
}

fn fixed_shift(op: B, value: KnownBits, count: u32) -> KnownBits {
    KnownBits {
        zero: !shift(op, !value.zero, u64::from(count)),
        one: shift(op, value.one, u64::from(count)),
    }
}

fn product(left: KnownBits, right: KnownBits, high: bool) -> KnownBits {
    let max = u128::from(left.maximum()) * u128::from(right.maximum());
    // Keep the producer's upper-bound precision. Extra lower-bound facts can
    // make later generic operations consume more work than the producer did.
    if high {
        return interval(0, (max >> 64) as u64);
    }
    if left.number() == Some(0) || right.number() == Some(0) {
        return KnownBits::constant(0);
    }
    for (factor, value) in [(left, right), (right, left)] {
        if let Some(n) = factor.number()
            && n.count_ones() == 1
        {
            return fixed_shift(B::Shl, value, n.trailing_zeros());
        }
    }
    let trailing = low(left.zero.trailing_ones() + right.zero.trailing_ones());
    let bound = if max < WORD {
        interval(0, max as u64)
    } else {
        KnownBits::UNKNOWN
    };
    KnownBits {
        zero: trailing | bound.zero,
        one: bound.one,
    }
}

fn quotient(left: KnownBits, right: KnownBits) -> KnownBits {
    match right.number() {
        Some(0) => return KnownBits::constant(u64::MAX),
        Some(n) if n.count_ones() == 1 => return fixed_shift(B::Shr, left, n.trailing_zeros()),
        _ => {}
    }
    if right.minimum() == 0 {
        KnownBits::UNKNOWN
    } else {
        interval(0, left.maximum() / right.minimum())
    }
}

fn residue(left: KnownBits, right: KnownBits, maximum: u64) -> KnownBits {
    let preserved = low(right.zero.trailing_ones());
    KnownBits {
        zero: interval(0, maximum).zero | (left.zero & preserved),
        one: left.one & preserved,
    }
}

fn remainder(left: KnownBits, right: KnownBits) -> KnownBits {
    match right.number() {
        Some(0) => return left,
        Some(n) if n.count_ones() == 1 => {
            return KnownBits {
                zero: left.zero | !(n - 1),
                one: left.one & (n - 1),
            };
        }
        _ => {}
    }
    if right.minimum() > left.maximum() {
        return left;
    }
    let max = if right.minimum() == 0 {
        left.maximum()
    } else {
        left.maximum().min(right.maximum() - 1)
    };
    residue(left, right, max)
}

fn signed_quotient(left: KnownBits, right: KnownBits) -> KnownBits {
    match right.number() {
        Some(0) => {
            return match sign(left) {
                Some(negative) => KnownBits::constant(if negative { 1 } else { u64::MAX }),
                None => KnownBits { zero: 0, one: 1 },
            };
        }
        Some(1) => return left,
        Some(u64::MAX) => return arithmetic(KnownBits::constant(0), left, true),
        _ => {}
    }
    if sign(left) == Some(false) && sign(right) == Some(false) {
        quotient(left, right)
    } else {
        KnownBits::UNKNOWN
    }
}

fn signed_remainder(left: KnownBits, right: KnownBits) -> KnownBits {
    match right.number() {
        Some(0) => return left,
        Some(1 | u64::MAX) => return KnownBits::constant(0),
        Some(n) => {
            let signed_divisor = signed(n);
            let magnitude = if signed_divisor < 0 {
                -signed_divisor
            } else {
                signed_divisor
            } as u64;
            if sign(left) == Some(false) {
                return remainder(left, KnownBits::constant(magnitude));
            }
            if magnitude.count_ones() == 1 && left.zero & (magnitude - 1) == magnitude - 1 {
                return KnownBits::constant(0);
            }
        }
        None => {}
    }
    residue(
        left,
        right,
        if sign(left) == Some(false) {
            left.maximum()
        } else {
            u64::MAX
        },
    )
}

pub(super) fn binary(op: B, left: KnownBits, right: KnownBits) -> KnownBits {
    if let (Some(a), Some(b)) = (left.number(), right.number()) {
        return KnownBits::constant(binary_word(op, a, b));
    }
    match op {
        B::Insert { start, width } => KnownBits {
            zero: !insert(!left.zero, !right.zero, start, width.bits()),
            one: insert(left.one, right.one, start, width.bits()),
        },
        B::And => KnownBits {
            zero: left.zero | right.zero,
            one: left.one & right.one,
        },
        B::Or => KnownBits {
            zero: left.zero & right.zero,
            one: left.one | right.one,
        },
        B::Xor => KnownBits {
            zero: (left.zero & right.zero) | (left.one & right.one),
            one: (left.zero & right.one) | (left.one & right.zero),
        },
        B::Add | B::Sub => arithmetic(left, right, op == B::Sub),
        B::Shl | B::Shr | B::AShr => shift_cube(op, left, right),
        B::Mul => product(left, right, false),
        B::UMulHigh => product(left, right, true),
        B::SMulHigh if left.number() == Some(0) || right.number() == Some(0) => {
            KnownBits::constant(0)
        }
        B::SMulHigh if sign(left) == Some(false) && sign(right) == Some(false) => {
            product(left, right, true)
        }
        B::SMulHigh => KnownBits::UNKNOWN,
        B::UDiv => quotient(left, right),
        B::URem => remainder(left, right),
        B::SDiv => signed_quotient(left, right),
        B::SRem => signed_remainder(left, right),
        B::Eq | B::Ne => {
            boolean(((left.one & right.zero) | (left.zero & right.one) != 0).then_some(op == B::Ne))
        }
        B::Ult => boolean(if left.maximum() < right.minimum() {
            Some(true)
        } else if left.minimum() >= right.maximum() {
            Some(false)
        } else {
            None
        }),
        B::Ule => boolean(if left.maximum() <= right.minimum() {
            Some(true)
        } else if left.minimum() > right.maximum() {
            Some(false)
        } else {
            None
        }),
    }
}

#[cfg(test)]
#[path = "kernel_tests.rs"]
mod tests;

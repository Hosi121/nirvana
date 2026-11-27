//! Total modular transfer functions. Arithmetic carries and masked shift
//! counts follow the executable IR, including zero-divisor bit-vector values.
use super::*;

pub(super) fn binary_identity(op: B, a: KnownBits, b: KnownBits, kept: Operand) -> bool {
    let (a, b) = if kept == Operand::Left {
        (a, b)
    } else {
        (b, a)
    };
    match op {
        B::And => a.maximum() & !b.one == 0,
        B::Or => b.maximum() & !a.one == 0,
        _ => false,
    }
}
pub(super) fn unary_identity(op: UnaryOp, value: KnownBits) -> bool {
    match op {
        UnaryOp::Extract { start: 0, width } => value.maximum() & !width.mask() == 0,
        UnaryOp::SignExtend(width) => {
            let high = !width.mask();
            let sign = 1u64 << (width.bits() - 1);
            high == 0
                || (value.zero & sign != 0 && value.zero & high == high)
                || (value.one & sign != 0 && value.one & high == high)
        }
        _ => false,
    }
}
fn low(bits: u32) -> u64 {
    if bits >= 64 {
        u64::MAX
    } else {
        (1u64 << bits) - 1
    }
}
fn upper(maximum: u64) -> KnownBits {
    KnownBits {
        zero: !low(64 - maximum.leading_zeros()),
        one: 0,
    }
}
fn sign(v: KnownBits) -> Option<bool> {
    if v.zero >> 63 != 0 {
        Some(false)
    } else if v.one >> 63 != 0 {
        Some(true)
    } else {
        None
    }
}
pub(super) fn unary(op: UnaryOp, v: KnownBits) -> KnownBits {
    if let Some(n) = v.number() {
        return KnownBits::constant(op.evaluate(n));
    }
    if let UnaryOp::Extract { start, width } = op {
        if start >= 64 {
            return KnownBits::constant(0);
        }
        let shifted = fixed_shift(B::Shr, v, u32::from(start));
        return binary(B::And, shifted, KnownBits::constant(width.mask()));
    }
    let UnaryOp::SignExtend(width) = op else {
        unreachable!()
    };
    let mask = width.mask();
    let bit = 1u64 << (width.bits() - 1);
    KnownBits {
        zero: (v.zero & mask) | if v.zero & bit != 0 { !mask } else { 0 },
        one: (v.one & mask) | if v.one & bit != 0 { !mask } else { 0 },
    }
}
pub(super) fn binary(op: B, a: KnownBits, b: KnownBits) -> KnownBits {
    if let (Some(a), Some(b)) = (a.number(), b.number()) {
        return KnownBits::constant(op.evaluate(a, b));
    }
    match op {
        B::Insert { .. } => KnownBits {
            zero: op.evaluate(a.zero, b.zero),
            one: op.evaluate(a.one, b.one),
        },
        B::And => KnownBits {
            zero: a.zero | b.zero,
            one: a.one & b.one,
        },
        B::Or => KnownBits {
            zero: a.zero & b.zero,
            one: a.one | b.one,
        },
        B::Xor => KnownBits {
            zero: (a.zero & b.zero) | (a.one & b.one),
            one: (a.zero & b.one) | (a.one & b.zero),
        },
        B::Add => add(a, b, false),
        B::Sub => add(
            a,
            KnownBits {
                zero: b.one,
                one: b.zero,
            },
            true,
        ),
        B::Shl | B::Shr | B::AShr => shift(op, a, b),
        B::Mul => multiply(a, b),
        B::UMulHigh => upper(((u128::from(a.maximum()) * u128::from(b.maximum())) >> 64) as u64),
        B::SMulHigh if a.number() == Some(0) || b.number() == Some(0) => KnownBits::constant(0),
        B::SMulHigh if sign(a) == Some(false) && sign(b) == Some(false) => {
            binary(B::UMulHigh, a, b)
        }
        B::SMulHigh => KnownBits::UNKNOWN,
        B::UDiv => udiv(a, b),
        B::URem => urem(a, b),
        B::SDiv => sdiv(a, b),
        B::SRem => srem(a, b),
        B::Eq | B::Ne => {
            if a.one & b.zero != 0 || a.zero & b.one != 0 {
                KnownBits::constant(u64::from(op == B::Ne))
            } else {
                KnownBits {
                    zero: u64::MAX ^ 1,
                    one: 0,
                }
            }
        }
        B::Ult | B::Ule => {
            let truth = if op == B::Ult {
                if a.maximum() < b.minimum() {
                    Some(true)
                } else if a.minimum() >= b.maximum() {
                    Some(false)
                } else {
                    None
                }
            } else if a.maximum() <= b.minimum() {
                Some(true)
            } else if a.minimum() > b.maximum() {
                Some(false)
            } else {
                None
            };
            truth.map_or(
                KnownBits {
                    zero: u64::MAX ^ 1,
                    one: 0,
                },
                |v| KnownBits::constant(u64::from(v)),
            )
        }
    }
}
fn add(a: KnownBits, b: KnownBits, carry: bool) -> KnownBits {
    if a == KnownBits::UNKNOWN || b == KnownBits::UNKNOWN {
        return KnownBits::UNKNOWN;
    }
    let mut result = KnownBits::UNKNOWN;
    let mut carries = if carry { 2u8 } else { 1 };
    for bit in 0..64 {
        let mask = 1u64 << bit;
        let possibilities = |v: KnownBits| {
            if v.zero & mask != 0 {
                1u8
            } else if v.one & mask != 0 {
                2
            } else {
                3
            }
        };
        let pa = possibilities(a);
        let pb = possibilities(b);
        let mut sums = 0u8;
        let mut next = 0u8;
        for x in 0..2 {
            for y in 0..2 {
                for c in 0..2 {
                    if pa & (1 << x) != 0 && pb & (1 << y) != 0 && carries & (1 << c) != 0 {
                        let sum = x + y + c;
                        sums |= 1 << (sum & 1);
                        next |= 1 << (sum >> 1);
                    }
                }
            }
        }
        if sums == 1 {
            result.zero |= mask
        } else if sums == 2 {
            result.one |= mask
        }
        carries = next;
    }
    result
}
fn fixed_shift(op: B, a: KnownBits, n: u32) -> KnownBits {
    if n == 0 {
        return a;
    }
    match op {
        B::Shl => KnownBits {
            zero: (a.zero << n) | low(n),
            one: a.one << n,
        },
        B::Shr => KnownBits {
            zero: (a.zero >> n) | (u64::MAX << (64 - n)),
            one: a.one >> n,
        },
        B::AShr => {
            let fill = u64::MAX << (64 - n);
            KnownBits {
                zero: (a.zero >> n) | if sign(a) == Some(false) { fill } else { 0 },
                one: (a.one >> n) | if sign(a) == Some(true) { fill } else { 0 },
            }
        }
        _ => unreachable!(),
    }
}
fn shift(op: B, a: KnownBits, b: KnownBits) -> KnownBits {
    if let Some(n) = b.number() {
        return fixed_shift(op, a, (n & 63) as u32);
    }
    let mut result: Option<KnownBits> = None;
    for n in 0..64u64 {
        if n & b.zero & 63 == 0 && n & b.one & 63 == b.one & 63 {
            let next = fixed_shift(op, a, n as u32);
            result = Some(result.map_or(next, |old| old.join(next)));
        }
    }
    result.unwrap_or(KnownBits::UNKNOWN)
}
fn multiply(a: KnownBits, b: KnownBits) -> KnownBits {
    if a.number() == Some(0) || b.number() == Some(0) {
        return KnownBits::constant(0);
    }
    for (value, factor) in [(a, b), (b, a)] {
        if let Some(n) = factor.number()
            && n.is_power_of_two()
        {
            return fixed_shift(B::Shl, value, n.trailing_zeros());
        }
    }
    let zeros = low(a
        .zero
        .trailing_ones()
        .saturating_add(b.zero.trailing_ones()));
    let maximum = u128::from(a.maximum()) * u128::from(b.maximum());
    KnownBits {
        zero: zeros
            | if maximum <= u128::from(u64::MAX) {
                upper(maximum as u64).zero
            } else {
                0
            },
        one: 0,
    }
}
fn udiv(a: KnownBits, b: KnownBits) -> KnownBits {
    if b.number() == Some(0) {
        return KnownBits::constant(u64::MAX);
    }
    if let Some(n) = b.number()
        && n.is_power_of_two()
    {
        return fixed_shift(B::Shr, a, n.trailing_zeros());
    }
    if b.minimum() != 0 {
        upper(a.maximum() / b.minimum())
    } else {
        KnownBits::UNKNOWN
    }
}
fn congruence(a: KnownBits, b: KnownBits) -> KnownBits {
    let mask = low(b.zero.trailing_ones());
    KnownBits {
        zero: a.zero & mask,
        one: a.one & mask,
    }
}
fn urem(a: KnownBits, b: KnownBits) -> KnownBits {
    if b.number() == Some(0) {
        return a;
    }
    if let Some(n) = b.number()
        && n.is_power_of_two()
    {
        return binary(B::And, a, KnownBits::constant(n - 1));
    }
    if b.minimum() != 0 && a.maximum() < b.minimum() {
        return a;
    }
    let maximum = if b.minimum() != 0 {
        a.maximum().min(b.maximum() - 1)
    } else {
        a.maximum()
    };
    let lower = congruence(a, b);
    KnownBits {
        zero: upper(maximum).zero | lower.zero,
        one: lower.one,
    }
}
fn sdiv(a: KnownBits, b: KnownBits) -> KnownBits {
    match b.number() {
        Some(0) => {
            return match sign(a) {
                Some(true) => KnownBits::constant(1),
                Some(false) => KnownBits::constant(u64::MAX),
                None => KnownBits { zero: 0, one: 1 },
            };
        }
        Some(1) => return a,
        Some(u64::MAX) => return binary(B::Sub, KnownBits::constant(0), a),
        _ => {}
    }
    if sign(a) == Some(false) && sign(b) == Some(false) {
        udiv(a, b)
    } else {
        KnownBits::UNKNOWN
    }
}
fn srem(a: KnownBits, b: KnownBits) -> KnownBits {
    match b.number() {
        Some(0) => return a,
        Some(1 | u64::MAX) => return KnownBits::constant(0),
        Some(n) => {
            let magnitude = if n >> 63 != 0 { n.wrapping_neg() } else { n };
            if sign(a) == Some(false) {
                return urem(a, KnownBits::constant(magnitude));
            }
            if magnitude.is_power_of_two() && a.zero & (magnitude - 1) == magnitude - 1 {
                return KnownBits::constant(0);
            }
        }
        _ => {}
    }
    let lower = congruence(a, b);
    let bound = if sign(a) == Some(false) {
        upper(a.maximum()).zero
    } else {
        0
    };
    KnownBits {
        zero: bound | lower.zero,
        one: lower.one,
    }
}

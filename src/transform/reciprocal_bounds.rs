//! Integer error bounds for reciprocal division, independent of IR matching.
//!
//! For X=q*D+r and M*D=P+E, M*X=q*P+q*E+M*r. The error is
//! monotone in q and r. Its maximum is attained at the final full quotient
//! interval or at the end of the final partial interval.

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct Reciprocal {
    pub divisor: u64,
    pub excess: u64,
    multiplier: u128,
}

/// A word-sized signed quotient certificate. The positive endpoint excludes
/// the sign bit; the negative magnitude domain includes that endpoint.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct SignedReciprocal {
    pub divisor: u64,
    pub excess: u64,
    pub positive_bound: u128,
    pub negative_bound: u128,
}

impl SignedReciprocal {
    pub fn infer(multiplier: u64, bits: u32, shift: u32) -> Option<Self> {
        if !(2..=64).contains(&bits) || shift >= bits {
            return None;
        }
        let power = 1u128.checked_shl(bits + shift)?;
        let divisor = Reciprocal::infer(u128::from(multiplier), power)?.divisor;
        Self::check(multiplier, bits, shift, divisor)
    }

    pub fn check(multiplier: u64, bits: u32, shift: u32, divisor: u64) -> Option<Self> {
        if !(2..=64).contains(&bits) || shift >= bits || u128::from(multiplier) >= (1u128 << bits) {
            return None;
        }
        let negative_maximum = 1u64 << (bits - 1);
        if divisor >= negative_maximum {
            return None;
        }
        let power = 1u128.checked_shl(bits + shift)?;
        let reciprocal = Reciprocal::check(u128::from(multiplier), power, divisor)?;
        let positive_bound = reciprocal.exact_bound(negative_maximum - 1)?;
        let negative_bound = reciprocal.exact_bound(negative_maximum)?;
        if reciprocal.excess == 0 || positive_bound >= power || negative_bound > power {
            return None;
        }
        Some(Self {
            divisor,
            excess: reciprocal.excess,
            positive_bound,
            negative_bound,
        })
    }
}

impl Reciprocal {
    pub fn infer(multiplier: u128, power: u128) -> Option<Self> {
        if multiplier == 0 || power == 0 {
            return None;
        }
        let divisor = power.div_ceil(multiplier);
        Self::check(multiplier, power, u64::try_from(divisor).ok()?)
    }

    pub fn check(multiplier: u128, power: u128, divisor: u64) -> Option<Self> {
        if multiplier == 0 || power == 0 || divisor < 2 {
            return None;
        }
        let ceiling = power.div_ceil(multiplier);
        if ceiling != u128::from(divisor) {
            return None;
        }
        let excess = multiplier
            .checked_mul(u128::from(divisor))?
            .checked_sub(power)?;
        if excess >= u128::from(divisor) {
            return None;
        }
        Some(Self {
            divisor,
            excess: u64::try_from(excess).ok()?,
            multiplier,
        })
    }

    /// Bound q and r independently; preserves the established unsigned
    /// certificates' numerical fields and conservative acceptance conditions.
    pub fn conservative_bound(self, maximum: u64) -> Option<u128> {
        u128::from(maximum / self.divisor)
            .checked_mul(u128::from(self.excess))?
            .checked_add(self.multiplier.checked_mul(u128::from(self.divisor - 1))?)
    }

    /// Exact maximum error over 0 <= X <= maximum, including an empty set
    /// of full quotient intervals when maximum < divisor.
    pub fn exact_bound(self, maximum: u64) -> Option<u128> {
        let (q, r) = (maximum / self.divisor, maximum % self.divisor);
        let terminal = u128::from(q)
            .checked_mul(u128::from(self.excess))?
            .checked_add(self.multiplier.checked_mul(u128::from(r))?)?;
        if q == 0 {
            return Some(terminal);
        }
        let full = u128::from(q - 1)
            .checked_mul(u128::from(self.excess))?
            .checked_add(self.multiplier.checked_mul(u128::from(self.divisor - 1))?)?;
        Some(full.max(terminal))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn exact_error_bounds_match_enumerated_integer_domains() {
        let mut checked = 0;
        for shift in 1..=10 {
            for multiplier in 1..=512 {
                let Some(r) = Reciprocal::infer(multiplier, 1 << shift) else {
                    continue;
                };
                for maximum in [0, 1, 2, 7, 31, 255] {
                    let expected = (0..=maximum)
                        .map(|x| {
                            u128::from(x / r.divisor) * u128::from(r.excess)
                                + multiplier * u128::from(x % r.divisor)
                        })
                        .max()
                        .unwrap();
                    assert_eq!(r.exact_bound(maximum), Some(expected));
                    assert!(r.conservative_bound(maximum).unwrap() >= expected);
                    checked += 1;
                }
            }
        }
        assert!(checked > 1000);
    }

    #[test]
    fn certified_reciprocals_match_every_unsigned_byte() {
        let mut checked = 0;
        for divisor in 2..=255u64 {
            for shift in 0..8 {
                let p = 1u128 << (8 + shift);
                let m = p.div_ceil(u128::from(divisor));
                if m > 255 {
                    continue;
                }
                let Some(r) = Reciprocal::check(m, p, divisor) else {
                    continue;
                };
                if r.exact_bound(255).unwrap() >= p {
                    continue;
                }
                for x in 0..=255u128 {
                    assert_eq!(m * x / p, x / u128::from(divisor));
                    checked += 1;
                }
            }
        }
        assert!(checked > 10000);
    }

    #[test]
    fn signed_bounds_preserve_minimum_values_and_negative_magic_addition() {
        let mut checked = 0;
        let mut add_kernels = 0;
        for divisor in 2..=127u64 {
            for shift in 0..8 {
                let p = 1u128 << (8 + shift);
                let m = p.div_ceil(u128::from(divisor));
                if m > 255 {
                    continue;
                }
                let Some(r) = Reciprocal::check(m, p, divisor) else {
                    continue;
                };
                let signed = SignedReciprocal::check(m as u64, 8, shift, divisor);
                let expected = r.excess != 0
                    && r.exact_bound(127).unwrap() < p
                    && r.exact_bound(128).unwrap() <= p;
                assert_eq!(signed.is_some(), expected);
                if r.excess == 0
                    || r.exact_bound(127).unwrap() >= p
                    || r.exact_bound(128).unwrap() > p
                {
                    continue;
                }
                for x in -128..=127i16 {
                    let mut high = ((x * i16::from(m as u8 as i8)) >> 8) as i8;
                    if m >= 128 {
                        high = high.wrapping_add(x as i8);
                    }
                    let quotient = (high >> shift).wrapping_sub((x >> 7) as i8);
                    assert_eq!(
                        i16::from(quotient),
                        x / divisor as i16,
                        "x={x}, d={divisor}, m={m}, s={shift}"
                    );
                    checked += 1;
                }
                add_kernels += usize::from(m >= 128);
            }
        }
        let third = Reciprocal::check(86, 256, 3).unwrap();
        assert_eq!(third.exact_bound(128), Some(256));
        assert!(third.exact_bound(127).unwrap() < 256);
        assert!(checked > 10000 && add_kernels > 0);
    }

    #[test]
    fn invalid_and_overflowing_parameters_decline() {
        for (m, p, d) in [
            (0, 256, 3),
            (86, 0, 3),
            (86, 256, 0),
            (86, 256, 1),
            (86, 256, 4),
            (85, 256, 3),
            (u128::MAX, 1, 2),
        ] {
            assert_eq!(Reciprocal::check(m, p, d), None);
        }
        assert_eq!(Reciprocal::infer(0, 256), None);
        assert_eq!(Reciprocal::infer(1, 0), None);
        let wide = Reciprocal::check((1u128 << 64) + 0x2492492492492493, 1u128 << 67, 7).unwrap();
        assert!(wide.exact_bound(u64::MAX).unwrap() < (1u128 << 67));
    }
}

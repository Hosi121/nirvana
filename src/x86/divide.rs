//! DIV/IDIV arithmetic, separate from operand reads and instruction effects.
//!
//! Intel SDM Vol.2A, DIV pp3-330–332 and IDIV pp3-507–509 (325383, 835757).
//! https://cdrdv2-public.intel.com/835757/325383-sdm-vol-2abcd.pdf
use crate::ir::Width;

/// Return complete post-instruction RAX/RDX, or None for #DE. The source is
/// the already-read operand; callers retain the original state on failure.
/// The Rust reference uses double-width arithmetic, independently of C's
/// unsigned restoring division. Undefined flags are an instruction policy.
pub fn evaluate(width: Width, signed: bool, rax: u64, rdx: u64, source: u64) -> Option<(u64, u64)> {
    let bits = width.bits();
    let mask = width.mask();
    let high = if width == Width::U8 {
        (rax >> 8) & mask
    } else {
        rdx & mask
    };
    let low = rax & mask;
    let divisor = source & mask;
    if divisor == 0 {
        return None;
    }
    let numerator = (u128::from(high) << bits) | u128::from(low);
    let (quotient, remainder) = if signed {
        let shift = 128 - bits * 2;
        let numerator = ((numerator << shift) as i128) >> shift;
        let divisor = (((u128::from(divisor) << (128 - bits)) as i128) >> (128 - bits)) as i64;
        let quotient = numerator.checked_div(i128::from(divisor))?;
        let half = 1i128 << (bits - 1);
        if !(-half..half).contains(&quotient) {
            return None;
        }
        (
            quotient as u64 & mask,
            (numerator % i128::from(divisor)) as u64 & mask,
        )
    } else {
        let quotient = numerator / u128::from(divisor);
        if quotient > u128::from(mask) {
            return None;
        }
        (quotient as u64, (numerator % u128::from(divisor)) as u64)
    };
    Some(match width {
        Width::U8 => ((rax & !0xffff) | quotient | (remainder << 8), rdx),
        Width::U16 => ((rax & !mask) | quotient, (rdx & !mask) | remainder),
        Width::U32 | Width::U64 => (quotient, remainder),
    })
}

pub(crate) const C_HELPER: &str = include_str!("divide.h");

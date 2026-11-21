//! Compact constructors for source IR cases; expected behavior stays in tests.
use nirvana::ir::{Expr, Reg};
/// Independent numeric oracle using Rust's narrow signed integer conversions.
pub fn unary_value(op: nirvana::ir::UnaryOp, value: u64) -> u64 {
    use nirvana::ir::{UnaryOp, Width};
    match op {
        UnaryOp::SignExtend(Width::U8) => value as u8 as i8 as i64 as u64,
        UnaryOp::SignExtend(Width::U16) => value as u16 as i16 as i64 as u64,
        UnaryOp::SignExtend(Width::U32) => value as u32 as i32 as i64 as u64,
        UnaryOp::SignExtend(Width::U64) => value,
        UnaryOp::Extract { start, width } => {
            let mut result = 0u64;
            for bit in 0..width.bits() {
                let source = u32::from(start) + bit;
                if source < 64 && (value >> source) & 1 != 0 {
                    result |= 1u64 << bit;
                }
            }
            result
        }
    }
}
/// Restoring long division supplies an oracle independent of the executable
/// IR's host integer division and the C backend's unsigned magnitudes.
pub fn division_value(op: nirvana::ir::BinaryOp, left: u64, right: u64) -> u64 {
    use nirvana::ir::BinaryOp as B;
    let signed = matches!(op, B::SDiv | B::SRem);
    let a = if signed && left >> 63 != 0 {
        left.wrapping_neg()
    } else {
        left
    };
    let b = if signed && right >> 63 != 0 {
        right.wrapping_neg()
    } else {
        right
    };
    let (q, r) = if b == 0 {
        (u64::MAX, a)
    } else {
        let mut q = 0u64;
        let mut r = 0u128;
        for bit in (0..64).rev() {
            r = (r << 1) | u128::from((a >> bit) & 1);
            if r >= u128::from(b) {
                r -= u128::from(b);
                q |= 1 << bit;
            }
        }
        (q, r as u64)
    };
    match op {
        B::UDiv => q,
        B::URem => r,
        B::SDiv => {
            if (left ^ right) >> 63 != 0 {
                q.wrapping_neg()
            } else {
                q
            }
        }
        B::SRem => {
            if left >> 63 != 0 {
                r.wrapping_neg()
            } else {
                r
            }
        }
        _ => panic!("division oracle received {op:?}"),
    }
}
pub fn r(index: usize) -> Expr {
    Expr::Register(Reg(index))
}
pub fn c(value: u64) -> Expr {
    Expr::Const(value)
}

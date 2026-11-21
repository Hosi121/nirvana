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
    }
}
pub fn r(index: usize) -> Expr {
    Expr::Register(Reg(index))
}
pub fn c(value: u64) -> Expr {
    Expr::Const(value)
}

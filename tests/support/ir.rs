//! Compact constructors for source IR cases; expected behavior stays in tests.
use nirvana::ir::{Expr, Reg};
pub fn r(index: usize) -> Expr {
    Expr::Register(Reg(index))
}
pub fn c(value: u64) -> Expr {
    Expr::Const(value)
}

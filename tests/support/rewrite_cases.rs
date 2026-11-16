use nirvana::ir::{BinaryOp::*, Expr, Reg};

fn r(i: usize) -> Expr {
    Expr::Register(Reg(i))
}
fn c(v: u64) -> Expr {
    Expr::Const(v)
}
fn b(op: nirvana::ir::BinaryOp, a: Expr, v: Expr) -> Expr {
    Expr::binary(op, a, v)
}

pub fn semantic_mutants() -> Vec<(&'static str, Expr, Expr)> {
    vec![
        (
            "wrong-shift-width",
            b(Shl, r(0), r(1)),
            b(Shl, r(0), b(And, r(1), c(31))),
        ),
        ("ignore-overflow", b(Eq, b(Add, r(0), c(1)), c(0)), c(0)),
        ("truthiness-as-value", Expr::select(r(0), c(1), c(0)), r(0)),
        (
            "wrong-signedness",
            b(Ult, r(0), r(1)),
            b(Ult, b(Xor, r(0), c(1 << 63)), b(Xor, r(1), c(1 << 63))),
        ),
    ]
}

pub fn cases() -> Vec<(&'static str, Expr)> {
    vec![
        ("add-zero", b(Add, r(0), c(0))),
        ("zero-add", b(Add, c(0), r(0))),
        ("subtract-zero", b(Sub, r(0), c(0))),
        ("self-subtract", b(Sub, r(0), r(0))),
        ("multiply-one", b(Mul, r(0), c(1))),
        ("multiply-zero", b(Mul, r(0), c(0))),
        ("and-all", b(And, r(0), c(u64::MAX))),
        ("and-zero", b(And, r(0), c(0))),
        ("or-zero", b(Or, r(0), c(0))),
        ("or-all", b(Or, r(0), c(u64::MAX))),
        ("self-xor", b(Xor, r(0), r(0))),
        ("self-and", b(And, r(0), r(0))),
        ("self-or", b(Or, r(0), r(0))),
        ("self-equal", b(Eq, r(0), r(0))),
        ("self-unequal", b(Ne, r(0), r(0))),
        ("self-less", b(Ult, r(0), r(0))),
        ("self-less-equal", b(Ule, r(0), r(0))),
        ("cmp-equal", b(Eq, b(Sub, r(0), r(1)), c(0))),
        ("cmp-unequal", b(Ne, c(0), b(Sub, r(0), r(1)))),
        (
            "unsigned-less-equal",
            b(Or, b(Ult, r(0), r(1)), b(Eq, r(0), r(1))),
        ),
        ("invert-less", b(Xor, b(Ult, r(0), r(1)), c(1))),
        ("invert-equal", b(Eq, b(Eq, r(0), r(1)), c(0))),
        ("boolean-and", b(And, b(Ult, r(0), r(1)), c(1))),
        ("boolean-equal-one", b(Eq, b(Ult, r(0), r(1)), c(1))),
        ("boolean-impossible", b(Eq, b(Ult, r(0), r(1)), c(2))),
        ("compare-zero", b(Ult, r(0), c(0))),
        ("compare-max", b(Ule, r(0), c(u64::MAX))),
        ("shift-64", b(Shl, r(0), c(64))),
        ("shift-65", b(Shr, r(0), c(65))),
        ("shift-count-mask", b(Shl, r(0), b(And, r(1), c(127)))),
        ("constant-wrap", b(Add, b(Add, r(0), c(u64::MAX)), c(1))),
        ("constant-sub-wrap", b(Sub, b(Sub, r(0), c(u64::MAX)), c(1))),
        ("nested-mask", b(And, b(And, r(0), c(255)), c(15))),
        ("coefficient", b(Add, r(0), b(Mul, r(0), c(2)))),
        ("coefficient-wrap", b(Add, b(Mul, r(0), c(u64::MAX)), r(0))),
        ("high-product-zero", b(UMulHigh, r(0), c(0))),
        (
            "high-product-constant",
            b(UMulHigh, c(u64::MAX), c(u64::MAX)),
        ),
        ("select-constant", Expr::select(c(0), r(0), r(1))),
        ("select-equal", Expr::select(r(0), r(1), r(1))),
        ("select-truthiness", Expr::select(r(0), c(1), c(0))),
        (
            "select-inversion",
            Expr::select(b(Eq, r(0), c(0)), r(1), r(2)),
        ),
        (
            "machine-cmp",
            b(
                Or,
                b(Or, b(Ult, r(0), c(9)), b(And, c(0), b(Eq, r(0), c(9)))),
                b(Eq, b(Sub, b(Sub, r(0), c(9)), c(0)), c(0)),
            ),
        ),
    ]
}

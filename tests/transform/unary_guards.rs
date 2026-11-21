use crate::support::ir::{c, r};
use nirvana::ir::{BinaryOp as B, Expr, UnaryOp as U, Width};
fn b(op: B, a: Expr, z: Expr) -> Expr {
    Expr::binary(op, a, z)
}
fn u(x: Expr) -> Expr {
    Expr::unary(U::SignExtend(Width::U32), x)
}
fn unsigned(x: Expr) -> Expr {
    b(B::Shr, b(B::UMulHigh, x, c(0xaaaa_aaaa_aaaa_aaab)), c(1))
}
fn signed(x: Expr) -> Expr {
    b(
        B::Sub,
        b(
            B::AShr,
            b(B::SMulHigh, x.clone(), c(0x6666_6666_6666_6667)),
            c(2),
        ),
        b(B::AShr, x, c(63)),
    )
}
fn narrow(x: Expr) -> Expr {
    b(
        B::Shr,
        b(B::Mul, b(B::And, x, c(u32::MAX as u64)), c(0xaaaa_aaab)),
        c(33),
    )
}
fn rotate(x: Expr) -> Expr {
    b(B::Or, b(B::Shl, x.clone(), c(8)), b(B::Shr, x, c(56)))
}

#[test]
fn unary_values_keep_their_width_and_load_free_views_keep_every_guard() {
    let x = u(r(0));
    for (source, d) in [(unsigned(x.clone()), 3), (narrow(x.clone()), 3)] {
        let view = nirvana::division_expr::recognize(&source)
            .map(|v| v.divisor)
            .or_else(|| nirvana::narrow_division_expr::recognize(&source).map(|v| v.divisor));
        assert_eq!(view, Some(d));
    }
    assert_eq!(
        nirvana::signed_division_expr::recognize(&signed(x.clone()))
            .unwrap()
            .divisor,
        10
    );
    assert!(nirvana::bit_expr::recognize(&rotate(x)).is_some());
    for source in [
        Expr::load(r(0), Width::U64),
        Expr::select(c(0), Expr::load(r(0), Width::U64), r(1)),
    ] {
        let x = u(source);
        assert!(nirvana::division_expr::recognize(&unsigned(x.clone())).is_none());
        assert!(nirvana::narrow_division_expr::recognize(&narrow(x.clone())).is_none());
        assert!(nirvana::signed_division_expr::recognize(&signed(x.clone())).is_none());
        assert!(nirvana::bit_expr::recognize(&rotate(x.clone())).is_none());
        assert!(nirvana::access_expr::recognize(&b(B::Add, r(7), b(B::Mul, x, c(8)))).is_none());
    }
    let mut deep = r(0);
    for _ in 0..130 {
        deep = u(deep);
    }
    assert!(nirvana::division_expr::recognize(&unsigned(deep.clone())).is_none());
    assert!(nirvana::signed_division_expr::recognize(&signed(deep)).is_none());
}

//! Projection expressions shared by executable and universal checks.
use super::ir::{c, r};
use nirvana::ir::{BinaryOp::And, Expr};
fn b(op: nirvana::ir::BinaryOp, a: Expr, value: Expr) -> Expr {
    Expr::binary(op, a, value)
}
/// Projection algebra shared by the executable fault tests and SMT harness.
/// Successful simplifications are always compared with the actual candidate.
pub fn cases() -> Vec<(String, Expr)> {
    use nirvana::ir::{UnaryOp as U, Width};
    let widths = [Width::U8, Width::U16, Width::U32, Width::U64];
    let starts = [0, 1, 7, 8, 15, 16, 31, 32, 63, 64, 127, 255];
    let extract = |start, width, value| Expr::unary(U::Extract { start, width }, value);
    let mut result = Vec::new();
    for width in widths {
        for inner in widths {
            for start in starts {
                for outer in [0, 1, 8, 32, 64] {
                    result.push((
                        format!("nested-{}-{}-{start}-{outer}", width.bits(), inner.bits()),
                        extract(outer, width, extract(start, inner, r(0))),
                    ));
                }
                result.push((
                    format!("signed-{}-{}-{start}", width.bits(), inner.bits()),
                    extract(start, width, Expr::unary(U::SignExtend(inner), r(0))),
                ));
            }
        }
        for mask in [
            0,
            1,
            7,
            255,
            65535,
            u32::MAX as u64,
            1 << 63,
            0x5555_5555_5555_5555,
            u64::MAX,
        ] {
            for reverse in [false, true] {
                let slice = extract(0, width, r(0));
                result.push((
                    format!("mask-{}-{mask}-{reverse}", width.bits()),
                    if reverse {
                        b(And, c(mask), slice)
                    } else {
                        b(And, slice, c(mask))
                    },
                ));
                result.push((
                    format!("project-mask-{}-{mask}-{reverse}", width.bits()),
                    extract(
                        0,
                        width,
                        if reverse {
                            b(And, c(mask), r(0))
                        } else {
                            b(And, r(0), c(mask))
                        },
                    ),
                ));
            }
        }
    }
    result
}

/// Ring/bitwise candidates with full u64 inputs and an explicit word observer.
pub fn word_cases() -> Vec<(String, Expr)> {
    use nirvana::ir::{BinaryOp as B, UnaryOp as U, Width};
    let mut result = Vec::new();
    for width in [Width::U8, Width::U16, Width::U32] {
        let clip = |kind, e| match kind {
            0 => b(And, e, c(width.mask())),
            1 => Expr::unary(U::Extract { start: 0, width }, e),
            _ => Expr::unary(U::SignExtend(width), e),
        };
        for inner in 0..3 {
            let a = clip(inner, r(0));
            let z = clip(inner, r(1));
            let mut forms = vec![
                (
                    "sub-coefficient",
                    b(B::Sub, b(B::Mul, a.clone(), c(8)), a.clone()),
                ),
                (
                    "wrapped-coefficient",
                    b(B::Sub, b(B::Mul, a.clone(), c(u64::MAX)), a.clone()),
                ),
                ("constant-mul", b(B::Mul, a.clone(), c(7))),
                ("variable-shift", b(B::Shl, a.clone(), r(1))),
            ];
            for (name, op) in [
                ("add", B::Add),
                ("sub", B::Sub),
                ("and", B::And),
                ("or", B::Or),
                ("xor", B::Xor),
            ] {
                forms.push((name, b(op, a.clone(), z.clone())));
            }
            for outer in 0..3 {
                for (name, form) in &forms {
                    result.push((
                        format!("word-{}-{inner}-{outer}-{name}", width.bits()),
                        clip(outer, form.clone()),
                    ));
                }
            }
        }
    }
    result
}

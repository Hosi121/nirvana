//! C typing and grouping for certified division/remainder views and large divisors.
#[allow(dead_code)]
#[path = "support/native.rs"]
mod native;

use nirvana::ir::{BinaryOp as B, Control, Expr, IrInstruction, Program, Reg};
use nirvana::readable::emit_readable_c;
use std::fmt::Write as _;

fn r(index: usize) -> Expr {
    Expr::Register(Reg(index))
}
fn c(value: u64) -> Expr {
    Expr::Const(value)
}
fn b(op: B, left: Expr, right: Expr) -> Expr {
    Expr::binary(op, left, right)
}

#[test]
fn division_and_remainder_keep_unsigned_constants_wrap_and_grouping() {
    let scratch = native::Scratch::new();
    let values = [
        0,
        1,
        2,
        9,
        10,
        11,
        (1 << 63) - 1,
        1 << 63,
        u64::MAX - 1,
        u64::MAX,
    ];
    let numerators = [
        r(0),
        b(B::Add, r(0), r(1)),
        b(B::Mul, b(B::Add, r(0), c(1)), r(1)),
        Expr::select(
            b(B::Ult, r(0), r(1)),
            b(B::Add, r(0), r(1)),
            b(B::Sub, r(0), r(1)),
        ),
    ];
    let mut configurations = 0;
    for (magic, shift, divisor) in [
        (0xcccc_cccc_cccc_cccd, 3, 10),
        (u64::MAX, 63, (1 << 63) + 1),
    ] {
        for numerator in &numerators {
            for reverse in [false, true] {
                for (outer, remainder) in
                    [(false, false), (true, false), (false, true), (true, true)]
                {
                    let product = if reverse {
                        b(B::UMulHigh, c(magic), numerator.clone())
                    } else {
                        b(B::UMulHigh, numerator.clone(), c(magic))
                    };
                    let quotient = b(B::Shr, product, c(shift));
                    let quotient = if remainder {
                        b(B::Sub, numerator.clone(), b(B::Mul, quotient, c(divisor)))
                    } else {
                        quotient
                    };
                    let expression = if outer {
                        b(B::Mul, r(1), quotient)
                    } else {
                        quotient
                    };
                    let program = Program::new(
                        0,
                        2,
                        vec![IrInstruction {
                            address: 0,
                            size: 1,
                            assignments: vec![],
                            control: Control::Return(expression),
                        }],
                    )
                    .unwrap();
                    let original = program.instructions().to_vec();
                    let output = emit_readable_c(&program).unwrap();
                    let operator = if remainder { " % " } else { " / " };
                    assert!(output.code.contains(operator), "{}", output.code);
                    assert!(
                        !output.code.contains("nirvana_umul_high("),
                        "unused helper: {}",
                        output.code
                    );
                    if divisor > i64::MAX as u64 {
                        assert!(output.code.contains("UINT64_C(0x8000000000000001)"));
                    }
                    let mut text = String::new();
                    let mut expected = Vec::new();
                    for left in values {
                        for right in values {
                            writeln!(text, "{left} {right}").unwrap();
                            expected.push(vec![program.execute(&[left, right], 10).unwrap().value]);
                        }
                    }
                    let arguments = output
                        .parameters
                        .iter()
                        .map(|reg| format!("r[{}]", reg.0))
                        .collect::<Vec<_>>()
                        .join(", ");
                    let source = format!(
                        r#"{}
#include <stdio.h>
#include <inttypes.h>
int main(void) {{
    uint64_t a,b;
    while(scanf("%" SCNu64 " %" SCNu64,&a,&b)==2) {{
        uint64_t r[2]={{a,b}};
        (void)r;
        printf("%" PRIu64 "\n",nirvana_readable({arguments}));
    }}
}}
"#,
                        output.code
                    );
                    for optimization in ["-O0", "-O2"] {
                        let path = scratch.0.join(format!("render-{configurations}.c"));
                        std::fs::write(&path, &source).unwrap();
                        let object = path.with_extension("o");
                        let binary = path.with_extension("bin");
                        native::object(&path, &object, optimization, "nirvana_readable");
                        native::link(&[&object], &binary);
                        assert_eq!(native::run_fields(&binary, &text, 1), expected);
                        configurations += 1;
                    }
                    assert_eq!(program.instructions(), original);
                }
            }
        }
    }
    assert_eq!(configurations, 128);
}

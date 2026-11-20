#[path = "support/native.rs"]
mod native;
#[path = "../examples/programs/mod.rs"]
mod programs;

use native::{Scratch, fixture_root, link, object, run};
use nirvana::ir::{BinaryOp::*, Control, Expr, IrInstruction, Program, Reg};
use nirvana::readable::emit_readable_c;
use std::fmt::Write;

fn r(index: usize) -> Expr {
    Expr::Register(Reg(index))
}
fn c(value: u64) -> Expr {
    Expr::Const(value)
}
fn b(op: nirvana::ir::BinaryOp, left: Expr, right: Expr) -> Expr {
    Expr::binary(op, left, right)
}

#[test]
fn c_integer_promotions_precedence_and_shift_counts_match_u64_ir() {
    let scratch = Scratch::new();
    let expressions = [
        b(Sub, b(Eq, r(0), r(1)), b(Ult, r(1), r(0))),
        b(Shl, b(Eq, r(0), r(1)), r(2)),
        b(Mul, b(Sub, b(Eq, r(0), r(1)), c(2)), r(2)),
        b(Shr, b(Add, r(0), r(1)), b(Add, r(2), c(1))),
        b(
            Xor,
            b(Or, b(Ule, r(0), r(1)), b(And, r(1), c(3))),
            b(Add, r(0), r(2)),
        ),
        b(
            Add,
            Expr::select(r(0), b(Eq, r(1), c(0)), c(2)),
            c(u64::MAX),
        ),
        b(Sub, r(0), b(Sub, r(1), r(2))),
        b(UMulHigh, b(Mul, r(0), r(1)), b(Add, r(2), c(17))),
    ];
    let values = [0, 1, 2, 31, 63, 64, 65, 1 << 63, u64::MAX];
    for optimization in ["-O0", "-O2"] {
        let harness = scratch.0.join(format!("harness{optimization}.o"));
        object(
            &fixture_root().join("harness.c"),
            &harness,
            optimization,
            "fixture",
        );
        for (index, expression) in expressions.iter().enumerate() {
            let program = Program::new(
                0,
                4,
                vec![IrInstruction {
                    address: 0,
                    size: 1,
                    assignments: vec![],
                    control: Control::Return(expression.clone()),
                }],
            )
            .unwrap();
            let output = emit_readable_c(&program).unwrap();
            let arguments = output
                .parameters
                .iter()
                .map(|reg| format!("r[{}]", reg.0))
                .collect::<Vec<_>>()
                .join(", ");
            let source = scratch.0.join(format!("case{index}{optimization}.c"));
            std::fs::write(&source, output.code + &format!("\nuint64_t fixture(uint64_t *r) {{ (void)r; return nirvana_readable({arguments}); }}\n")).unwrap();
            let compiled = source.with_extension("o");
            let binary = source.with_extension("bin");
            object(&source, &compiled, optimization, "fixture");
            link(&[&compiled, &harness], &binary);
            let mut text = String::new();
            let mut expected = Vec::new();
            for &left in &values {
                for &right in &values {
                    for &shift in &values {
                        let input = [left, right, shift, 0];
                        writeln!(text, "{left} {right} {shift} 0").unwrap();
                        let value = program.execute(&input, 1).unwrap().value;
                        expected.push(vec![value, left, right, shift, 0]);
                    }
                }
            }
            assert_eq!(
                run(&binary, &text),
                expected,
                "expression {index}, {optimization}"
            );
        }
    }
}

#[test]
fn structured_loops_have_conventional_c_syntax_and_goto_fallback_survives() {
    for name in programs::NAMES {
        let output = emit_readable_c(&programs::named(name).unwrap()).unwrap();
        if output.fallback_reason.is_some() {
            assert!(output.code.contains("goto bb"));
            assert!(output.structure_evidence.is_none());
        } else {
            assert!(output.structure_stats.is_some());
            assert!(output.structure_evidence.is_some());
        }
    }
    let sum = emit_readable_c(&programs::named("sum").unwrap()).unwrap();
    assert!(
        sum.code.contains("while (")
            || sum.code.contains("for (; ")
            || sum.code.contains("for (;\n"),
        "{}",
        sum.code
    );
    let irreducible = emit_readable_c(&programs::named("irreducible").unwrap()).unwrap();
    assert!(irreducible.fallback_reason.is_none());
    assert!(!irreducible.code.contains("goto bb"));
}

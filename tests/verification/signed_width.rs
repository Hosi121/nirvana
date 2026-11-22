use crate::support::ir::r;
use nirvana::{
    dataflow::signed_width::SignedWidths,
    ir::{
        Assignment, BinaryOp as B, Control, Expr, IrInstruction, Program, Reg, UnaryOp as U, Width,
    },
    verify::{self, Solver, Verdict},
};

#[test]
#[ignore = "requires Z3; set NIRVANA_Z3"]
fn signed_storage_transfer_bounds_have_universal_checks_and_unsigned_counterexamples() {
    let root =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("target/verification/signed-widths");
    std::fs::create_dir_all(&root).unwrap();
    let solver = Solver::new(std::env::var("NIRVANA_Z3").unwrap_or_else(|_| "z3".into()))
        .with_timeout(std::time::Duration::from_secs(3));
    let mut proved = 0;
    let mut broken = 0;
    let mut check = |name: String, expr: Expr, bad: Option<Width>| {
        let program = Program::new(
            0,
            4,
            vec![IrInstruction {
                address: 0,
                size: 1,
                assignments: vec![Assignment {
                    destination: Reg(3).into(),
                    value: expr.clone(),
                }],
                control: Control::Return(r(3)),
            }],
        )
        .unwrap();
        let bound = SignedWidths::analyze(&program).width(Reg(3));
        let width = if let Some(w) = bad {
            w
        } else {
            assert_ne!(bound, Width::U64);
            bound
        };
        let query =
            verify::pure_query(&expr, &Expr::unary(U::SignExtend(width), expr.clone())).unwrap();
        std::fs::write(
            root.join(format!("{name}.smt2")),
            format!("{}(check-sat)\n", query.smt2()),
        )
        .unwrap();
        let verdict = solver.check_query(&query);
        std::fs::write(root.join(format!("{name}.out")), format!("{verdict:?}\n")).unwrap();
        if bad.is_some() {
            let Verdict::Counterexample(w) = verdict else {
                panic!("{name}: {verdict:?}")
            };
            assert_ne!(w.before, w.after);
            broken += 1;
        } else {
            assert_eq!(verdict, Verdict::EquivalentUnderModel, "{name}");
            proved += 1;
        }
    };
    let widths = [Width::U8, Width::U16, Width::U32];
    for a in widths {
        for z in widths {
            let left = Expr::unary(U::SignExtend(a), r(0));
            let right = Expr::unary(U::SignExtend(z), r(1));
            for op in [B::And, B::Or, B::Xor] {
                check(
                    format!("bits-{}-{}-{op:?}", a.bits(), z.bits()),
                    Expr::binary(op, left.clone(), right.clone()),
                    None,
                );
            }
            check(
                format!("select-{}-{}", a.bits(), z.bits()),
                Expr::select(r(2), left, right),
                None,
            );
        }
    }
    for width in widths {
        check(
            format!("shift-{}", width.bits()),
            Expr::binary(B::AShr, Expr::unary(U::SignExtend(width), r(0)), r(1)),
            None,
        );
        let extract = Expr::unary(U::Extract { start: 0, width }, r(0));
        if width != Width::U32 {
            check(
                format!("unsigned-fits-{}", width.bits()),
                extract.clone(),
                None,
            );
        }
        check(
            format!("wrong-unsigned-{}", width.bits()),
            extract,
            Some(width),
        );
    }
    assert_eq!((proved, broken), (41, 3));
    std::fs::write(
        root.join("result.json"),
        format!(
            "{{\"model\":\"signed-ssa-storage-v1\",\"unsat\":{proved},\"sat_replayed\":{broken}}}\n"
        ),
    )
    .unwrap();
}

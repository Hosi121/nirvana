use crate::support::ir::{c, r};
use nirvana::ir::{BinaryOp as B, Expr, UnaryOp as U, Width};
use nirvana::verify::{self, Solver, Verdict};
fn b(op: B, a: Expr, z: Expr) -> Expr {
    Expr::binary(op, a, z)
}
fn low(width: Width, value: Expr) -> Expr {
    Expr::unary(U::Extract { start: 0, width }, value)
}
#[test]
#[ignore = "requires Z3; set NIRVANA_Z3"]
fn stored_word_projection_rules_have_universal_checks_and_replayed_width_mutants() {
    let solver = Solver::new(std::env::var("NIRVANA_Z3").unwrap_or_else(|_| "z3".into()));
    let root =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("target/verification/memory-values");
    std::fs::create_dir_all(&root).unwrap();
    let check = |name: &str, a: &Expr, z: &Expr| {
        let query = verify::pure_query(a, z).unwrap();
        std::fs::write(
            root.join(format!("{name}.smt2")),
            format!("{}(check-sat)\n", query.smt2()),
        )
        .unwrap();
        let verdict = solver.check_query(&query);
        std::fs::write(root.join(format!("{name}.out")), format!("{verdict:?}\n")).unwrap();
        verdict
    };
    let widths = [Width::U8, Width::U16, Width::U32, Width::U64];
    let mut proved = 0;
    for width in widths {
        for from in widths.into_iter().filter(|w| *w >= width) {
            for op in [
                U::SignExtend(from),
                U::Extract {
                    start: 0,
                    width: from,
                },
            ] {
                assert_eq!(
                    check(
                        &format!("project-{}-{op:?}", width.bits()),
                        &low(width, Expr::unary(op, r(0))),
                        &low(width, r(0))
                    ),
                    Verdict::EquivalentUnderModel
                );
                proved += 1;
            }
        }
        let mask = b(B::Or, r(1), c(width.mask()));
        assert_eq!(
            check(
                &format!("mask-{}", width.bits()),
                &low(width, b(B::And, r(0), mask)),
                &low(width, r(0))
            ),
            Verdict::EquivalentUnderModel
        );
        proved += 1;
    }
    let mutants = [
        (
            "narrow-signed",
            low(Width::U16, Expr::unary(U::SignExtend(Width::U8), r(0))),
            low(Width::U16, r(0)),
        ),
        (
            "missing-mask-bit",
            low(Width::U16, b(B::And, r(0), c(0xfffe))),
            low(Width::U16, r(0)),
        ),
        (
            "narrow-extract",
            low(Width::U16, low(Width::U8, r(0))),
            low(Width::U16, r(0)),
        ),
        (
            "shifted-word",
            low(Width::U8, b(B::Shr, r(0), c(8))),
            low(Width::U8, r(0)),
        ),
    ];
    for (name, a, z) in mutants {
        let Verdict::Counterexample(w) = check(name, &a, &z) else {
            panic!("missing replayed width witness {name}")
        };
        assert_ne!(w.before, w.after);
    }
    assert_eq!(proved, 24);
    println!(
        "{proved} universal stored-word projection identities; 4 IR-replayed width/mask SAT controls"
    );
}

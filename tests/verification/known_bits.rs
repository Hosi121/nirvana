use crate::support::ir::{c, r};
use nirvana::ir::{BinaryOp as B, Expr, UnaryOp, Width};
use nirvana::known_bits::KnownBits as K;
use nirvana::verify::{self, Solver, Verdict};
fn b(op: B, a: Expr, z: Expr) -> Expr {
    Expr::binary(op, a, z)
}
fn input(reg: usize, fact: K) -> Expr {
    b(
        B::Or,
        b(B::And, r(reg), c(!(fact.zero() | fact.one()))),
        c(fact.one()),
    )
}
fn violation(value: Expr, fact: K) -> Expr {
    b(
        B::Or,
        b(B::And, value.clone(), c(fact.zero())),
        b(B::Xor, b(B::And, value, c(fact.one())), c(fact.one())),
    )
}
fn save(solver: &Solver, name: &str, value: &Expr, fact: K) -> Verdict {
    let root =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("target/verification/known-bits");
    std::fs::create_dir_all(&root).unwrap();
    let query = verify::pure_query(&violation(value.clone(), fact), &c(0)).unwrap();
    std::fs::write(
        root.join(format!("{name}.smt2")),
        format!("{}(check-sat)\n", query.smt2()),
    )
    .unwrap();
    let verdict = solver.check_query(&query);
    std::fs::write(root.join(format!("{name}.out")), format!("{verdict:?}\n")).unwrap();
    verdict
}
#[test]
#[ignore = "requires Z3; set NIRVANA_Z3"]
fn known_bit_transfer_claims_have_universal_bit_vector_checks_and_replayed_controls() {
    let solver = Solver::new(std::env::var("NIRVANA_Z3").unwrap_or_else(|_| "z3".into()));
    let ops = [
        B::Add,
        B::Sub,
        B::Mul,
        B::And,
        B::Or,
        B::Xor,
        B::Shl,
        B::Shr,
        B::AShr,
        B::Eq,
        B::Ne,
        B::Ult,
        B::Ule,
        B::UMulHigh,
        B::SMulHigh,
        B::UDiv,
        B::URem,
        B::SDiv,
        B::SRem,
    ];
    let cases = [
        ("byte", K::new(!255, 0).unwrap(), K::constant(3)),
        ("multiple", K::new(15, 0).unwrap(), K::constant(16)),
        ("flags", K::new(!511, 256).unwrap(), K::new(!7, 1).unwrap()),
        (
            "negative",
            K::new(0, u64::MAX ^ 255).unwrap(),
            K::constant(1),
        ),
        ("zero-divisor", K::UNKNOWN, K::constant(0)),
        ("masked-count", K::new(!255, 128).unwrap(), K::constant(64)),
    ];
    let mut proved = 0;
    let mut skipped = 0;
    for (name, a, z) in cases {
        for op in ops {
            let fact = K::binary(op, a, z);
            if fact == K::UNKNOWN {
                skipped += 1;
                continue;
            }
            assert_eq!(
                save(
                    &solver,
                    &format!("{name}-{op:?}"),
                    &b(op, input(0, a), input(1, z)),
                    fact
                ),
                Verdict::EquivalentUnderModel,
                "{name}/{op:?}/{fact:?}"
            );
            proved += 1;
        }
    }
    let mut unary_ops = Vec::new();
    for width in [Width::U8, Width::U16, Width::U32, Width::U64] {
        unary_ops.push(UnaryOp::SignExtend(width));
        for start in [0, 1, 7, 8, 31, 32, 60, 63, 64, 255] {
            unary_ops.push(UnaryOp::Extract { start, width });
        }
    }
    for op in unary_ops {
        for (name, a) in [
            ("unknown", K::UNKNOWN),
            ("low", K::new(!255, 0).unwrap()),
            ("negative", K::new(0, u64::MAX ^ 127).unwrap()),
        ] {
            let fact = K::unary(op, a);
            if fact == K::UNKNOWN {
                skipped += 1;
                continue;
            }
            assert_eq!(
                save(
                    &solver,
                    &format!("unary-{op:?}-{name}"),
                    &Expr::unary(op, input(0, a)),
                    fact
                ),
                Verdict::EquivalentUnderModel
            );
            proved += 1;
        }
    }
    let mutants = [
        (
            "lost-carry",
            b(B::Add, input(0, K::new(!255, 0).unwrap()), c(1)),
            K::new(1 << 8, 0).unwrap(),
        ),
        ("unmasked-shift", b(B::Shl, r(0), c(64)), K::constant(0)),
        (
            "signed-divisor-zero",
            b(B::SDiv, r(0), c(0)),
            K::constant(0),
        ),
    ];
    for (name, value, fact) in mutants {
        let Verdict::Counterexample(w) = save(&solver, name, &value, fact) else {
            panic!("missing replayed witness {name}")
        };
        assert_ne!(w.before, 0);
    }
    assert!(proved >= 70);
    println!(
        "{proved} universal known-bit transfer claims; {skipped} unknown facts skipped; 3 IR-replayed SAT controls"
    );
}

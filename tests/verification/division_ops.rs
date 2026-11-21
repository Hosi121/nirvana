use crate::support::ir::{c, division_value, r};
use crate::support::word_reciprocals::{b, cases, kernel, sext, word};
use nirvana::ir::{BinaryOp as B, Expr, Width};
use nirvana::verify::{self, Solver, Verdict};

fn save(name: &str, a: &Expr, z: &Expr, solver: &Solver) -> Verdict {
    let root =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("target/verification/total-division");
    std::fs::create_dir_all(&root).unwrap();
    let query = verify::pure_query(a, z).unwrap();
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
fn total_division_has_distinct_smt_operators_and_explicit_zero_cases() {
    for (op, term) in [
        (B::UDiv, "bvudiv"),
        (B::URem, "bvurem"),
        (B::SDiv, "bvsdiv"),
        (B::SRem, "bvsrem"),
    ] {
        let query = verify::pure_query(&b(op, r(0), r(1)), &c(0)).unwrap();
        assert!(query.smt2().contains(term));
        for a in [0, 1, 1 << 63, u64::MAX] {
            assert_eq!(op.evaluate(a, 0), division_value(op, a, 0));
        }
    }
}

#[test]
#[ignore = "requires Z3; set NIRVANA_Z3"]
fn total_division_definitions_zero_edges_and_unsafe_rewrites_have_solver_checks() {
    let solver = Solver::new(std::env::var("NIRVANA_Z3").unwrap_or_else(|_| "z3".into()));
    let mut equal = vec![
        ("unsigned-zero", b(B::UDiv, r(0), c(0)), c(u64::MAX)),
        ("unsigned-rem-zero", b(B::URem, r(0), c(0)), r(0)),
        (
            "signed-zero",
            b(B::SDiv, r(0), c(0)),
            Expr::select(b(B::Shr, r(0), c(63)), c(1), c(u64::MAX)),
        ),
        ("signed-rem-zero", b(B::SRem, r(0), c(0)), r(0)),
        (
            "signed-negative-one",
            b(B::SDiv, r(0), c(u64::MAX)),
            b(B::Sub, c(0), r(0)),
        ),
        (
            "signed-rem-negative-one",
            b(B::SRem, r(0), c(u64::MAX)),
            c(0),
        ),
    ];
    for op in [B::UDiv, B::URem, B::SDiv, B::SRem] {
        equal.push((
            match op {
                B::UDiv => "udiv-one",
                B::URem => "urem-one",
                B::SDiv => "sdiv-one",
                _ => "srem-one",
            },
            b(op, r(0), c(1)),
            if matches!(op, B::UDiv | B::SDiv) {
                r(0)
            } else {
                c(0)
            },
        ));
    }
    for (name, a, z) in &equal {
        assert_eq!(
            save(name, a, z, &solver),
            Verdict::EquivalentUnderModel,
            "{name}"
        );
    }
    // Four sign cases partition the complete 64-bit domain. Explicit sign
    // bits let the solver simplify the standard's conditional definition
    // before bit-blasting a symbolic division circuit.
    for negative_a in [false, true] {
        for negative_b in [false, true] {
            let input = |reg, negative| {
                if negative {
                    b(B::Or, r(reg), c(1 << 63))
                } else {
                    b(B::And, r(reg), c(i64::MAX as u64))
                }
            };
            let a = input(0, negative_a);
            let z = input(1, negative_b);
            let ma = if negative_a {
                b(B::Sub, c(0), a.clone())
            } else {
                a.clone()
            };
            let mz = if negative_b {
                b(B::Sub, c(0), z.clone())
            } else {
                z.clone()
            };
            for rem in [false, true] {
                let expected = b(if rem { B::URem } else { B::UDiv }, ma.clone(), mz.clone());
                let expected = if if rem {
                    negative_a
                } else {
                    negative_a ^ negative_b
                } {
                    b(B::Sub, c(0), expected)
                } else {
                    expected
                };
                let name = format!("definition-negative-{negative_a}-{negative_b}-rem-{rem}");
                assert_eq!(
                    save(
                        &name,
                        &b(if rem { B::SRem } else { B::SDiv }, a.clone(), z.clone()),
                        &expected,
                        &solver
                    ),
                    Verdict::EquivalentUnderModel,
                    "{name}"
                );
            }
        }
    }
    for (name, a, z) in [
        ("wrong-unsigned-self", b(B::UDiv, r(0), r(0)), c(1)),
        ("wrong-signed-self", b(B::SDiv, r(0), r(0)), c(1)),
        ("wrong-signed-zero", b(B::SDiv, r(0), c(0)), c(u64::MAX)),
    ] {
        let Verdict::Counterexample(w) = save(name, &a, &z, &solver) else {
            panic!("missing replayed counterexample: {name}")
        };
        assert_ne!(w.before, w.after);
    }
    println!(
        "{} universal total-division identities and 3 replayed SAT controls",
        equal.len() + 8
    );
}

#[test]
#[ignore = "requires Z3; set NIRVANA_Z3"]
fn every_selected_byte_kernel_matches_canonical_division_over_all_register_bits() {
    let solver = Solver::new(std::env::var("NIRVANA_Z3").unwrap_or_else(|_| "z3".into()));
    let width = Width::U8;
    let mut count = 0;
    for (d, s) in cases(width) {
        for neg in [false, true] {
            let d = if neg { -d } else { d };
            for split in [false, true] {
                let q = kernel(width, d, s, split, true);
                for rem in [false, true] {
                    let a = if rem {
                        word(b(B::Sub, r(0), b(B::Mul, q.clone(), c(d as u64))), width)
                    } else {
                        q.clone()
                    };
                    let z = word(
                        b(
                            if rem { B::SRem } else { B::SDiv },
                            sext(r(0), width),
                            c(d as u64),
                        ),
                        width,
                    );
                    let name = format!("byte-divisor-{d}-shift-{s}-split-{split}-rem-{rem}");
                    assert_eq!(
                        save(&name, &a, &z, &solver),
                        Verdict::EquivalentUnderModel,
                        "{name}"
                    );
                    count += 1;
                }
            }
        }
    }
    assert_eq!(count, 96);
    println!("{count} universal byte-kernel to canonical IR equivalences");
}

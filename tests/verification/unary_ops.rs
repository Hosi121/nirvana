use crate::support::ir::{c, r, unary_value};
use nirvana::ir::{BinaryOp as B, Expr, UnaryOp as U, Width};
use nirvana::verify::{self, Solver, UnknownReason, Verdict};
const WIDTHS: [Width; 4] = [Width::U8, Width::U16, Width::U32, Width::U64];
fn unary(width: Width, value: Expr) -> Expr {
    Expr::unary(U::SignExtend(width), value)
}
fn expanded(width: Width, value: Expr) -> Expr {
    let sign = c(1u64 << (width.bits() - 1));
    Expr::binary(
        B::Sub,
        Expr::binary(
            B::Xor,
            Expr::binary(B::And, value, c(width.mask())),
            sign.clone(),
        ),
        sign,
    )
}

#[test]
fn extension_proofs_keep_memory_and_nested_expression_limits_explicit() {
    let load = unary(Width::U8, Expr::load(c(0), Width::U64));
    assert_eq!(
        verify::pure_query(&load, &c(0)).unwrap_err(),
        UnknownReason::MemoryExpression
    );
    let mut deep = r(0);
    for _ in 0..258 {
        deep = unary(Width::U8, deep);
    }
    assert_eq!(
        verify::pure_query(&deep, &r(0)).unwrap_err(),
        UnknownReason::ResourceLimit
    );
    for width in WIDTHS {
        let q = verify::pure_query(&unary(width, r(0)), &expanded(width, r(0))).unwrap();
        assert_eq!(q.register_indices(), &[0]);
        if width != Width::U64 {
            assert!(
                q.smt2()
                    .contains(&format!("(_ sign_extend {})", 64 - width.bits()))
            );
        }
    }
}

#[test]
#[ignore = "requires Z3; set NIRVANA_Z3"]
fn all_word_extensions_and_nested_widths_have_universal_checks_and_replayed_mutants() {
    let solver = Solver::new(std::env::var("NIRVANA_Z3").unwrap_or_else(|_| "z3".into()));
    let root =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("target/verification/sign-extend");
    std::fs::create_dir_all(&root).unwrap();
    let mut equal = 0;
    let mut broken = 0;
    let save = |name: &str, a: &Expr, b: &Expr| {
        let query = verify::pure_query(a, b).unwrap();
        std::fs::write(
            root.join(format!("{name}.smt2")),
            format!("{}(check-sat)\n", query.smt2()),
        )
        .unwrap();
        let verdict = solver.check_query(&query);
        std::fs::write(root.join(format!("{name}.out")), format!("{verdict:?}\n")).unwrap();
        verdict
    };
    for width in WIDTHS {
        let a = unary(width, r(0));
        let b = expanded(width, r(0));
        assert_eq!(
            save(&format!("width-{}", width.bits()), &a, &b),
            Verdict::EquivalentUnderModel
        );
        equal += 1;
        for inner in WIDTHS {
            let nested = unary(width, unary(inner, r(0)));
            let simplified = nirvana::simplify::simplify(&nested);
            let expected = if width.min(inner) == Width::U64 {
                r(0)
            } else {
                unary(width.min(inner), r(0))
            };
            assert_eq!(simplified, expected);
            assert_eq!(
                save(
                    &format!("nested-{}-{}", width.bits(), inner.bits()),
                    &nested,
                    &simplified
                ),
                Verdict::EquivalentUnderModel
            );
            equal += 1;
        }
        if width == Width::U64 {
            continue;
        }
        let wrong = Expr::binary(B::And, r(0), c(width.mask()));
        let Verdict::Counterexample(witness) = save(
            &format!("zero-extended-mutant-{}", width.bits()),
            &a,
            &wrong,
        ) else {
            panic!("a wrong unsigned extension needs a replayed witness")
        };
        let x = witness
            .registers
            .iter()
            .find(|(reg, _)| reg.0 == 0)
            .unwrap()
            .1;
        assert_eq!(witness.before, unary_value(U::SignExtend(width), x));
        assert_eq!(witness.after, x & width.mask());
        assert_ne!(witness.before, witness.after);
        broken += 1;
    }
    assert_eq!((equal, broken), (20, 3));
    println!(
        "{equal} universal sign-extension equivalences; {broken} replayed zero-extension mutants"
    );
}

#[test]
#[ignore = "requires Z3; set NIRVANA_Z3"]
fn all_static_slices_have_universal_checks_and_replayed_offset_mutants() {
    let solver = Solver::new(std::env::var("NIRVANA_Z3").unwrap_or_else(|_| "z3".into()));
    let root =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("target/verification/bit-slices");
    std::fs::create_dir_all(&root).unwrap();
    let expanded = |start: u8, width: Width| {
        if start >= 64 {
            Expr::binary(B::And, r(0), c(0))
        } else {
            Expr::binary(
                B::And,
                Expr::binary(B::Shr, r(0), c(u64::from(start))),
                c(width.mask()),
            )
        }
    };
    let save = |name: &str, a: &Expr, b: &Expr| {
        let query = verify::pure_query(a, b).unwrap();
        std::fs::write(
            root.join(format!("{name}.smt2")),
            format!("{}(check-sat)\n", query.smt2()),
        )
        .unwrap();
        let verdict = solver.check_query(&query);
        std::fs::write(root.join(format!("{name}.out")), format!("{verdict:?}\n")).unwrap();
        verdict
    };
    let mut equal = 0;
    for width in WIDTHS {
        for start in 0..=255 {
            let a = Expr::unary(U::Extract { start, width }, r(0));
            assert_eq!(
                save(
                    &format!("slice-{}-{start}", width.bits()),
                    &a,
                    &expanded(start, width)
                ),
                Verdict::EquivalentUnderModel
            );
            equal += 1;
        }
    }
    let high_byte = Expr::unary(
        U::Extract {
            start: 8,
            width: Width::U8,
        },
        r(0),
    );
    let mutants = [
        (
            "masked-offset-64",
            Expr::unary(
                U::Extract {
                    start: 64,
                    width: Width::U64,
                },
                r(0),
            ),
            r(0),
        ),
        ("wrong-high-byte", high_byte.clone(), expanded(7, Width::U8)),
        (
            "signed-high-byte",
            high_byte.clone(),
            Expr::unary(U::SignExtend(Width::U8), high_byte),
        ),
    ];
    for (name, a, b) in mutants {
        let Verdict::Counterexample(w) = save(name, &a, &b) else {
            panic!("missing replayed slice witness {name}")
        };
        assert_ne!(w.before, w.after);
    }
    assert_eq!(equal, 1024);
    println!(
        "{equal} universal static-slice equivalences; 3 IR-replayed offset/signedness SAT controls"
    );
}

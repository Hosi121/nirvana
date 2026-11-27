//! Actual identity predicates against the independent full-word expression SMT.
use super::*;

fn query(out: &Path, solver: &Solver, name: &str, before: Expr, after: Expr, equal: bool) {
    let query = verify::pure_query(&before, &after).unwrap();
    std::fs::write(
        out.join(format!("{name}.smt2")),
        format!("{}(check-sat)\n", query.smt2()),
    )
    .unwrap();
    let result = solver.check_query(&query);
    std::fs::write(out.join(format!("{name}.out")), format!("{result:?}\n")).unwrap();
    if equal {
        assert_eq!(result, Verdict::EquivalentUnderModel, "{name}");
    } else {
        let Verdict::Counterexample(witness) = result else {
            panic!("missing replayed counterexample {name}: {result:?}")
        };
        assert_ne!(witness.before, witness.after, "{name}");
    }
}

#[test]
#[ignore = "requires NIRVANA_Z3 and NIRVANA_BITS_CHECK_OUT managed directory"]
fn actual_partial_bit_identity_rules_have_full_word_proofs_and_negative_controls() {
    let out = std::path::PathBuf::from(std::env::var_os("NIRVANA_BITS_CHECK_OUT").unwrap())
        .join("identities");
    assert!(!out.exists());
    std::fs::create_dir_all(&out).unwrap();
    let solver = Solver::new(std::env::var("NIRVANA_Z3").unwrap());
    let masks = [
        1,
        3,
        255,
        65535,
        u64::from(u32::MAX),
        1 << 63,
        0x5555_aaaa_1111_8888,
        u64::MAX,
    ];
    let mut proved = 0;
    let mut rejected = 0;
    for (case, mask) in masks.into_iter().enumerate() {
        let bounded = K::new(!mask, 0).unwrap();
        let ones = K::new(0, mask).unwrap();
        for (op, a, z) in [(B::And, bounded, ones), (B::Or, ones, bounded)] {
            for keep_left in [true, false] {
                let (a, z) = if keep_left { (a, z) } else { (z, a) };
                assert!(kernel::binary_identity(op, a, z, keep_left));
                let x = input(0, a);
                let y = input(1, z);
                let retained = if keep_left { x.clone() } else { y.clone() };
                query(
                    &out,
                    &solver,
                    &format!("binary-{case}-{op:?}-{keep_left}"),
                    b(op, x, y),
                    retained,
                    true,
                );
                proved += 1;
            }
        }
        let bit = mask & mask.wrapping_neg();
        for (op, a, z) in [
            (B::And, bounded, K::new(bit, mask ^ bit).unwrap()),
            (B::Or, K::new(bit, mask ^ bit).unwrap(), bounded),
        ] {
            assert!(!kernel::binary_identity(op, a, z, true));
            let x = input(0, a);
            let y = input(1, z);
            query(
                &out,
                &solver,
                &format!("missing-bit-{case}-{op:?}"),
                b(op, x.clone(), y),
                x,
                false,
            );
            rejected += 1;
        }
    }
    for (case, width) in [Width::U8, Width::U16, Width::U32, Width::U64]
        .into_iter()
        .enumerate()
    {
        let sign = 1u64 << (width.bits() - 1);
        for (name, op, fact) in [
            (
                "extract",
                U::Extract { start: 0, width },
                K::new(!width.mask(), 0).unwrap(),
            ),
            (
                "positive-sign",
                U::SignExtend(width),
                K::new(!(sign - 1), 0).unwrap(),
            ),
            (
                "negative-sign",
                U::SignExtend(width),
                K::new(0, !(sign - 1)).unwrap(),
            ),
        ] {
            assert!(kernel::unary_identity(op, fact));
            let value = input(0, fact);
            query(
                &out,
                &solver,
                &format!("unary-{case}-{name}"),
                Expr::unary(op, value.clone()),
                value,
                true,
            );
            proved += 1;
        }
        if width != Width::U64 {
            for (name, op, fact) in [
                ("upper-bit", U::Extract { start: 0, width }, K::UNKNOWN),
                (
                    "unknown-sign",
                    U::SignExtend(width),
                    K::new(!width.mask(), 0).unwrap(),
                ),
            ] {
                assert!(!kernel::unary_identity(op, fact));
                let value = input(0, fact);
                query(
                    &out,
                    &solver,
                    &format!("wrong-unary-{case}-{name}"),
                    Expr::unary(op, value.clone()),
                    value,
                    false,
                );
                rejected += 1;
            }
        }
    }
    assert_eq!((proved, rejected), (44, 22));
    std::fs::write(
        out.join("summary.json"),
        format!("{{\"full_u64_unsat\":{proved},\"ir_replayed_sat\":{rejected}}}\n"),
    )
    .unwrap();
    println!("{proved} identity-rule full-u64 UNSAT; {rejected} IR-replayed SAT controls");
}

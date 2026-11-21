use crate::support::ir::{c, insert_value, r};
use nirvana::ir::{BinaryOp as B, Expr, Width};
use nirvana::verify::{self, Solver, Verdict};
fn b(op: B, a: Expr, z: Expr) -> Expr {
    Expr::binary(op, a, z)
}
#[test]
#[ignore = "requires Z3; set NIRVANA_Z3"]
fn every_insert_has_a_universal_mask_equivalence_and_replayed_controls() {
    let solver = Solver::new(std::env::var("NIRVANA_Z3").unwrap_or_else(|_| "z3".into()));
    let root =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("target/verification/bit-insert");
    std::fs::create_dir_all(&root).unwrap();
    let save = |name: &str, a: &Expr, z: &Expr| {
        let query = verify::pure_query(a, z).unwrap();
        std::fs::write(
            root.join(format!("{name}.smt2")),
            format!("{}(check-sat)\n", query.smt2()),
        )
        .unwrap();
        let result = solver.check_query(&query);
        std::fs::write(root.join(format!("{name}.out")), format!("{result:?}\n")).unwrap();
        result
    };
    let mut proved = 0;
    for width in [Width::U8, Width::U16, Width::U32, Width::U64] {
        for start in 0..=255u8 {
            let before = b(B::Insert { start, width }, r(0), r(1));
            let mask = (((1u128 << width.bits()) - 1)
                .checked_shl(u32::from(start))
                .unwrap_or(0)) as u64;
            let after = if start >= 64 {
                b(B::Or, r(0), b(B::And, r(1), c(0)))
            } else {
                b(
                    B::Or,
                    b(B::And, r(0), c(!mask)),
                    b(B::And, b(B::Shl, r(1), c(u64::from(start))), c(mask)),
                )
            };
            assert_eq!(
                save(&format!("insert-{}-{start}", width.bits()), &before, &after),
                Verdict::EquivalentUnderModel
            );
            proved += 1;
        }
    }
    let mut projected = 0;
    for width in [Width::U8, Width::U16, Width::U32, Width::U64] {
        for start in [0, 8, 63, 64, 255] {
            for left_mask in [0, 255, 65535, u32::MAX as u64, u64::MAX] {
                for right_mask in [0, 255, 65535, u32::MAX as u64, u64::MAX] {
                    let before = b(
                        B::Insert { start, width },
                        b(B::And, r(0), c(left_mask)),
                        b(B::And, r(1), c(right_mask)),
                    );
                    let after = nirvana::presentation::normalize(&before, |_| Width::U64);
                    assert_eq!(
                        save(
                            &format!("display-{}-{start}-{left_mask}-{right_mask}", width.bits()),
                            &before,
                            &after
                        ),
                        Verdict::EquivalentUnderModel
                    );
                    projected += 1;
                }
            }
        }
    }
    let cases = [
        (
            "masked-offset",
            64,
            Width::U8,
            b(
                B::Insert {
                    start: 0,
                    width: Width::U8,
                },
                r(0),
                r(1),
            ),
        ),
        ("dropped-base", 0, Width::U8, b(B::And, r(1), c(255))),
        (
            "eax-is-insert32",
            0,
            Width::U32,
            b(B::And, r(1), c(u32::MAX as u64)),
        ),
    ];
    for (name, start, width, bad) in cases {
        let before = b(B::Insert { start, width }, r(0), r(1));
        let Verdict::Counterexample(w) = save(name, &before, &bad) else {
            panic!("missing IR-replayed {name}")
        };
        let input = |index| w.registers.iter().find(|(r, _)| r.0 == index).unwrap().1;
        assert_eq!(w.before, insert_value(start, width, input(0), input(1)));
        assert_ne!(w.before, w.after);
    }
    println!(
        "{proved} universal insert/independent mask equivalences, {projected} actual presentation rewrites and 3 IR-replayed controls"
    );
}

#[test]
#[ignore = "requires Z3; set NIRVANA_Z3"]
fn checked_insert_blocks_keep_unused_operand_faults_and_store_order() {
    let solver = Solver::new(std::env::var("NIRVANA_Z3").unwrap_or_else(|_| "z3".into()));
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("target/verification/bit-insert-blocks");
    std::fs::create_dir_all(&root).unwrap();
    let save = |name: &str,
                source: &nirvana::ir::Program,
                candidate: &nirvana::ir::Program,
                evidence: &nirvana::block_verify::Validation| {
        for block in &evidence.blocks {
            let query = nirvana::block_verify::block_query(
                source,
                candidate,
                block.address,
                &block.shared_inputs,
                &block.required_outputs,
            )
            .unwrap();
            let path = root.join(format!("{name}-{}.smt2", block.address));
            std::fs::write(&path, format!("{}(check-sat)\n", query.smt2())).unwrap();
            std::fs::write(path.with_extension("out"), format!("{:?}\n", block.verdict)).unwrap();
        }
    };
    let mut proved = 0;
    for op in [
        B::Insert {
            start: 0,
            width: Width::U8,
        },
        B::Insert {
            start: 8,
            width: Width::U8,
        },
        B::Insert {
            start: 60,
            width: Width::U16,
        },
        B::Insert {
            start: 64,
            width: Width::U64,
        },
        B::Insert {
            start: 0,
            width: Width::U64,
        },
    ] {
        let source = crate::support::bit_insert::memory_program(op);
        let expanded = crate::support::bit_insert::expanded(&source);
        let evidence = nirvana::block_verify::validate_program(&source, &expanded, &solver);
        save(&format!("{op:?}"), &source, &expanded, &evidence);
        assert!(evidence.accepted(), "{op:?}: {evidence:?}");
        proved += evidence.blocks.len();
    }
    use nirvana::ir::{Control, IrInstruction, Program};
    let source = Program::new(
        0,
        2,
        vec![IrInstruction {
            address: 0,
            size: 1,
            assignments: vec![],
            control: Control::Return(b(
                B::Insert {
                    start: 64,
                    width: Width::U64,
                },
                Expr::load(r(0), Width::U8),
                Expr::load(r(1), Width::U8),
            )),
        }],
    )
    .unwrap();
    let bad = Program::new(
        0,
        2,
        vec![IrInstruction {
            address: 0,
            size: 1,
            assignments: vec![],
            control: Control::Return(Expr::load(r(0), Width::U8)),
        }],
    )
    .unwrap();
    let evidence = nirvana::block_verify::validate_program(&source, &bad, &solver);
    save("dropped-rhs-fault", &source, &bad, &evidence);
    assert!(
        evidence.blocks.iter().any(|b| matches!(
            b.verdict,
            nirvana::block_verify::BlockVerdict::Counterexample(_)
        )),
        "{evidence:?}"
    );
    println!(
        "{proved} universal checked-memory insert blocks, 1 IR-replayed dropped-RHS-fault control"
    );
}

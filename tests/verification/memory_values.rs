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

#[test]
#[ignore = "requires Z3; set NIRVANA_Z3"]
fn actual_reaching_byte_candidates_preserve_checked_block_observations() {
    use nirvana::block_verify::{self, BlockVerdict};
    use nirvana::ir::{Assignment, Control, IrInstruction, Place, Program, Reg};
    let solver = Solver::new(std::env::var("NIRVANA_Z3").unwrap_or_else(|_| "z3".into()));
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("target/verification/byte-memory-values");
    std::fs::create_dir_all(&root).unwrap();
    let mut proved = 0;
    for write in [Width::U8, Width::U16, Width::U32, Width::U64] {
        for read in [Width::U8, Width::U16, Width::U32, Width::U64] {
            for offset in 0..=8usize {
                if offset + read.bytes() > write.bytes() {
                    continue;
                }
                let source = Program::new(
                    0,
                    8,
                    vec![
                        IrInstruction {
                            address: 0,
                            size: 1,
                            assignments: vec![
                                Assignment {
                                    destination: Place::Memory {
                                        address: r(7),
                                        width: write,
                                    },
                                    value: r(0),
                                },
                                Assignment {
                                    destination: Reg(0).into(),
                                    value: c(0),
                                },
                            ],
                            control: Control::Next,
                        },
                        IrInstruction {
                            address: 1,
                            size: 1,
                            assignments: vec![Assignment {
                                destination: Reg(2).into(),
                                value: Expr::load(b(B::Add, r(7), c(offset as u64)), read),
                            }],
                            control: Control::Return(r(2)),
                        },
                    ],
                )
                .unwrap();
                let plan = nirvana::memory_values::MemoryValuePlan::analyze(&source).unwrap();
                let candidate = plan.lower(&source).unwrap();
                let prefix: Vec<_> = (0..8).map(Reg).collect();
                let query =
                    block_verify::block_query(&source, &candidate, 0, &prefix, &prefix).unwrap();
                let name = format!("word-{}-{}-{offset}", write.bits(), read.bits());
                std::fs::write(
                    root.join(format!("{name}.smt2")),
                    format!("{}(check-sat)\n", query.smt2()),
                )
                .unwrap();
                let verdict = query.check(&solver);
                std::fs::write(root.join(format!("{name}.out")), format!("{verdict:?}\n")).unwrap();
                assert_eq!(verdict, BlockVerdict::EquivalentUnderModel, "{name}");
                proved += 1;
                if write == Width::U32 && read == Width::U16 && offset == 1 {
                    let mut rows = candidate.instructions().to_vec();
                    let Control::Return(Expr::Unary(U::Extract { start, .. }, _)) =
                        &mut rows[1].control
                    else {
                        panic!("actual return must use the captured word projection")
                    };
                    *start += 8;
                    let bad = Program::new(0, candidate.register_count(), rows).unwrap();
                    assert!(nirvana::memory_values::validate(&source, &plan, &bad).is_err());
                    let query =
                        block_verify::block_query(&source, &bad, 0, &prefix, &prefix).unwrap();
                    std::fs::write(
                        root.join("wrong-byte.smt2"),
                        format!("{}(check-sat)\n", query.smt2()),
                    )
                    .unwrap();
                    let verdict = query.check(&solver);
                    std::fs::write(root.join("wrong-byte.out"), format!("{verdict:?}\n")).unwrap();
                    assert!(
                        matches!(verdict, BlockVerdict::Counterexample(_)),
                        "{verdict:?}"
                    );
                }
            }
        }
    }
    println!(
        "{proved} universal actual store/load-to-snapshot block checks; 1 IR-replayed wrong-byte SAT control"
    );
}

#[test]
#[ignore = "requires Z3; set NIRVANA_Z3"]
fn actual_split_ssa_producers_have_checked_memory_proofs() {
    use nirvana::block_verify::{self, BlockVerdict};
    use nirvana::ir::{Control, Program, Reg};
    let solver = Solver::new(std::env::var("NIRVANA_Z3").unwrap_or_else(|_| "z3".into()));
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("target/verification/ssa-byte-origins");
    std::fs::create_dir_all(&root).unwrap();
    let prefix: Vec<_> = (0..8).map(Reg).collect();
    for (i, source) in crate::support::byte_values::producer_programs()
        .into_iter()
        .enumerate()
    {
        let plan = nirvana::memory_values::MemoryValuePlan::analyze(&source).unwrap();
        assert_eq!(plan.evidence().snapshot_values, 1);
        let candidate = plan.lower(&source).unwrap();
        let query = block_verify::block_query(&source, &candidate, 0, &prefix, &prefix).unwrap();
        std::fs::write(
            root.join(format!("producer-{i}.smt2")),
            format!("{}(check-sat)\n", query.smt2()),
        )
        .unwrap();
        let verdict = query.check(&solver);
        std::fs::write(
            root.join(format!("producer-{i}.out")),
            format!("{verdict:?}\n"),
        )
        .unwrap();
        assert_eq!(verdict, BlockVerdict::EquivalentUnderModel);
        if i == 0 {
            let mut rows = candidate.instructions().to_vec();
            let Control::Return(Expr::Unary(U::Extract { start, .. }, _)) = &mut rows[2].control
            else {
                panic!("captured projection")
            };
            *start += 1;
            let bad = Program::new(0, candidate.register_count(), rows).unwrap();
            assert!(nirvana::memory_values::validate(&source, &plan, &bad).is_err());
            let query = block_verify::block_query(&source, &bad, 0, &prefix, &prefix).unwrap();
            std::fs::write(
                root.join("wrong-ssa-bit.smt2"),
                format!("{}(check-sat)\n", query.smt2()),
            )
            .unwrap();
            let verdict = query.check(&solver);
            std::fs::write(root.join("wrong-ssa-bit.out"), format!("{verdict:?}\n")).unwrap();
            assert!(
                matches!(verdict, BlockVerdict::Counterexample(_)),
                "{verdict:?}"
            );
        }
    }
    println!(
        "5 universal actual SSA producer/RAM/first-fault proofs; 1 IR-replayed wrong-bit SAT control"
    );
}

#[test]
#[ignore = "requires Z3; set NIRVANA_Z3"]
fn actual_loop_exit_captures_preserve_checked_block_observations() {
    use nirvana::block_verify::{self, BlockVerdict};
    use nirvana::ir::Reg;
    let solver = Solver::new(std::env::var("NIRVANA_Z3").unwrap_or_else(|_| "z3".into()));
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("target/verification/post-loop-values");
    std::fs::create_dir_all(&root).unwrap();
    let prefix: Vec<_> = (0..8).map(Reg).collect();
    for (i, source) in crate::support::byte_values::after_loop_programs()
        .into_iter()
        .enumerate()
    {
        let plan = nirvana::memory_values::MemoryValuePlan::analyze(&source).unwrap();
        let candidate = plan.lower(&source).unwrap();
        let query = block_verify::block_query(&source, &candidate, 2, &prefix, &prefix).unwrap();
        std::fs::write(
            root.join(format!("exit-{i}.smt2")),
            format!("{}(check-sat)\n", query.smt2()),
        )
        .unwrap();
        let verdict = query.check(&solver);
        std::fs::write(root.join(format!("exit-{i}.out")), format!("{verdict:?}\n")).unwrap();
        assert_eq!(verdict, BlockVerdict::EquivalentUnderModel);
    }
}

#[test]
#[ignore = "requires Z3; set NIRVANA_Z3"]
fn actual_pure_store_expression_captures_have_checked_memory_proofs() {
    use nirvana::block_verify::{self, BlockVerdict};
    use nirvana::ir::{Program, Reg};
    let solver = Solver::new(std::env::var("NIRVANA_Z3").unwrap_or_else(|_| "z3".into()));
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("target/verification/store-expressions");
    std::fs::create_dir_all(&root).unwrap();
    let prefix: Vec<_> = (0..8).map(Reg).collect();
    for (i, source) in crate::support::byte_values::stored_expression_programs()
        .into_iter()
        .enumerate()
    {
        let plan = nirvana::memory_values::MemoryValuePlan::analyze(&source).unwrap();
        assert_eq!(plan.evidence().snapshot_values, 1);
        let candidate = plan.lower(&source).unwrap();
        let query = block_verify::block_query(&source, &candidate, 0, &prefix, &prefix).unwrap();
        std::fs::write(
            root.join(format!("expression-{i}.smt2")),
            format!("{}(check-sat)\n", query.smt2()),
        )
        .unwrap();
        let verdict = query.check(&solver);
        std::fs::write(
            root.join(format!("expression-{i}.out")),
            format!("{verdict:?}\n"),
        )
        .unwrap();
        assert_eq!(
            verdict,
            BlockVerdict::EquivalentUnderModel,
            "expression {i}"
        );
        if i == 0 {
            let mut rows = candidate.instructions().to_vec();
            let capture = rows[1]
                .assignments
                .iter_mut()
                .find(|a| matches!(a.destination,nirvana::ir::Place::Register(r) if r.0>=8))
                .unwrap();
            capture.value = b(B::Add, capture.value.clone(), c(256));
            let bad = Program::new(0, candidate.register_count(), rows).unwrap();
            assert!(nirvana::memory_values::validate(&source, &plan, &bad).is_err());
            let query = block_verify::block_query(&source, &bad, 0, &prefix, &prefix).unwrap();
            std::fs::write(
                root.join("wrong-capture.smt2"),
                format!("{}(check-sat)\n", query.smt2()),
            )
            .unwrap();
            let verdict = query.check(&solver);
            std::fs::write(root.join("wrong-capture.out"), format!("{verdict:?}\n")).unwrap();
            assert!(
                matches!(verdict, BlockVerdict::Counterexample(_)),
                "{verdict:?}"
            );
        }
    }
    println!(
        "6 universal actual pure-Store expression/RAM/first-fault proofs; 1 IR-replayed wrong-capture SAT control"
    );
}

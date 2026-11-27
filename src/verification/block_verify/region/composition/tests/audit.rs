//! Compare real Rust cut certificates with an independent flat legacy encoding.
use super::super::super::{build_query_encoded, encode, observations::Observations};
use super::*;

fn program(seed: u64, mutation: usize, after: bool) -> Program {
    let base = if after { 100 } else { 0 };
    let width = [Width::U8, Width::U16, Width::U32, Width::U64][seed as usize % 4];
    let bias = seed.wrapping_mul(0x9e3779b97f4a7c15).rotate_left(17);
    let offset = (seed >> 7) & 7;
    let address = add(r(1), offset);
    let initial = Expr::binary(
        [BinaryOp::Xor, BinaryOp::Add, BinaryOp::Sub, BinaryOp::And][((seed >> 5) & 3) as usize],
        r(0),
        Expr::Const(seed.rotate_right(7)),
    );
    let value = if after { add(r(2), bias) } else { r(3) };
    let load = || Expr::load(address.clone(), width);
    let condition = if after && mutation == 5 {
        Expr::Const(0)
    } else if seed & 8 != 0 {
        Expr::select(
            Expr::binary(BinaryOp::And, r(0), Expr::Const(1)),
            load(),
            Expr::Const(0),
        )
    } else {
        load()
    };
    let store = |extra: u64| Assignment {
        destination: Place::Memory {
            address: add(address.clone(), extra),
            width,
        },
        value: add(value.clone(), if after && mutation == 2 { 1 } else { 0 }),
    };
    let returned = if seed & 16 == 0 { u64::MAX } else { 9 };
    let instruction = |pc, assignments, control| IrInstruction {
        address: base + pc,
        size: 1,
        assignments,
        control,
    };
    Program::new(
        base,
        4,
        vec![
            instruction(
                0,
                vec![
                    set(2, initial),
                    set(
                        3,
                        add(r(2), bias.wrapping_add(u64::from(after && mutation == 1))),
                    ),
                ],
                Control::Jump(base + 10),
            ),
            instruction(
                10,
                vec![],
                Control::Branch {
                    condition,
                    target: base + if seed & 4 != 0 { 11 } else { 14 },
                },
            ),
            instruction(11, vec![store(0)], Control::Jump(base + 20)),
            instruction(
                14,
                vec![store(width.bytes() as u64)],
                Control::Jump(base + 20),
            ),
            instruction(
                20,
                vec![set(
                    2,
                    add(
                        Expr::binary(BinaryOp::Add, value, load()),
                        u64::from(after && mutation == 3),
                    ),
                )],
                Control::Return(Expr::Const(returned ^ u64::from(after && mutation == 4))),
            ),
        ],
    )
    .unwrap()
}

fn plan(seed: u64) -> Vec<Cut> {
    let bias = seed.wrapping_mul(0x9e3779b97f4a7c15).rotate_left(17);
    let mut cuts = vec![Cut {
        before: 0,
        after: 100,
        shared: vec![Reg(0), Reg(1)],
        before_invariants: vec![],
        after_invariants: vec![],
    }];
    for pc in [10, 20] {
        cuts.push(Cut {
            before: pc,
            after: pc + 100,
            shared: vec![Reg(0), Reg(1), Reg(2)],
            before_invariants: vec![set(3, add(r(2), bias))],
            after_invariants: vec![set(3, add(r(2), bias))],
        });
    }
    cuts
}

#[test]
#[ignore = "requires NIRVANA_Z3; all-word/all-RAM differential composition audit"]
fn generated_cut_certificates_agree_with_flat_legacy_queries() {
    let seeds: usize = std::env::var("NIRVANA_COMPOSITION_AUDIT_SEEDS")
        .unwrap_or_else(|_| "64".into())
        .parse()
        .unwrap();
    assert!((1..=512).contains(&seeds));
    let solver =
        Solver::new(std::env::var("NIRVANA_Z3").unwrap()).with_timeout(Duration::from_secs(3));
    let mut certified = 0;
    let mut conservative = 0;
    let mut rejected = 0;
    let start = Instant::now();
    for seed in 0..seeds as u64 {
        let before = program(seed, 0, false);
        for mutation in 0..6 {
            let after = program(seed, mutation, true);
            let original = query(&before, &after, &[Reg(0), Reg(1)], &[Reg(2)]).unwrap();
            let problem = Problem::new(&original, &plan(seed)).unwrap();
            let outcome = problem.check(&solver, Duration::from_secs(5));
            let flat = build_query_encoded(
                &before,
                &after,
                &[Reg(0), Reg(1)],
                Observations::uniform(&[Reg(2)]).unwrap(),
                encode::reference_dag,
                encode::reference_dag,
            )
            .unwrap();
            let oracle = flat.check(&solver);
            let okay = match (&outcome, &oracle, mutation) {
                (Outcome::Verified(seal), Verdict::EquivalentUnderModel, 0) => {
                    assert!(seal.matches(&original));
                    certified += 1;
                    true
                }
                (Outcome::Unproved(failure), Verdict::EquivalentUnderModel, 1)
                    if matches!(failure.verdict, Verdict::Counterexample(_)) =>
                {
                    conservative += 1;
                    true
                }
                (Outcome::Unproved(failure), Verdict::Counterexample(_), 2..=5)
                    if matches!(failure.verdict, Verdict::Counterexample(_)) =>
                {
                    rejected += 1;
                    true
                }
                _ => false,
            };
            if !okay {
                if let Some(directory) = std::env::var_os("NIRVANA_COMPOSITION_AUDIT_OUTPUT") {
                    let directory = std::path::PathBuf::from(directory);
                    std::fs::create_dir_all(&directory).unwrap();
                    std::fs::write(directory.join("original.smt2"), original.smt2()).unwrap();
                    std::fs::write(directory.join("flat-legacy.smt2"), flat.smt2()).unwrap();
                    std::fs::write(directory.join("sources.txt"),format!("seed={seed} mutation={mutation}\nbefore={:#?}\nafter={:#?}\ncuts={:#?}\n",before.instructions(),after.instructions(),plan(seed))).unwrap();
                    for (n, obligation) in problem.obligations().iter().enumerate() {
                        std::fs::write(
                            directory.join(format!("local-{n}.smt2")),
                            obligation.query().smt2(),
                        )
                        .unwrap();
                    }
                }
                let local = match outcome {
                    Outcome::Verified(_) => "verified".to_string(),
                    Outcome::Unproved(f) => format!(
                        "unproved cut={} kind={:?} verdict={}",
                        f.cut,
                        f.kind,
                        match f.verdict {
                            Verdict::Counterexample(_) => "local counterexample",
                            Verdict::Unknown(_) => "unknown",
                            Verdict::EquivalentUnderModel => "equivalent",
                        }
                    ),
                };
                let flat = match oracle {
                    Verdict::EquivalentUnderModel => "equivalent".to_string(),
                    Verdict::Counterexample(_) => "counterexample".to_string(),
                    Verdict::Unknown(r) => format!("unknown {r:?}"),
                };
                panic!("seed={seed} mutation={mutation} local={local} flat={flat}");
            }
        }
        if (seed + 1) % 16 == 0 {
            println!(
                "COMPOSITION-AUDIT progress={} total={} certified={certified} conservative={conservative} rejected={rejected} ms={}",
                seed + 1,
                seeds,
                start.elapsed().as_millis()
            );
        }
    }
    assert_eq!(certified, seeds);
    assert_eq!(conservative, seeds);
    assert_eq!(rejected, 4 * seeds);
    println!(
        "COMPOSITION-AUDIT complete seeds={seeds} variants=6 cases={} certificates={certified} conservative_equal={conservative} semantic_mutants_replayed={rejected} arbitrary_words=true arbitrary_ram=true legacy_flat=true ms={}",
        6 * seeds,
        start.elapsed().as_millis()
    );
}

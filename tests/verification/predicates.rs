use crate::support::pure_prefix as model;
use nirvana::{
    ir::{Assignment, BinaryOp as B, Control, Expr, IrInstruction, Program, Reg},
    predicates::{self, PredicatePlan},
    verify::{self, Solver, Verdict},
};

fn r(n: usize) -> Expr {
    Expr::Register(Reg(n))
}
fn c(n: u64) -> Expr {
    Expr::Const(n)
}
fn b(op: B, a: Expr, z: Expr) -> Expr {
    Expr::binary(op, a, z)
}
fn set(n: usize, value: Expr) -> Assignment {
    Assignment {
        destination: Reg(n).into(),
        value,
    }
}
fn program(rows: Vec<(Vec<Assignment>, Control)>) -> Program {
    Program::new(
        0,
        8,
        rows.into_iter()
            .enumerate()
            .map(|(n, (assignments, control))| IrInstruction {
                address: n as u64,
                size: 1,
                assignments,
                control,
            })
            .collect(),
    )
    .unwrap()
}
fn families() -> Vec<Program> {
    let mut out = Vec::new();
    for condition in [
        b(B::And, r(0), c(1)),
        b(B::Xor, b(B::Eq, b(B::And, r(0), c(255)), c(0)), c(1)),
        b(B::Xor, r(0), c(1)),
        b(B::Ult, b(B::Add, r(0), c(1)), r(1)),
        b(B::Ule, r(0), c(u64::MAX - 2)),
    ] {
        out.push(program(vec![
            (
                vec![],
                Control::Branch {
                    condition: condition.clone(),
                    target: 4,
                },
            ),
            (
                vec![set(2, b(B::Eq, condition.clone(), c(0)))],
                Control::Next,
            ),
            (
                vec![],
                Control::Branch {
                    condition: r(2),
                    target: 5,
                },
            ),
            (vec![], Control::Return(c(99))),
            (vec![], Control::Return(r(1))),
            (
                vec![set(3, Expr::select(condition, r(1), r(0)))],
                Control::Return(r(3)),
            ),
        ]));
    }
    out.push(program(vec![
        (
            vec![],
            Control::Branch {
                condition: r(0),
                target: 2,
            },
        ),
        (vec![set(1, r(2))], Control::Jump(3)),
        (vec![set(1, r(2))], Control::Jump(3)),
        (
            vec![],
            Control::Branch {
                condition: r(1),
                target: 6,
            },
        ),
        (
            vec![],
            Control::Branch {
                condition: r(2),
                target: 7,
            },
        ),
        (vec![], Control::Return(c(0))),
        (vec![], Control::Return(c(1))),
        (vec![], Control::Return(c(2))),
    ]));
    // A new definition has separate truth even after a related path predicate.
    out.push(program(vec![
        (
            vec![],
            Control::Branch {
                condition: r(0),
                target: 5,
            },
        ),
        (
            vec![],
            Control::Branch {
                condition: r(0),
                target: 5,
            },
        ),
        (vec![set(0, r(1))], Control::Next),
        (
            vec![],
            Control::Branch {
                condition: r(0),
                target: 5,
            },
        ),
        (vec![], Control::Return(c(0))),
        (vec![], Control::Return(r(0))),
    ]));
    out
}
fn difference(a: &[Expr], z: &[Expr]) -> Expr {
    assert_eq!(a.len(), z.len());
    a.iter().zip(z).fold(c(0), |out, (a, z)| {
        b(B::Or, out, b(B::Ne, a.clone(), z.clone()))
    })
}

#[test]
fn independent_prefix_model_matches_actual_pure_execution_and_transforms() {
    for source in families() {
        let plan = PredicatePlan::analyze(&source).unwrap();
        let (candidate, _) = plan.lower(&source).unwrap();
        for budget in 0..=source.instructions().len() {
            for program in [&source, &candidate] {
                let symbolic = model::symbolic(program, budget);
                for a in [0, 1, 2, 3, 255, 256, 1 << 63, u64::MAX - 2, u64::MAX] {
                    for z in [0, 1, u64::MAX] {
                        let input = [a, z, a ^ z, 7, 5, 3, 1, 0];
                        let report = program.run_with_memory(&input, 0, &[], budget).unwrap();
                        assert_eq!(
                            symbolic
                                .iter()
                                .map(|e| model::evaluate(e, &input))
                                .collect::<Vec<_>>(),
                            model::concrete(&report, budget)
                        );
                    }
                }
            }
        }
    }
}

#[test]
#[ignore = "requires Z3; set NIRVANA_Z3"]
fn actual_predicate_plans_preserve_all_pure_entry_prefixes_and_replay_a_bad_target() {
    let solver = Solver::new(std::env::var("NIRVANA_Z3").unwrap_or_else(|_| "z3".into()));
    let root =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("target/verification/predicates");
    std::fs::create_dir_all(&root).unwrap();
    let check = |name: &str, a: &[Expr], z: &[Expr]| {
        let query = verify::pure_query(&difference(a, z), &c(0)).unwrap();
        std::fs::write(
            root.join(format!("{name}.smt2")),
            format!(
                "; {} over {}\n{}(check-sat)\n",
                model::MODEL_ID,
                verify::MODEL_ID,
                query.smt2()
            ),
        )
        .unwrap();
        let verdict = solver.check_query(&query);
        std::fs::write(root.join(format!("{name}.out")), format!("{verdict:?}\n")).unwrap();
        verdict
    };
    let mut proved = 0;
    for (family, source) in families().into_iter().enumerate() {
        let plan = PredicatePlan::analyze(&source).unwrap();
        let (candidate, _) = plan.lower(&source).unwrap();
        std::fs::write(
            root.join(format!("{family}.source.txt")),
            format!("{:#?}", source.instructions()),
        )
        .unwrap();
        std::fs::write(
            root.join(format!("{family}.candidate.txt")),
            format!("{:#?}", candidate.instructions()),
        )
        .unwrap();
        for budget in 0..=source.instructions().len() {
            assert_eq!(
                check(
                    &format!("{family}-budget-{budget}"),
                    &model::symbolic(&source, budget),
                    &model::symbolic(&candidate, budget)
                ),
                Verdict::EquivalentUnderModel,
                "family={family}, budget={budget}"
            );
            proved += 1;
        }
        if family == 0 {
            let mut rows = candidate.instructions().to_vec();
            rows[2].control = Control::Jump(4);
            let wrong = Program::new(0, 8, rows).unwrap();
            assert!(predicates::validate(&source, &plan, &wrong).is_err());
            let budget = source.instructions().len();
            let Verdict::Counterexample(w) = check(
                "wrong-target",
                &model::symbolic(&source, budget),
                &model::symbolic(&wrong, budget),
            ) else {
                panic!("missing wrong-target counterexample")
            };
            let mut input = vec![0; 8];
            for (reg, value) in w.registers {
                input[reg.0] = value;
            }
            let expected = source.run_with_memory(&input, 0, &[], budget).unwrap();
            let actual = wrong.run_with_memory(&input, 0, &[], budget).unwrap();
            assert_ne!(expected, actual);
            std::fs::write(
                root.join("wrong-target.replay.txt"),
                format!("input={input:?}\nexpected={expected:?}\nactual={actual:?}\n"),
            )
            .unwrap();
        }
    }
    assert_eq!(proved, 51);
    println!("{proved} universal pure-DAG prefix comparisons; one full-state SAT witness replayed");
}

#[test]
#[ignore = "requires Z3; set NIRVANA_Z3"]
fn actual_masked_load_plans_preserve_checked_memory_and_replay_removed_reads() {
    use nirvana::{
        block_verify::{self, BlockVerdict},
        ir::Width,
    };
    let solver = Solver::new(std::env::var("NIRVANA_Z3").unwrap_or_else(|_| "z3".into()));
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("target/verification/predicate-memory");
    std::fs::create_dir_all(&root).unwrap();
    let path = |p: &Program| {
        let rows = [0, 1, 3]
            .into_iter()
            .enumerate()
            .map(|(n, address)| {
                let mut row = p.instructions()[address].clone();
                row.address = n as u64;
                row.size = 1;
                if !matches!(row.control, Control::Return(_)) {
                    row.control = Control::Next;
                }
                row
            })
            .collect();
        Program::new(0, 8, rows).unwrap()
    };
    for width in [Width::U8, Width::U16, Width::U32, Width::U64] {
        let source = program(vec![
            (
                vec![set(
                    0,
                    b(B::Or, b(B::And, Expr::load(r(7), width), c(0)), c(7)),
                )],
                Control::Next,
            ),
            (
                vec![],
                Control::Branch {
                    condition: r(0),
                    target: 3,
                },
            ),
            (vec![], Control::Return(c(99))),
            (vec![], Control::Return(r(0))),
        ]);
        let plan = PredicatePlan::analyze(&source).unwrap();
        let (candidate, e) = plan.lower(&source).unwrap();
        assert_eq!(e.pruned_branches, 1);
        let regs = (0..8).map(Reg).collect::<Vec<_>>();
        let check = |name: &str, before: &Program, after: &Program| {
            let q =
                block_verify::block_query(&path(before), &path(after), 0, &regs, &regs).unwrap();
            std::fs::write(
                root.join(format!("{name}.smt2")),
                format!("{}(check-sat)\n", q.smt2()),
            )
            .unwrap();
            let v = q.check(&solver);
            std::fs::write(root.join(format!("{name}.out")), format!("{v:?}\n")).unwrap();
            v
        };
        assert_eq!(
            check(&format!("masked-{}", width.bits()), &source, &candidate),
            BlockVerdict::EquivalentUnderModel
        );
        let mut rows = candidate.instructions().to_vec();
        rows[0].assignments[0].value = c(7);
        let bad = Program::new(0, 8, rows).unwrap();
        assert!(predicates::validate(&source, &plan, &bad).is_err());
        let BlockVerdict::Counterexample(w) =
            check(&format!("removed-{}", width.bits()), &source, &bad)
        else {
            panic!("missing removed-read witness")
        };
        assert_ne!(
            source
                .run_with_memory(&w.before_registers, w.memory_base, &w.memory, 8)
                .unwrap(),
            bad.run_with_memory(&w.before_registers, w.memory_base, &w.memory, 8)
                .unwrap()
        );
    }
}

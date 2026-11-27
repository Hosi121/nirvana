use super::*;

fn r(n: usize) -> Expr {
    Expr::Register(Reg(n))
}
fn add(a: Expr, b: u64) -> Expr {
    Expr::binary(BinaryOp::Add, a, Expr::Const(b))
}
fn set(n: usize, value: Expr) -> Assignment {
    Assignment {
        destination: Reg(n).into(),
        value,
    }
}
fn fixture(cut: u64, increment: u64, returned: u64) -> Program {
    Program::new(
        0,
        2,
        vec![
            IrInstruction {
                address: 0,
                size: 1,
                assignments: vec![set(1, add(r(0), increment))],
                control: Control::Jump(cut),
            },
            IrInstruction {
                address: cut,
                size: 1,
                assignments: vec![set(1, add(r(1), 1))],
                control: Control::Return(Expr::Const(returned)),
            },
        ],
    )
    .unwrap()
}
fn cuts() -> Vec<Cut> {
    vec![
        Cut {
            before: 0,
            after: 0,
            shared: vec![Reg(0)],
            before_invariants: vec![],
            after_invariants: vec![],
        },
        Cut {
            before: 10,
            after: 20,
            shared: vec![Reg(0)],
            before_invariants: vec![set(1, add(r(0), 1))],
            after_invariants: vec![set(1, add(r(0), 1))],
        },
    ]
}
fn problem(increment: u64) -> Problem {
    let original = query(
        &fixture(10, 1, u64::MAX),
        &fixture(20, increment, u64::MAX),
        &[Reg(0)],
        &[Reg(1)],
    )
    .unwrap();
    Problem::new(&original, &cuts()).unwrap()
}

#[test]
fn construction_binds_entry_interfaces_and_pure_equations_before_cloning() {
    let original = problem(1).original;
    let rejected = |cuts: Vec<Cut>| Problem::new(&original, &cuts).is_err();
    assert!(rejected(vec![]));
    let mut changed = cuts();
    changed[0].before_invariants = vec![set(0, Expr::Const(0))];
    assert!(rejected(changed));
    let mut changed = cuts();
    changed[0].shared.clear();
    assert!(rejected(changed));
    let mut changed = cuts();
    changed[1].after = 0;
    assert!(rejected(changed));
    let mut changed = cuts();
    changed[1].before = 1;
    assert!(rejected(changed));
    let mut changed = cuts();
    changed[1].shared = vec![Reg(1), Reg(0)];
    assert!(rejected(changed));
    let mut changed = cuts();
    changed[1].after_invariants[0].value = Expr::load(r(0), Width::U8);
    assert!(rejected(changed));
    let mut changed = cuts();
    changed[1].after_invariants[0].destination = Place::Memory {
        address: r(0),
        width: Width::U8,
    };
    assert!(rejected(changed));
    let mut changed = cuts();
    changed[1].after_invariants[0].value = r(2);
    assert!(rejected(changed));
    let mut deep = r(0);
    for _ in 0..MAX_DEPTH + 2 {
        deep = add(deep, 1);
    }
    let mut changed = cuts();
    changed[1].after_invariants[0].value = deep;
    assert!(rejected(changed));
    let dynamic = Program::new(
        0,
        1,
        vec![IrInstruction {
            address: 0,
            size: 1,
            assignments: vec![],
            control: Control::Return(r(0)),
        }],
    )
    .unwrap();
    let original = query(&dynamic, &dynamic, &[Reg(0)], &[]).unwrap();
    assert_eq!(
        Problem::new(&original, &cuts()[..1]).unwrap_err(),
        BuildError::DynamicReturn
    );
}

#[test]
fn local_queries_keep_postconditions_effects_and_terminal_outputs() {
    let problem = problem(1);
    assert_eq!(problem.obligations.len(), 6);
    for obligation in &problem.obligations {
        assert!(obligation.query.smt2().contains("memory_witness"));
        assert!(obligation.query.smt2().contains("(xor "));
    }
    let final_chunk = problem
        .obligations
        .iter()
        .find(|o| o.cut == 1 && o.kind == Kind::Correspondence)
        .unwrap();
    assert_eq!(
        final_chunk.query.outputs.at(&RunStatus::Returned(2)),
        [Reg(1)]
    );
    let solver = Solver::new("/nirvana/missing-solver");
    let Outcome::Unproved(failure) = problem.check(&solver, Duration::ZERO) else {
        panic!("zero budget cannot construct a seal")
    };
    assert_eq!(failure.checked, 0);
    assert_eq!(
        failure.verdict,
        Verdict::Unknown(UnknownReason::SolverTimeout)
    );
    let Outcome::Unproved(failure) = problem.check(&solver, Duration::from_secs(1)) else {
        panic!("missing solver cannot construct a seal")
    };
    assert!(matches!(
        failure.verdict,
        Verdict::Unknown(UnknownReason::SolverUnavailable(_))
    ));
}

#[test]
#[ignore = "requires NIRVANA_Z3; compositional proof and failed handoff controls"]
fn all_local_obligations_are_needed_before_a_bound_certificate_exists() {
    let solver =
        Solver::new(std::env::var("NIRVANA_Z3").unwrap()).with_timeout(Duration::from_secs(5));
    let good = problem(1);
    let Outcome::Verified(seal) = good.check(&solver, Duration::from_secs(5)) else {
        panic!("valid functional cut relation should compose")
    };
    assert_eq!(seal.checked(), 6);
    assert!(seal.matches(good.original()));
    let wrong = problem(2);
    assert!(!seal.matches(wrong.original()));
    // All local comparisons agree after normalization. The after-prefix did
    // not establish the assumed equation; its postcondition must still fail.
    for obligation in wrong
        .obligations()
        .iter()
        .filter(|o| o.kind == Kind::Correspondence)
    {
        assert_eq!(
            obligation.query.check(&solver),
            Verdict::EquivalentUnderModel
        );
    }
    let Outcome::Unproved(failure) = wrong.check(&solver, Duration::from_secs(5)) else {
        panic!("an unproved incoming equation cannot authorize adoption")
    };
    assert_eq!(failure.cut, 0);
    assert_eq!(failure.kind, Kind::AfterPostconditions);
    assert!(matches!(failure.verdict, Verdict::Counterexample(_)));
    assert!(matches!(
        wrong.original().check(&solver),
        Verdict::Counterexample(_)
    ));
    let same = query(&fixture(10, 2, 7), &fixture(20, 2, 7), &[Reg(0)], &[Reg(1)]).unwrap();
    let spurious = Problem::new(&same, &cuts()).unwrap();
    assert!(matches!(
        spurious.check(&solver, Duration::from_secs(5)),
        Outcome::Unproved(_)
    ));
    assert_eq!(
        same.check(&solver),
        Verdict::EquivalentUnderModel,
        "a failed local relation need not be a global counterexample"
    );

    // Sharing a value at a later cut requires proving its equality on arrival.
    let mut handoff = cuts();
    handoff[1].before_invariants.clear();
    handoff[1].after_invariants.clear();
    handoff[1].shared = vec![Reg(0), Reg(1)];
    let lost = Problem::new(wrong.original(), &handoff).unwrap();
    let Outcome::Unproved(failure) = lost.check(&solver, Duration::from_secs(5)) else {
        panic!("cut input equality must be established by the previous chunk")
    };
    assert_eq!(failure.kind, Kind::Correspondence);
    assert_eq!(failure.cut, 0);
    assert!(matches!(failure.verdict, Verdict::Counterexample(_)));

    // Unlisted original returns retain every common register observation.
    let before = fixture(10, 1, 9);
    let after = fixture(20, 2, 9);
    let original = query_at_returns(
        &before,
        &after,
        &[Reg(0)],
        &[ReturnOutputs {
            value: 0,
            registers: vec![],
        }],
    )
    .unwrap();
    let only_entry = [cuts()[0].clone()];
    let unlisted = Problem::new(&original, &only_entry).unwrap();
    let Outcome::Unproved(failure) = unlisted.check(&solver, Duration::from_secs(5)) else {
        panic!("unlisted terminal outputs must remain observed")
    };
    assert!(matches!(failure.verdict, Verdict::Counterexample(_)));
    println!(
        "DAG-COMPOSITION positive=1 failed_postcondition=1 failed_handoff=1 default_outputs=1"
    );
}

#[test]
#[ignore = "requires NIRVANA_Z3; private state, full RAM and first-fault composition"]
fn private_cut_constants_do_not_alias_capture_registers_or_drop_effects() {
    let solver =
        Solver::new(std::env::var("NIRVANA_Z3").unwrap()).with_timeout(Duration::from_secs(5));
    let before = fixture(10, 1, 7);
    let mut body = fixture(20, 1, 7).instructions().to_vec();
    body[0].assignments.push(set(2, Expr::Const(1)));
    body[1].assignments[0].value = Expr::binary(BinaryOp::Add, r(1), r(2));
    let after = Program::new(0, 3, body.clone()).unwrap();
    let original = query(&before, &after, &[Reg(0)], &[Reg(1)]).unwrap();
    let mut relations = cuts();
    relations[1].after_invariants.push(set(2, Expr::Const(1)));
    let problem = Problem::new(&original, &relations).unwrap();
    assert!(matches!(
        problem.check(&solver, Duration::from_secs(5)),
        Outcome::Verified(_)
    ));
    assert_eq!(original.check(&solver), Verdict::EquivalentUnderModel);
    body[0].assignments.last_mut().unwrap().value = Expr::Const(2);
    let wrong = Program::new(0, 3, body).unwrap();
    let original = query(&before, &wrong, &[Reg(0)], &[Reg(1)]).unwrap();
    assert!(matches!(
        Problem::new(&original, &relations)
            .unwrap()
            .check(&solver, Duration::from_secs(5)),
        Outcome::Unproved(_)
    ));

    let effects = |change: bool, reverse: bool| {
        let load = |n| Expr::load(r(n), Width::U64);
        Program::new(
            0,
            3,
            vec![
                IrInstruction {
                    address: 0,
                    size: 1,
                    assignments: vec![
                        Assignment {
                            destination: Place::Memory {
                                address: r(0),
                                width: Width::U8,
                            },
                            value: Expr::Const(if change { 3 } else { 2 }),
                        },
                        set(
                            2,
                            if reverse {
                                Expr::binary(BinaryOp::Add, load(1), load(0))
                            } else {
                                Expr::binary(BinaryOp::Add, load(0), load(1))
                            },
                        ),
                    ],
                    control: Control::Jump(10),
                },
                IrInstruction {
                    address: 10,
                    size: 1,
                    assignments: vec![],
                    control: Control::Return(Expr::Const(0)),
                },
            ],
        )
        .unwrap()
    };
    let mut relations = vec![cuts()[0].clone(), cuts()[1].clone()];
    relations[0].shared = vec![Reg(0), Reg(1)];
    relations[1].after = 10;
    relations[1].shared.clear();
    relations[1].before_invariants.clear();
    relations[1].after_invariants.clear();
    for (change, reverse) in [(false, false), (true, false), (false, true)] {
        let before = effects(false, false);
        let after = effects(change, reverse);
        let original = query(&before, &after, &[Reg(0), Reg(1)], &[]).unwrap();
        let outcome = Problem::new(&original, &relations)
            .unwrap()
            .check(&solver, Duration::from_secs(5));
        if !change && !reverse {
            assert!(matches!(outcome, Outcome::Verified(_)));
            assert_eq!(original.check(&solver), Verdict::EquivalentUnderModel);
        } else {
            let Outcome::Unproved(failure) = outcome else {
                panic!("RAM and first-fault mutations must fail")
            };
            let Verdict::Counterexample(witness) = failure.verdict else {
                panic!("effect mutations need local Rust replays")
            };
            if change {
                assert_ne!(witness.before.state.memory, witness.after.state.memory);
            } else {
                assert_ne!(witness.before.status, witness.after.status);
            }
        }
    }
    println!(
        "DAG-COMPOSITION private_constant=1 false_constant=1 ram_replay=1 fault_replay=1 global_oracles=2"
    );
}

mod audit;

use super::*;

#[test]
fn rejects_a_discovery_from_another_source() {
    let make = |value| {
        Program::new(
            0,
            1,
            vec![IrInstruction {
                address: 0,
                size: 1,
                assignments: vec![],
                control: Control::Return(Expr::Const(value)),
            }],
        )
        .unwrap()
    };
    let source = make(1);
    let discovery = lane_patterns::discover(&source).unwrap();
    assert_eq!(propose(&make(2), &discovery, 0).unwrap_err(), Error::Source);
    assert_eq!(propose(&source, &discovery, 0).unwrap_err(), Error::Pattern);
}

fn fixture() -> Program {
    let r = |n| Expr::Register(Reg(n));
    let c = Expr::Const;
    let op = Expr::binary;
    let set = |n, value| Assignment {
        destination: Reg(n).into(),
        value,
    };
    let step = |address, assignments, control| IrInstruction {
        address,
        size: 1,
        assignments,
        control,
    };
    let mut instructions = vec![
        step(
            0,
            vec![set(7, op(BinaryOp::And, r(7), c(3))), set(0, c(0))],
            Control::Jump(10),
        ),
        step(
            10,
            vec![set(4, op(BinaryOp::Add, r(0), c(1)))],
            Control::Branch {
                condition: op(BinaryOp::Eq, r(7), c(0)),
                target: 90,
            },
        ),
        step(11, vec![], Control::Jump(20)),
    ];
    for lane in 0..3u64 {
        let pc = 20 + 20 * lane;
        let offset = lane + 1;
        instructions.extend([
            step(
                pc,
                vec![
                    set(5, op(BinaryOp::Add, r(0), c(offset))),
                    set(
                        3,
                        Expr::load(
                            op(
                                BinaryOp::Add,
                                r(1),
                                op(BinaryOp::Mul, op(BinaryOp::And, r(5), c(3)), c(8)),
                            ),
                            crate::model::ir::Width::U64,
                        ),
                    ),
                    set(2, op(BinaryOp::Add, r(2), op(BinaryOp::Xor, r(3), r(4)))),
                ],
                Control::Next,
            ),
            step(
                pc + 1,
                vec![Assignment {
                    destination: Place::Memory {
                        address: op(BinaryOp::Add, r(1), c(16)),
                        width: crate::model::ir::Width::U64,
                    },
                    value: r(2),
                }],
                Control::Branch {
                    condition: op(BinaryOp::Eq, op(BinaryOp::And, r(2), c(7)), c(0)),
                    target: 110,
                },
            ),
            step(
                pc + 2,
                vec![],
                Control::Branch {
                    condition: op(BinaryOp::Eq, op(BinaryOp::And, r(2), c(3)), c(1)),
                    target: pc + 5,
                },
            ),
            step(
                pc + 3,
                vec![set(
                    6,
                    op(BinaryOp::Add, r(6), op(BinaryOp::And, r(2), c(15))),
                )],
                if lane == 2 {
                    Control::Jump(90)
                } else {
                    Control::Branch {
                        condition: op(BinaryOp::Eq, r(7), c(offset)),
                        target: 90,
                    }
                },
            ),
            step(pc + 4, vec![], Control::Jump(pc + 20)),
            step(
                pc + 5,
                vec![set(6, op(BinaryOp::Xor, r(6), r(5)))],
                Control::Jump(90),
            ),
        ]);
    }
    // Last-lane fallthrough is unreachable, but every static edge stays closed.
    instructions
        .iter_mut()
        .find(|i| i.address == 64)
        .unwrap()
        .control = Control::Jump(90);
    instructions.extend([
        step(
            90,
            vec![
                set(6, op(BinaryOp::Add, r(6), r(4))),
                Assignment {
                    destination: Place::Memory {
                        address: op(BinaryOp::Add, r(1), c(24)),
                        width: crate::model::ir::Width::U64,
                    },
                    value: r(6),
                },
                set(0, op(BinaryOp::Add, r(0), c(1))),
            ],
            Control::Branch {
                condition: op(BinaryOp::Ult, r(0), c(2)),
                target: 10,
            },
        ),
        step(91, vec![], Control::Jump(100)),
        step(100, vec![], Control::Return(op(BinaryOp::Xor, r(2), r(6)))),
        step(110, vec![], Control::Return(op(BinaryOp::Xor, r(2), r(6)))),
    ]);
    Program::new(0, 9, instructions).unwrap()
}

#[test]
fn builds_a_source_bound_loop_and_preserves_aliases_and_first_faults() {
    let source = fixture();
    let discovery = lane_patterns::discover(&source).unwrap();
    assert_eq!(discovery.groups().len(), 1);
    let proposal = propose(&source, &discovery, 0).unwrap();
    assert!(proposal.belongs_to(&source));
    assert_eq!(proposal.envelope().lane_entries, [20, 40, 60]);
    assert_eq!(proposal.rounds(), 3);
    assert_eq!(proposal.selector(), Some((Reg(7), 2)));
    for seed in 0..32u64 {
        for address in [1040, 1136, 1023, 1152, u64::MAX] {
            let mut input = vec![0; 9];
            input[1] = address;
            input[2] = seed.wrapping_mul(19);
            input[6] = seed ^ 11;
            input[7] = seed;
            let memory: Vec<_> = (0..128u64).map(|n| (n * 29 + seed) as u8).collect();
            let left = source.run_with_memory(&input, 1024, &memory, 512).unwrap();
            input.push(u64::MAX);
            let right = proposal
                .program()
                .run_with_memory(&input, 1024, &memory, 512)
                .unwrap();
            assert_eq!(left.status, right.status, "seed={seed} address={address}");
            assert_eq!(left.state.memory, right.state.memory);
        }
    }
}

#[test]
fn a_lane_at_the_cut_entry_keeps_its_checked_input_normalization() {
    let source = fixture();
    let discovery = lane_patterns::discover(&source).unwrap();
    let mut envelope = propose(&source, &discovery, 0).unwrap().envelope;
    envelope.header = envelope.first_lane;
    let counter = Reg(source.register_count());
    let padded = Program::new(
        0,
        source.register_count() + 1,
        source.instructions().to_vec(),
    )
    .unwrap();
    let widths = ValueWidths::analyze(&padded);
    let before =
        extraction::extract(&padded, envelope.header, &envelope.stops(), Some(&widths)).unwrap();
    assert_eq!(before.input_bit_caps()[7], 2);
    let group = &discovery.groups()[0];
    let controls = controls::analyze(&padded, &discovery, group, &envelope, counter).unwrap();
    let (candidate, _) =
        emit::candidate(&padded, group, &envelope, &before, &controls, counter).unwrap();
    for value in [0, 3, 4, 5, u64::MAX] {
        let mut input = vec![0; padded.register_count()];
        input[7] = value;
        let memory = vec![0x5a; 32];
        let state = candidate
            .run_block_with_memory(envelope.header, &input, 1024, &memory)
            .unwrap();
        assert_eq!(state.state.registers[7], value & 3);
        assert_eq!(state.state.memory, memory);
    }
}

#[test]
fn lane_cuts_infer_entry_values_and_leave_later_definitions_inside_the_chunk() {
    let source = fixture();
    let found = lane_patterns::discover(&source).unwrap();
    let proposal = propose(&source, &found, 0).unwrap();
    let problem = proposal.verification_problem().unwrap();
    let local = problem.composition_problem().unwrap();
    assert_eq!(local.cuts().len(), 4);
    assert!(local.cuts()[0].before_invariants.is_empty());
    assert!(local.cuts()[0].after_invariants.is_empty());
    for (phase, cut) in local.cuts().iter().skip(1).enumerate() {
        assert!(cut.before_invariants.iter().any(|equation| {
            equation.destination == Place::Register(Reg(4))
                && equation.value
                    == Expr::binary(BinaryOp::Add, Expr::Register(Reg(0)), Expr::Const(1))
        }));
        assert!(
            cut.before_invariants
                .iter()
                .all(|equation| { equation.destination != Place::Register(Reg(5)) }),
            "the lane index is assigned after the cut"
        );
        assert!(cut.after_invariants.iter().any(|equation| {
            equation.destination == Place::Register(proposal.counter())
                && equation.value == Expr::Const(phase as u64 + 1)
        }));
        assert!(!cut.shared.contains(&proposal.counter()));
    }
}

#[test]
#[ignore = "requires NIRVANA_Z3"]
fn accepts_only_completed_equivalent_proposals() {
    let source = fixture();
    let discovery = lane_patterns::discover(&source).unwrap();
    let proposal = propose(&source, &discovery, 0).unwrap();
    let solver = Solver::new(std::env::var("NIRVANA_Z3").unwrap())
        .with_timeout(std::time::Duration::from_secs(15));
    let Outcome::Verified(accepted) = proposal.verify(&solver) else {
        panic!("positive proposal rejected")
    };
    assert_eq!(accepted.checked_partitions(), 16);
    assert!(
        accepted
            .outputs()
            .matches(accepted.proposal().source_region())
    );
    let mut wrong = proposal.clone();
    let mut instructions = wrong.program.instructions().to_vec();
    let load = instructions
        .iter_mut()
        .find(|i| i.address == wrong.feedback)
        .unwrap();
    let update = load
        .assignments
        .iter_mut()
        .find(|a| a.destination == Place::Register(Reg(2)))
        .unwrap();
    update.value = Expr::binary(
        BinaryOp::Add,
        Expr::Register(Reg(2)),
        Expr::Register(Reg(3)),
    );
    wrong.program = Program::new(0, 10, instructions).unwrap();
    let Outcome::Counterexample(witness) = wrong.verify(&solver) else {
        panic!("wrong update must replay in the original cyclic regions")
    };
    assert_ne!(witness.before.memory, witness.after.memory);
    assert!(!witness.before.trace.is_empty() && !witness.after.trace.is_empty());
    let mut forged = witness.dag.clone();
    forged.before.state.memory[0] ^= 1;
    let outputs = extraction::live_out::derive(wrong.source_region()).unwrap();
    assert_eq!(
        super::replay::check(&wrong, forged, &outputs).unwrap_err(),
        UnknownReason::InvalidCounterexample
    );
    let staged = staged_fixture();
    let found = lane_patterns::discover(&staged).unwrap();
    let staged = propose(&staged, &found, 0).unwrap();
    assert!(matches!(staged.verify(&solver), Outcome::Verified(_)));

    let mut short = proposal.clone();
    short.rounds = 1;
    assert!(matches!(short.verify(&solver), Outcome::Incomplete(_)));
    let missing = Solver::new("/nirvana/missing-solver");
    assert!(matches!(proposal.verify(&missing), Outcome::Unknown(_)));
}

fn staged_fixture() -> Program {
    let source = fixture();
    let mut instructions = source.instructions().to_vec();
    for i in &mut instructions {
        match &mut i.control {
            Control::Jump(to) | Control::Branch { target: to, .. } if *to == 90 => *to = 80,
            _ => {}
        }
        if i.address == 90 {
            i.assignments[0].value = Expr::binary(
                BinaryOp::Add,
                Expr::Register(Reg(3)),
                Expr::Register(Reg(4)),
            );
        }
    }
    instructions.push(IrInstruction {
        address: 80,
        size: 1,
        assignments: vec![Assignment {
            destination: Reg(3).into(),
            value: Expr::Register(Reg(6)),
        }],
        control: Control::Jump(90),
    });
    Program::new(0, 9, instructions).unwrap()
}

#[test]
fn stages_last_updates_and_rejects_ambiguous_guards_and_multiple_latches() {
    let source = staged_fixture();
    let found = lane_patterns::discover(&source).unwrap();
    let proposal = propose(&source, &found, 0).unwrap();
    for seed in 0..64u64 {
        let mut input = vec![0; 9];
        input[1] = 1040;
        input[2] = seed.wrapping_mul(71);
        input[6] = seed ^ 17;
        input[7] = seed;
        let memory: Vec<_> = (0..128u64).map(|n| (n * 13 + seed) as u8).collect();
        let left = source.run_with_memory(&input, 1024, &memory, 512).unwrap();
        input.push(37);
        let right = proposal
            .program()
            .run_with_memory(&input, 1024, &memory, 512)
            .unwrap();
        assert_eq!(left.status, right.status);
        assert_eq!(left.state.memory, right.state.memory);
    }
    let source = fixture();
    let mut instructions = source.instructions().to_vec();
    let Control::Branch { condition, .. } = &mut instructions
        .iter_mut()
        .find(|i| i.address == 43)
        .unwrap()
        .control
    else {
        panic!()
    };
    *condition = Expr::binary(BinaryOp::Eq, Expr::Register(Reg(8)), Expr::Const(2));
    let ambiguous = Program::new(0, 9, instructions).unwrap();
    let found = lane_patterns::discover(&ambiguous).unwrap();
    assert_eq!(propose(&ambiguous, &found, 0).unwrap_err(), Error::Controls);
    let mut instructions = source.instructions().to_vec();
    instructions
        .iter_mut()
        .find(|i| i.address == 25)
        .unwrap()
        .control = Control::Jump(10);
    let multiple = Program::new(0, 9, instructions).unwrap();
    let found = lane_patterns::discover(&multiple).unwrap();
    assert_eq!(propose(&multiple, &found, 0).unwrap_err(), Error::Boundary);
    let mut instructions = source.instructions().to_vec();
    instructions
        .iter_mut()
        .find(|i| i.address == 63)
        .unwrap()
        .control = Control::Return(Expr::Register(Reg(2)));
    let early = Program::new(0, 9, instructions).unwrap();
    let found = lane_patterns::discover(&early).unwrap();
    let proposal = propose(&early, &found, 0).unwrap();
    assert!(proposal.envelope().abrupt.contains(&63));
    assert!(
        !proposal
            .source_region()
            .source_to_region()
            .contains_key(&63)
    );
}

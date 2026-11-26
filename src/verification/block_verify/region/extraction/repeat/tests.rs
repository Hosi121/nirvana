use super::*;
use crate::model::ir::{Place, RunStatus, Width};

fn fixture() -> Program {
    let r = |n| Expr::Register(Reg(n));
    Program::new(
        0,
        5,
        vec![
            IrInstruction {
                address: 0,
                size: 1,
                assignments: vec![Assignment {
                    destination: Reg(1).into(),
                    value: Expr::binary(BinaryOp::And, r(1), Expr::Const(3)),
                }],
                control: Control::Jump(10),
            },
            IrInstruction {
                address: 10,
                size: 1,
                assignments: vec![
                    Assignment {
                        destination: Reg(3).into(),
                        value: Expr::load(r(2), Width::U64),
                    },
                    Assignment {
                        destination: Place::Memory {
                            address: r(2),
                            width: Width::U64,
                        },
                        value: Expr::binary(BinaryOp::Add, r(3), Expr::Const(1)),
                    },
                    Assignment {
                        destination: Reg(0).into(),
                        value: Expr::binary(BinaryOp::Add, r(0), Expr::Const(1)),
                    },
                ],
                control: Control::Branch {
                    condition: Expr::binary(BinaryOp::Ult, r(0), r(1)),
                    target: 10,
                },
            },
            IrInstruction {
                address: 11,
                size: 1,
                assignments: vec![],
                control: Control::Return(r(4)),
            },
        ],
    )
    .unwrap()
}
fn projection(source: &Program) -> Region {
    extract(source, 10, &[10], Some(&ValueWidths::analyze(source))).unwrap()
}
fn modify(unfolding: &Unfolding, edit: impl FnOnce(&mut Vec<IrInstruction>)) -> Unfolding {
    let mut bad = unfolding.clone();
    let mut instructions = bad.program.instructions().to_vec();
    edit(&mut instructions);
    bad.program = Program::new(0, bad.program.register_count(), instructions).unwrap();
    bad
}

#[test]
fn repeated_regions_preserve_effects_values_and_faults_including_counter_wrap() {
    let source = fixture();
    let region = projection(&source);
    assert_eq!(region.input_bit_caps()[1], 2);
    assert_eq!(region.input_bit_caps()[0], 64);
    let unfolding = unfold(&region, 4).unwrap();
    for initial in [0, 1, 2, 3, u64::MAX - 1, u64::MAX] {
        for limit in 0..4 {
            for address in [100, 99, 109, u64::MAX] {
                for size in [0, 7, 8, 16] {
                    let memory: Vec<_> = (0..size).map(|i| (i * 29 + 7) as u8).collect();
                    let input = [initial, limit, address, 99, u64::MAX];
                    let mut actual_input = input.to_vec();
                    actual_input.extend([19, 23]);
                    let actual = unfolding
                        .program()
                        .run_with_memory(&actual_input, 100, &memory, 128)
                        .unwrap();
                    let mut expected_registers = input.to_vec();
                    let mut expected_memory = memory.clone();
                    let mut pc = 10;
                    let expected = loop {
                        let report = source
                            .run_block_with_memory(pc, &expected_registers, 100, &expected_memory)
                            .unwrap();
                        expected_registers = report.state.registers;
                        expected_memory = report.state.memory;
                        match report.exit {
                            BlockExit::Next(next) => pc = next,
                            BlockExit::Returned(value) => break Ok(value),
                            BlockExit::Fault(fault) => break Err(fault),
                        }
                    };
                    match expected {
                        Ok(value) => {
                            let RunStatus::Returned(tag) = actual.status else {
                                panic!("normal source became {:?}", actual.status);
                            };
                            assert_eq!(region.exit(tag), Some(Exit::FunctionReturn));
                            assert_eq!(actual.state.registers[region.return_register().0], value);
                            assert_eq!(
                                actual.state.registers[unfolding.exhaustion_register().0],
                                0
                            );
                        }
                        Err(fault) => assert_eq!(actual.status, RunStatus::Fault(fault)),
                    }
                    assert_eq!(&actual.state.registers[..input.len()], expected_registers);
                    assert_eq!(actual.state.memory, expected_memory);
                }
            }
        }
    }
}

#[test]
fn composition_tampering_and_missing_feedback_or_resources_are_rejected() {
    let source = fixture();
    let region = projection(&source);
    let unfolding = unfold(&region, 4).unwrap();
    let store = unfolding.copies[0][&region.body[&10]];
    let last = unfolding.exhaustion;
    let feedback = unfolding.copies[0][&region.terminals[&10]];
    for bad in [
        modify(&unfolding, |is| {
            is.iter_mut()
                .find(|i| i.address == store)
                .unwrap()
                .assignments
                .remove(1);
        }),
        modify(&unfolding, |is| {
            is.iter_mut()
                .find(|i| i.address == last)
                .unwrap()
                .assignments
                .clear()
        }),
        modify(&unfolding, |is| {
            is.iter_mut()
                .find(|i| i.address == feedback)
                .unwrap()
                .control = Control::Jump(last)
        }),
    ] {
        assert!(bad.validate().is_err());
    }
    assert!(matches!(
        unfold(&region, usize::MAX),
        Err(ExtractionError::Region(Error::Limit))
    ));
    let no_feedback = extract(&source, 11, &[], None).unwrap();
    assert!(matches!(
        unfold(&no_feedback, 1),
        Err(ExtractionError::Boundary)
    ));
}

#[test]
fn missing_solver_never_seals_a_complete_region() {
    let source = fixture();
    let region = projection(&source);
    let solver = Solver::new("/nirvana-missing-repeat-solver");
    assert!(matches!(
        unfold(&region, 4).unwrap().check_complete(&solver),
        Completion::Unknown(UnknownReason::SolverUnavailable(_))
    ));
}

#[test]
#[ignore = "requires Z3; checks bound completeness and replays insufficient bounds on the cyclic source"]
fn completion_queries_distinguish_proven_bounds_exhaustion_and_unknown() {
    let source = fixture();
    let region = projection(&source);
    let solver = Solver::new(std::env::var_os("NIRVANA_Z3").unwrap_or_else(|| "z3".into()))
        .with_timeout(std::time::Duration::from_secs(5));
    for rounds in [0, 1, 3, 4, 5] {
        let unfolded = unfold(&region, rounds).unwrap();
        let now = std::time::Instant::now();
        let query = unfolded.completion_query().unwrap();
        if let Some(directory) = std::env::var_os("NIRVANA_REPEAT_REPORT") {
            let directory = std::path::PathBuf::from(directory);
            std::fs::create_dir_all(&directory).unwrap();
            std::fs::write(
                directory.join(format!("rounds-{rounds}.smt2")),
                query.smt2(),
            )
            .unwrap();
        }
        let verdict = unfolded.check_complete(&solver);
        let name = match verdict {
            Completion::Complete(complete) => {
                assert!(rounds >= 4);
                assert_eq!(complete.rounds(), rounds);
                assert!(complete.source_region().belongs_to(&source));
                assert_eq!(
                    complete.program().instructions(),
                    unfolded.program().instructions()
                );
                "complete"
            }
            Completion::BoundExceeded(witness) => {
                assert!(rounds < 4);
                assert_eq!(witness.rounds, rounds);
                if rounds > 0 {
                    assert_eq!(witness.source.trace.len(), rounds);
                }
                "bound_exceeded"
            }
            Completion::Unknown(reason) => panic!("unexpected solver result: {reason:?}"),
        };
        println!(
            "REGION-COMPLETE rounds={rounds} verdict={name} bytes={} ms={}",
            query.smt2().len(),
            now.elapsed().as_millis()
        );
    }
    let unconstrained = extract(&source, 10, &[10], None).unwrap();
    assert!(matches!(
        unfold(&unconstrained, 4).unwrap().check_complete(&solver),
        Completion::BoundExceeded(_)
    ));
    println!("REGION-COMPLETE unbounded_inputs=bound_exceeded");
}

fn independent_four_lane_source() -> Program {
    let source = fixture();
    let mut instructions = vec![IrInstruction {
        address: 0,
        size: 1,
        assignments: vec![
            source.instructions()[0].assignments[0].clone(),
            Assignment {
                destination: Reg(5).into(),
                value: Expr::Const(0),
            },
        ],
        control: Control::Jump(10),
    }];
    for lane in 0..4 {
        let pc = 10 + lane * 10;
        instructions.push(IrInstruction {
            address: pc,
            size: 1,
            assignments: source.instructions()[1].assignments.clone(),
            control: if lane == 3 {
                Control::Jump(100)
            } else {
                Control::Branch {
                    condition: Expr::binary(
                        BinaryOp::Ult,
                        Expr::Register(Reg(0)),
                        Expr::Register(Reg(1)),
                    ),
                    target: pc + 10,
                }
            },
        });
        if lane != 3 {
            instructions.push(IrInstruction {
                address: pc + 1,
                size: 1,
                assignments: vec![],
                control: Control::Jump(100),
            });
        }
    }
    instructions.push(IrInstruction {
        address: 100,
        size: 1,
        assignments: vec![Assignment {
            destination: Reg(5).into(),
            value: Expr::Register(Reg(4)),
        }],
        control: Control::Return(Expr::Const(1)),
    });
    Program::new(0, 6, instructions).unwrap()
}

#[test]
#[ignore = "requires Z3; compare a certified cyclic candidate to a separate acyclic four-lane source"]
fn certified_cyclic_candidate_matches_unrolled_memory_and_rejects_wrong_increment() {
    let source = fixture();
    let solver = Solver::new(std::env::var_os("NIRVANA_Z3").unwrap_or_else(|| "z3".into()))
        .with_timeout(std::time::Duration::from_secs(5));
    let baseline = independent_four_lane_source();
    for wrong in [false, true] {
        let mut instructions = source.instructions().to_vec();
        if wrong {
            instructions[1].assignments[2].value =
                Expr::binary(BinaryOp::Add, Expr::Register(Reg(0)), Expr::Const(2));
        }
        let candidate = Program::new(0, 5, instructions).unwrap();
        let projected = projection(&candidate);
        let Completion::Complete(complete) = unfold(&projected, 4).unwrap().check_complete(&solver)
        else {
            panic!("candidate bound did not complete");
        };
        let shared: Vec<_> = (0..5).map(Reg).collect();
        // Positive comparison retains every original normal register. The
        // negative must also differ under the C return/RAM/first-fault scope.
        let outputs: Vec<_> = if wrong {
            vec![Reg(5)]
        } else {
            (0..6).map(Reg).collect()
        };
        let query = region::query(&baseline, complete.program(), &shared, &outputs).unwrap();
        if let Some(directory) = std::env::var_os("NIRVANA_REPEAT_REPORT") {
            std::fs::write(
                std::path::PathBuf::from(directory).join(format!("candidate-wrong-{wrong}.smt2")),
                query.smt2(),
            )
            .unwrap();
        }
        let now = std::time::Instant::now();
        let verdict = match query.check(&solver) {
            Verdict::EquivalentUnderModel if !wrong => "equivalent",
            Verdict::Counterexample(witness) if wrong => {
                let left = source
                    .run_with_memory(
                        &witness.before_registers[..5],
                        witness.memory_base,
                        &witness.memory,
                        32,
                    )
                    .unwrap();
                let right = candidate
                    .run_with_memory(
                        &witness.after_registers[..5],
                        witness.memory_base,
                        &witness.memory,
                        32,
                    )
                    .unwrap();
                assert!(
                    matches!(left.status, RunStatus::Returned(_))
                        && matches!(right.status, RunStatus::Returned(_))
                );
                assert!(left.state.memory != right.state.memory || left.status != right.status);
                assert_eq!(&witness.before.state.registers[..5], left.state.registers);
                assert_eq!(&witness.after.state.registers[..5], right.state.registers);
                assert_eq!(witness.before.state.memory, left.state.memory);
                assert_eq!(witness.after.state.memory, right.state.memory);
                "counterexample"
            }
            other => panic!("unexpected candidate result: {other:?}"),
        };
        println!(
            "REGION-CANDIDATE wrong={wrong} verdict={verdict} bytes={} ms={}",
            query.smt2().len(),
            now.elapsed().as_millis()
        );
    }
}

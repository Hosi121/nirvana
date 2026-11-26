use super::*;
use crate::model::ir::{BinaryOp, Place, RunStatus, Width};
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
                control: Control::Branch {
                    condition: r(1),
                    target: 2,
                },
            },
            IrInstruction {
                address: 1,
                size: 1,
                assignments: vec![],
                control: Control::Jump(100),
            },
            IrInstruction {
                address: 2,
                size: 1,
                assignments: vec![Assignment {
                    destination: Reg(0).into(),
                    value: Expr::Const(1),
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
                ],
                control: Control::Branch {
                    condition: Expr::binary(BinaryOp::Eq, r(0), r(1)),
                    target: 100,
                },
            },
            IrInstruction {
                address: 11,
                size: 1,
                assignments: vec![Assignment {
                    destination: Reg(0).into(),
                    value: Expr::binary(BinaryOp::Add, r(0), Expr::Const(1)),
                }],
                control: Control::Jump(10),
            },
            IrInstruction {
                address: 100,
                size: 1,
                assignments: vec![],
                control: Control::Return(r(4)),
            },
        ],
    )
    .unwrap()
}
#[test]
#[ignore = "requires Z3; checks real entry relations and source-replayed exhaustion"]
fn entry_prefix_relations_prove_equal_exit_loops_and_replay_exhaustion() {
    let source = fixture();
    let prefix = extract(&source, 0, &[10], None).unwrap();
    let iteration = extract(&source, 10, &[10], None).unwrap();
    let solver = Solver::new(std::env::var("NIRVANA_Z3").unwrap())
        .with_timeout(std::time::Duration::from_secs(5));
    let directory = std::path::PathBuf::from(
        std::env::var("NIRVANA_PREFIX_REPORT").unwrap_or_else(|_| String::from("target")),
    );
    for rounds in [0, 2, 3, 4] {
        let repeated = unfold(&iteration, rounds).unwrap();
        let context = Prefixed::new(&prefix, &repeated).unwrap();
        let query = context.completion_query().unwrap();
        if std::env::var_os("NIRVANA_PREFIX_REPORT").is_some() {
            std::fs::write(
                directory.join(format!("rounds-{rounds}.smt2")),
                query.smt2(),
            )
            .unwrap();
        }
        let now = std::time::Instant::now();
        let verdict = match context.check_complete(&solver) {
            Completion::Complete(complete) if rounds >= 3 => {
                assert_eq!(complete.source_region().source_entry(), 0);
                assert_eq!(complete.rounds(), rounds);
                assert_eq!(
                    complete.program().instructions(),
                    context.program().instructions()
                );
                "complete"
            }
            Completion::BoundExceeded(w) if rounds < 3 => {
                assert!(!w.source.trace.is_empty());
                assert_eq!(w.source.registers[0], 1 + rounds as u64);
                "bound_exceeded"
            }
            other => panic!("unexpected context verdict {other:?}"),
        };
        println!(
            "PREFIX rounds={rounds} verdict={verdict} bytes={} ms={}",
            query.smt2().len(),
            now.elapsed().as_millis()
        );
    }
    let caps = ValueWidths::analyze(&source);
    let without_context = extract(&source, 10, &[10], Some(&caps)).unwrap();
    assert_eq!(without_context.input_bit_caps()[1], 2);
    assert!(matches!(
        unfold(&without_context, 4).unwrap().check_complete(&solver),
        Completion::BoundExceeded(_)
    ));
    println!("PREFIX without_entry_context=bound_exceeded");
}

#[test]
fn prefixed_unfolding_preserves_initializers_lazy_exits_full_effects_and_faults() {
    let source = fixture();
    let prefix = extract(&source, 0, &[10], None).unwrap();
    let iteration = extract(&source, 10, &[10], None).unwrap();
    for rounds in [3, 4] {
        let context = Prefixed::new(&prefix, &unfold(&iteration, rounds).unwrap()).unwrap();
        for counter in [0, u64::MAX] {
            for limit in [0, 1, 2, 3, 4, u64::MAX] {
                for result in [0, 1, u64::MAX] {
                    for pointer in [100, 99, u64::MAX] {
                        for size in [0, 7, 8, 16] {
                            let input = [counter, limit, pointer, 19, result];
                            let memory: Vec<_> = (0..size).map(|i| (i * 29 + 7) as u8).collect();
                            let expected =
                                source.run_with_memory(&input, 100, &memory, 32).unwrap();
                            let mut extended = input.to_vec();
                            extended.extend([23, 29]);
                            let actual = context
                                .program()
                                .run_with_memory(&extended, 100, &memory, 128)
                                .unwrap();
                            match expected.status {
                                RunStatus::Returned(value) => {
                                    let RunStatus::Returned(tag) = actual.status else {
                                        panic!("prefix lost Return");
                                    };
                                    assert_eq!(prefix.exit(tag), Some(Exit::FunctionReturn));
                                    assert_eq!(
                                        actual.state.registers[prefix.return_register().0],
                                        value
                                    );
                                    assert_eq!(actual.state.registers[context.repeated.flag.0], 0);
                                }
                                RunStatus::Fault(fault) => {
                                    assert_eq!(actual.status, RunStatus::Fault(fault))
                                }
                                RunStatus::Suspended => panic!("bounded source suspended"),
                            }
                            assert_eq!(&actual.state.registers[..5], expected.state.registers);
                            assert_eq!(actual.state.memory, expected.state.memory);
                        }
                    }
                }
            }
        }
    }
}
#[test]
fn source_tag_domains_input_caps_and_connection_tampering_are_rejected() {
    let source = fixture();
    let prefix = extract(&source, 0, &[10], None).unwrap();
    let iteration = extract(&source, 10, &[10], None).unwrap();
    let unfolded = unfold(&iteration, 3).unwrap();
    let context = Prefixed::new(&prefix, &unfolded).unwrap();
    let large = unfold(&iteration, 25).unwrap();
    assert!(matches!(
        Prefixed::new(&prefix, &large),
        Err(ExtractionError::Region(Error::Limit))
    ));
    assert!(matches!(
        Prefixed::new(&iteration, &unfolded),
        Err(ExtractionError::Boundary)
    ));
    let tags = extract(&source, 0, &[10, 100], None).unwrap();
    assert!(matches!(
        Prefixed::new(&tags, &unfolded),
        Err(ExtractionError::Boundary)
    ));
    let cap = extract(&source, 10, &[10], Some(&ValueWidths::analyze(&source))).unwrap();
    assert!(matches!(
        Prefixed::new(&prefix, &unfold(&cap, 3).unwrap()),
        Err(ExtractionError::Boundary)
    ));
    let mut foreign = source.instructions().to_vec();
    foreign[2].assignments[0].value = Expr::Const(2);
    let foreign = Program::new(0, 5, foreign).unwrap();
    let foreign = extract(&foreign, 0, &[10], None).unwrap();
    assert!(matches!(
        Prefixed::new(&foreign, &unfolded),
        Err(ExtractionError::Boundary)
    ));
    for change in [0, 1, 2] {
        let mut bad = context.clone();
        let mut is = bad.program.instructions().to_vec();
        match change {
            0 => is[0].assignments[0].value = Expr::Const(1),
            1 => {
                is.iter_mut()
                    .find(|i| i.address == bad.prefix.terminals[&10] + bad.prefix_offset)
                    .unwrap()
                    .control = Control::Return(Expr::Const(0))
            }
            _ => {
                is.iter_mut()
                    .find(|i| i.address == bad.prefix.body[&2] + bad.prefix_offset)
                    .unwrap()
                    .assignments[0]
                    .value = Expr::Const(2)
            }
        }
        bad.program = Program::new(0, bad.program.register_count(), is).unwrap();
        assert!(bad.validate().is_err());
    }
    let missing = Solver::new("/nirvana-missing-prefixed-solver");
    assert!(matches!(
        context.check_complete(&missing),
        Completion::Unknown(UnknownReason::SolverUnavailable(_))
    ));
}

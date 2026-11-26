use super::*;
use crate::model::ir::Width;

fn fixture() -> Program {
    let step = |address, assignments, control| IrInstruction {
        address,
        size: 1,
        assignments,
        control,
    };
    Program::new(
        0,
        9,
        vec![
            step(0, vec![], Control::Return(Expr::Const(0))),
            step(
                10,
                vec![
                    Assignment {
                        destination: Place::Memory {
                            address: Expr::Register(Reg(0)),
                            width: Width::U8,
                        },
                        value: Expr::Register(Reg(1)),
                    },
                    Assignment {
                        destination: Reg(2).into(),
                        value: Expr::Const(7),
                    },
                ],
                Control::Branch {
                    condition: Expr::Register(Reg(3)),
                    target: 20,
                },
            ),
            step(
                11,
                vec![Assignment {
                    destination: Reg(4).into(),
                    value: Expr::load(Expr::Register(Reg(5)), Width::U8),
                }],
                Control::Return(Expr::Register(Reg(4))),
            ),
            step(
                20,
                vec![Assignment {
                    destination: Reg(6).into(),
                    value: Expr::select(
                        Expr::Register(Reg(7)),
                        Expr::Register(Reg(1)),
                        Expr::Register(Reg(8)),
                    ),
                }],
                Control::Return(Expr::Register(Reg(6))),
            ),
        ],
    )
    .unwrap()
}

#[test]
fn unreachable_continuations_get_fresh_arbitrary_input_interfaces() {
    let source = fixture();
    let region = extract(&source, 0, &[10, 11, 20], None).unwrap();
    let interface = derive(&region).unwrap();
    assert!(interface.matches(&region));
    assert_eq!(
        interface.returns,
        [
            ReturnOutputs {
                value: 0,
                registers: [0, 1, 3, 5, 7, 8, 9].into_iter().map(Reg).collect()
            },
            ReturnOutputs {
                value: 1,
                registers: vec![Reg(5), Reg(9)]
            },
            ReturnOutputs {
                value: 2,
                registers: vec![Reg(1), Reg(7), Reg(8), Reg(9)]
            },
            ReturnOutputs {
                value: 3,
                registers: vec![Reg(9)]
            },
        ]
    );
    assert!(!interface.matches(&extract(&source, 0, &[10], None).unwrap()));
    let mut other = source.instructions().to_vec();
    other[0].control = Control::Return(Expr::Const(1));
    let other = Program::new(0, 9, other).unwrap();
    assert!(!interface.matches(&extract(&other, 0, &[10, 11, 20], None).unwrap()));
}

#[test]
fn independent_check_rejects_missing_address_value_branch_select_and_return_reads() {
    let source = fixture();
    let interface = derive(&extract(&source, 0, &[10, 11, 20], None).unwrap()).unwrap();
    for (tag, register) in [
        (0, 0),
        (0, 1),
        (0, 3),
        (0, 5),
        (0, 7),
        (0, 8),
        (1, 5),
        (2, 1),
        (2, 7),
        (2, 8),
        (3, 9),
    ] {
        let mut broken = interface.clone();
        broken.returns[tag].registers.retain(|r| r.0 != register);
        assert_eq!(
            broken.validate(),
            Err(ExtractionError::LiveOut),
            "tag={tag} register={register}"
        );
    }
    let mut broken = interface.clone();
    broken.returns[0].value = 1;
    assert_eq!(broken.validate(), Err(ExtractionError::LiveOut));
    let mut broken = interface.clone();
    broken.stops.swap(0, 1);
    assert_eq!(broken.validate(), Err(ExtractionError::LiveOut));
    let mut broken = interface;
    broken.returns[0].registers.push(Reg(99));
    assert_eq!(broken.validate(), Err(ExtractionError::LiveOut));
}

#[test]
fn sequential_writes_kill_old_values_and_identity_copies_keep_future_reads_live() {
    let source = Program::new(
        0,
        3,
        vec![
            IrInstruction {
                address: 0,
                size: 1,
                assignments: vec![],
                control: Control::Jump(10),
            },
            IrInstruction {
                address: 10,
                size: 1,
                assignments: vec![
                    Assignment {
                        destination: Reg(0).into(),
                        value: Expr::Const(7),
                    },
                    Assignment {
                        destination: Reg(1).into(),
                        value: Expr::Register(Reg(1)),
                    },
                    Assignment {
                        destination: Reg(2).into(),
                        value: Expr::Register(Reg(0)),
                    },
                ],
                control: Control::Branch {
                    condition: Expr::Register(Reg(1)),
                    target: 10,
                },
            },
            IrInstruction {
                address: 11,
                size: 1,
                assignments: vec![],
                control: Control::Return(Expr::Register(Reg(2))),
            },
        ],
    )
    .unwrap();
    let interface = derive(&extract(&source, 0, &[10], None).unwrap()).unwrap();
    assert_eq!(interface.returns[0].registers, [Reg(1), Reg(3)]);
    let mut work = 0;
    assert_eq!(
        reads_before_write(
            &source,
            &shape::bounded_successors(&source).unwrap(),
            10,
            Reg(1),
            &mut work
        ),
        Err(ExtractionError::Region(Error::Limit))
    );
    let mut broken = interface;
    broken.returns[0].registers.retain(|r| *r != Reg(1));
    assert_eq!(broken.validate(), Err(ExtractionError::LiveOut));
}

#[test]
fn interface_count_bound_declines_without_publishing_partial_rows() {
    let source = Program::new(
        0,
        1,
        (0..=MAX_CONTINUATIONS)
            .map(|n| IrInstruction {
                address: n as u64,
                size: 1,
                assignments: vec![],
                control: Control::Return(Expr::Const(0)),
            })
            .collect(),
    )
    .unwrap();
    let region = extract(
        &source,
        0,
        &(0..=MAX_CONTINUATIONS as u64).collect::<Vec<_>>(),
        None,
    )
    .unwrap();
    assert!(matches!(
        derive(&region),
        Err(ExtractionError::Region(Error::Limit))
    ));
}

#[test]
fn omitted_initial_values_do_not_change_continuation_returns_ram_or_first_fault() {
    let source = fixture();
    let interface = derive(&extract(&source, 0, &[10, 11, 20], None).unwrap()).unwrap();
    for (tag, pc) in [10, 11, 20].into_iter().enumerate() {
        let continuation = Program::new(pc, 9, source.instructions().to_vec()).unwrap();
        for seed in 0..64u64 {
            let mut input: Vec<_> = (0..9)
                .map(|n| seed.wrapping_mul(0x9e3779b97f4a7c15).wrapping_add(n))
                .collect();
            input[0] = if seed & 4 == 0 { 100 } else { u64::MAX };
            input[5] = if seed & 8 == 0 { 108 } else { 99 };
            input[3] = seed & 1;
            input[7] = seed & 2;
            let memory: Vec<_> = (0..16).map(|n| (n * 23 + 11) as u8).collect();
            let expected = continuation
                .run_with_memory(&input, 100, &memory, 128)
                .unwrap();
            for reg in 0..9 {
                if interface.returns[tag].registers.contains(&Reg(reg)) {
                    continue;
                }
                let mut changed = input.clone();
                changed[reg] = !changed[reg];
                let actual = continuation
                    .run_with_memory(&changed, 100, &memory, 128)
                    .unwrap();
                assert_eq!(
                    actual.status, expected.status,
                    "pc={pc} seed={seed} reg={reg}"
                );
                assert_eq!(actual.state.memory, expected.state.memory);
                assert_eq!(actual.state.trace, expected.state.trace);
            }
        }
    }
}

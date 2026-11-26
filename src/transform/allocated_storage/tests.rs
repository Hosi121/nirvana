use super::*;
use crate::model::ir::{Assignment, BinaryOp, Control, Expr, IrInstruction, Place, Width};
fn fixture() -> Program {
    let r = |n| Expr::Register(Reg(n));
    Program::new(
        0,
        6,
        vec![
            IrInstruction {
                address: 0,
                size: 1,
                assignments: vec![
                    Assignment {
                        destination: Reg(4).into(),
                        value: Expr::binary(BinaryOp::Add, r(0), Expr::Const(8)),
                    },
                    Assignment {
                        destination: Place::Memory {
                            address: r(4),
                            width: Width::U64,
                        },
                        value: r(3),
                    },
                    Assignment {
                        destination: Reg(1).into(),
                        value: Expr::load(r(0), Width::U64),
                    },
                    Assignment {
                        destination: Reg(2).into(),
                        value: r(1),
                    },
                ],
                control: Control::Branch {
                    condition: r(3),
                    target: 2,
                },
            },
            IrInstruction {
                address: 1,
                size: 1,
                assignments: vec![Assignment {
                    destination: Reg(2).into(),
                    value: Expr::select(
                        r(3),
                        Expr::load(Expr::Const(u64::MAX), Width::U64),
                        Expr::binary(BinaryOp::Add, r(2), Expr::Const(1)),
                    ),
                }],
                control: Control::Jump(3),
            },
            IrInstruction {
                address: 2,
                size: 1,
                assignments: vec![Assignment {
                    destination: Reg(2).into(),
                    value: Expr::binary(BinaryOp::Add, r(2), Expr::load(r(4), Width::U64)),
                }],
                control: Control::Jump(3),
            },
            IrInstruction {
                address: 3,
                size: 1,
                assignments: vec![],
                control: Control::Return(r(2)),
            },
        ],
    )
    .unwrap()
}
fn mapping() -> Vec<(Reg, usize)> {
    vec![
        (Reg(1), usize::MAX - 1),
        (Reg(2), usize::MAX - 1),
        (Reg(4), 7),
    ]
}
#[test]
fn checked_storage_retains_effects_faults_and_every_pc_and_budget_with_poison_slots() {
    let source = fixture();
    let lowered = lower(&source, &mapping()).unwrap();
    assert_eq!(lowered.program().register_count(), 8);
    assert_eq!(lowered.renamed_register(Reg(0)), Some(Reg(0)));
    assert_eq!(
        lowered.renamed_register(Reg(1)),
        lowered.renamed_register(Reg(2))
    );
    assert_eq!(lowered.renamed_register(Reg(6)), None);
    for pointer in [100, 99, 92, u64::MAX] {
        for size in [0, 7, 8, 16, 24] {
            for argument in [0, 1, u64::MAX] {
                for poison in [0, u64::MAX] {
                    let input = [pointer, 17, 19, argument, 23, 29];
                    let extended = lowered.extend_input(&input, poison).unwrap();
                    let memory: Vec<_> = (0..size).map(|i| (i * 29 + 7) as u8).collect();
                    for budget in 0..7 {
                        let expected = source
                            .run_with_memory(&input, 100, &memory, budget)
                            .unwrap();
                        let actual = lowered
                            .program()
                            .run_with_memory(&extended, 100, &memory, budget)
                            .unwrap();
                        assert_eq!(actual.status, expected.status);
                        assert_eq!(actual.state.memory, expected.state.memory);
                        assert_eq!(actual.state.trace, expected.state.trace);
                        assert_eq!(actual.state.instruction, expected.state.instruction);
                        assert_eq!(actual.state.memory_layout, expected.state.memory_layout);
                    }
                }
            }
        }
    }
    assert_eq!(lowered.extend_input(&[0; 5], 0), Err(Error::Input));
}
#[test]
fn live_inputs_interfering_colors_and_miscompiled_destinations_are_rejected() {
    let source = fixture();
    assert!(matches!(
        lower(&source, &[(Reg(0), 0)]),
        Err(Error::Allocation(_))
    ));
    assert!(matches!(
        lower(&source, &[(Reg(1), 0), (Reg(2), 0), (Reg(4), 0)]),
        Err(Error::Allocation(_))
    ));
    let lowered = lower(&source, &mapping()).unwrap();
    let mut aliased = lowered.clone();
    aliased.names.insert(1, Reg(0));
    assert_eq!(aliased.validate(), Err(Error::Correspondence));
    let mut collided = lowered.clone();
    collided.names.insert(4, lowered.names[&1]);
    assert_eq!(collided.validate(), Err(Error::Correspondence));
    let mut bad = lowered.clone();
    let mut is = bad.program.instructions().to_vec();
    is[0].assignments[1].value = Expr::Const(0);
    bad.program = Program::new(0, 8, is).unwrap();
    assert_eq!(bad.validate(), Err(Error::Correspondence));
    let mut evidence = lowered.clone();
    evidence.evidence.register_reads += 1;
    assert_eq!(evidence.validate(), Err(Error::Correspondence));
}
#[test]
fn empty_allocation_is_identity_and_namespace_limits_precede_cloning() {
    let source = fixture();
    let identity = lower(&source, &[]).unwrap();
    assert_eq!(identity.program().instructions(), source.instructions());
    assert_eq!(identity.program().register_count(), source.register_count());
    let huge = Program::new(
        0,
        MAX_REGISTERS + 1,
        vec![IrInstruction {
            address: 0,
            size: 1,
            assignments: vec![],
            control: Control::Return(Expr::Const(0)),
        }],
    )
    .unwrap();
    assert!(matches!(lower(&huge, &[]), Err(Error::Limit)));
    let mut deep = Expr::Const(0);
    for _ in 0..allocation_verify::MAX_EXPRESSION_DEPTH + 2 {
        deep = Expr::unary(crate::model::ir::UnaryOp::SignExtend(Width::U8), deep);
    }
    let deep = Program::new(
        0,
        1,
        vec![IrInstruction {
            address: 0,
            size: 1,
            assignments: vec![],
            control: Control::Return(deep),
        }],
    )
    .unwrap();
    assert!(matches!(
        lower(&deep, &[]),
        Err(Error::Allocation(AllocationError::Unavailable { .. }))
    ));
}

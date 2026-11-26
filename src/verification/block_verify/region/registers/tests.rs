use super::*;
use crate::model::ir::{Assignment, BinaryOp, Width};

fn fixture() -> Program {
    let r = |n| Expr::Register(Reg(n));
    Program::new(
        10,
        740,
        vec![
            IrInstruction {
                address: 10,
                size: 1,
                assignments: vec![
                    Assignment {
                        destination: Reg(739).into(),
                        value: Expr::select(r(319), Expr::load(r(7), Width::U64), r(0)),
                    },
                    Assignment {
                        destination: Place::Memory {
                            address: Expr::binary(BinaryOp::Add, r(7), Expr::Const(8)),
                            width: Width::U64,
                        },
                        value: r(739),
                    },
                    Assignment {
                        destination: Reg(300).into(),
                        value: Expr::binary(BinaryOp::Add, r(739), Expr::Const(1)),
                    },
                ],
                control: Control::Next,
            },
            IrInstruction {
                address: 11,
                size: 1,
                assignments: vec![],
                control: Control::Branch {
                    condition: Expr::load(
                        Expr::binary(BinaryOp::Add, r(7), Expr::Const(16)),
                        Width::U8,
                    ),
                    target: 12,
                },
            },
            IrInstruction {
                address: 12,
                size: 1,
                assignments: vec![],
                control: Control::Return(r(300)),
            },
        ],
    )
    .unwrap()
}
#[test]
fn sparse_projection_preserves_full_reports_at_every_budget_and_fault_boundary() {
    let source = fixture();
    let compact = compact(&source).unwrap();
    assert_eq!(compact.program().register_count(), 5);
    assert_eq!(compact.dense_register(Reg(739)), Some(Reg(4)));
    assert_eq!(compact.dense_register(Reg(738)), None);
    for pointer in [100, 99, u64::MAX] {
        for size in [0, 7, 8, 16, 17, 24] {
            for condition in [0, 1] {
                for value in [0, u64::MAX] {
                    let mut input: Vec<_> = (0..740).map(|i| i as u64 * 0x1234_5678_9abc).collect();
                    input[7] = pointer;
                    input[319] = condition;
                    input[0] = value;
                    let dense = compact.project_input(&input).unwrap();
                    let memory: Vec<_> = (0..size).map(|n| (n * 29 + 7) as u8).collect();
                    for budget in 0..5 {
                        let expected = source
                            .run_with_memory(&input, 100, &memory, budget)
                            .unwrap();
                        let mut actual = compact
                            .program()
                            .run_with_memory(&dense, 100, &memory, budget)
                            .unwrap();
                        actual.state.registers = compact
                            .restore_registers(&input, &actual.state.registers)
                            .unwrap();
                        assert_eq!(actual, expected);
                    }
                }
            }
        }
    }
    assert!(compact.project_input(&[0; 8]).is_err());
    assert!(compact.project_input(&[0; 741]).is_err());
    assert!(compact.restore_registers(&[], &[0; 4]).is_err());
}

fn edit(compact: &Compact, change: impl FnOnce(&mut Vec<IrInstruction>)) -> Compact {
    let mut bad = compact.clone();
    let mut is = bad.program.instructions().to_vec();
    change(&mut is);
    bad.program = Program::new(10, bad.program.register_count(), is).unwrap();
    bad
}
#[test]
fn independent_checker_rejects_aliasing_operands_effects_and_dropped_control_loads() {
    // Missing an original register must never fall back to an aliased dense ID.
    let source = Program::new(
        0,
        2,
        vec![IrInstruction {
            address: 0,
            size: 1,
            assignments: vec![Assignment {
                destination: Reg(0).into(),
                value: Expr::Register(Reg(1)),
            }],
            control: Control::Return(Expr::Register(Reg(0))),
        }],
    )
    .unwrap();
    let candidate = Program::new(
        0,
        1,
        vec![IrInstruction {
            address: 0,
            size: 1,
            assignments: vec![Assignment {
                destination: Reg(0).into(),
                value: Expr::Register(Reg(0)),
            }],
            control: Control::Return(Expr::Register(Reg(0))),
        }],
    )
    .unwrap();
    let missing = Compact {
        source,
        program: candidate,
        registers: vec![Reg(1)],
    };
    assert_eq!(missing.validate(), Err(Error::BoundaryMapping));

    let compact = compact(&fixture()).unwrap();
    let mut aliased = compact.clone();
    aliased.registers[0] = aliased.registers[1];
    assert_eq!(aliased.validate(), Err(Error::BoundaryMapping));
    for bad in [
        edit(&compact, |is| is[0].assignments[0].value = Expr::Const(0)),
        edit(&compact, |is| {
            is[0].assignments[1].destination = Place::Memory {
                address: Expr::Const(0),
                width: Width::U8,
            }
        }),
        edit(&compact, |is| is[1].control = Control::Jump(12)),
        edit(&compact, |is| {
            is[2].control = Control::Return(Expr::Register(Reg(0)))
        }),
    ] {
        assert_eq!(bad.validate(), Err(Error::BoundaryMapping));
    }
}
#[test]
fn unused_slots_restore_inputs_and_query_and_source_bounds_remain_distinct() {
    let constant = |count| {
        Program::new(
            0,
            count,
            vec![IrInstruction {
                address: 0,
                size: 1,
                assignments: vec![],
                control: Control::Return(Expr::Const(7)),
            }],
        )
        .unwrap()
    };
    let projected = compact(&constant(740)).unwrap();
    assert!(projected.registers().is_empty());
    let mut input = vec![0; 740];
    input[0] = 17;
    input[1] = 19;
    let restored = projected.restore_registers(&input, &[]).unwrap();
    assert_eq!(&restored[..3], &[17, 19, 0]);
    assert_eq!(restored.len(), 740);
    assert!(matches!(
        compact(&constant(MAX_SOURCE_REGISTERS + 1)),
        Err(Error::Limit)
    ));
    let crowded = Program::new(
        0,
        740,
        vec![IrInstruction {
            address: 0,
            size: 1,
            assignments: (0..=MAX_REGISTERS)
                .map(|id| Assignment {
                    destination: Reg(id).into(),
                    value: Expr::Const(0),
                })
                .collect(),
            control: Control::Return(Expr::Const(0)),
        }],
    )
    .unwrap();
    assert!(matches!(compact(&crowded), Err(Error::Limit)));
    assert!(matches!(
        super::super::query(projected.source(), projected.source(), &[], &[]),
        Err(Error::Limit)
    ));
    assert!(super::super::query(projected.program(), projected.program(), &[], &[]).is_ok());
}

#[test]
fn comparison_uses_one_map_for_different_register_uses_and_boundary_only_slots() {
    let returning = |reg| {
        Program::new(
            0,
            740,
            vec![IrInstruction {
                address: 0,
                size: 1,
                assignments: vec![],
                control: Control::Return(Expr::Register(Reg(reg))),
            }],
        )
        .unwrap()
    };
    let left = returning(319);
    let right = returning(739);
    let comparison = compact_comparison(&left, &right, &[Reg(319), Reg(739)], &[Reg(500)]).unwrap();
    assert_eq!(comparison.before.registers(), comparison.after.registers());
    assert!(comparison.query().is_ok());
    let mut input = vec![0; 740];
    input[319] = 7;
    input[739] = 9;
    input[500] = u64::MAX;
    let left = comparison
        .before
        .program()
        .execute(&comparison.before.project_input(&input).unwrap(), 1)
        .unwrap();
    let right = comparison
        .after
        .program()
        .execute(&comparison.after.project_input(&input).unwrap(), 1)
        .unwrap();
    assert_eq!((left.value, right.value), (7, 9));
    assert_eq!(
        comparison
            .before
            .restore_registers(&input, &left.registers)
            .unwrap()[500],
        u64::MAX
    );
    assert!(matches!(
        compact_comparison(&fixture(), &returning(319), &[Reg(740)], &[]),
        Err(Error::BoundaryMapping)
    ));
    let short = Program::new(
        0,
        1,
        vec![IrInstruction {
            address: 0,
            size: 1,
            assignments: vec![],
            control: Control::Return(Expr::Const(0)),
        }],
    )
    .unwrap();
    assert!(matches!(
        compact_comparison(&short, &returning(319), &[], &[]),
        Err(Error::BoundaryMapping)
    ));
}

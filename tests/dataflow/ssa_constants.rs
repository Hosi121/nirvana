use crate::support::ir::c;
use crate::support::ir::r;
use nirvana::ir::{
    Assignment, BinaryOp as B, Control, Expr, IrInstruction, Place, Program, Reg, Width,
};
use nirvana::ssa::{Definition, Site};
use nirvana::ssa_constants::{self, ConstantPlan, ConstantValue as V};
fn b(op: B, a: Expr, z: Expr) -> Expr {
    Expr::binary(op, a, z)
}
fn set(i: usize, value: Expr) -> Assignment {
    Assignment {
        destination: Reg(i).into(),
        value,
    }
}
fn ins(address: u64, assignments: Vec<Assignment>, control: Control) -> IrInstruction {
    IrInstruction {
        address,
        size: 1,
        assignments,
        control,
    }
}
fn program(instructions: Vec<IrInstruction>) -> Program {
    Program::new(0, 8, instructions).unwrap()
}
fn diamond(value: u64, op: B, operand: u64) -> Program {
    program(vec![
        ins(
            0,
            vec![],
            Control::Branch {
                condition: r(0),
                target: 2,
            },
        ),
        ins(1, vec![set(1, c(value))], Control::Jump(3)),
        ins(2, vec![set(1, c(value))], Control::Jump(3)),
        ins(
            3,
            vec![set(2, b(op, r(1), c(operand)))],
            Control::Return(r(2)),
        ),
    ])
}
fn invariant_loop() -> Program {
    program(vec![
        ins(
            0,
            vec![set(1, c(7)), set(2, b(B::And, r(0), c(7))), set(3, c(0))],
            Control::Jump(1),
        ),
        ins(
            1,
            vec![],
            Control::Branch {
                condition: b(B::Eq, r(2), c(0)),
                target: 3,
            },
        ),
        ins(
            2,
            vec![
                set(3, b(B::Add, r(3), r(1))),
                set(1, r(1)),
                set(2, b(B::Sub, r(2), c(1))),
            ],
            Control::Jump(1),
        ),
        ins(3, vec![], Control::Return(r(3))),
    ])
}
fn compare(source: &Program, candidate: &Program) {
    for input in [0, 1, 2, 7, 1 << 63, u64::MAX] {
        for address in [4096, 4097, 4104, 4112, 4120, 4127, u64::MAX] {
            let mut registers = [0; 8];
            registers[0] = input;
            registers[7] = address;
            let memory: Vec<_> = (0..32).map(|i| (i * 29 + 7) as u8).collect();
            for limit in [0, 1, 2, 8, 32, 100] {
                let a = source
                    .run_with_memory(&registers, 4096, &memory, limit)
                    .unwrap();
                let z = candidate
                    .run_with_memory(&registers, 4096, &memory, limit)
                    .unwrap();
                assert_eq!(a.status, z.status);
                assert_eq!(a.state.memory, z.state.memory);
                assert_eq!(a.state.trace, z.state.trace);
            }
        }
    }
}
#[test]
fn equal_diamond_values_fold_after_a_real_phi() {
    let source = diamond(7, B::Add, 5);
    let plan = ConstantPlan::analyze(&source).unwrap();
    let (candidate, evidence) = plan.propose(&source).unwrap();
    assert!(evidence.replacements > 0);
    assert_eq!(candidate.instructions()[3].assignments[0].value, c(12));
    assert_eq!(candidate.instructions()[3].control, Control::Return(c(12)));
    let phi = plan
        .graph()
        .values
        .iter()
        .position(|v| {
            matches!(
                v,
                Definition::Phi {
                    block: 3,
                    register: Reg(1),
                    ..
                }
            )
        })
        .unwrap();
    assert_eq!(plan.values()[phi], V::Known(7));
    compare(&source, &candidate);
}
#[test]
fn conflicting_paths_and_arbitrary_initial_registers_stay_unknown() {
    let mut instructions = diamond(7, B::Add, 5).instructions().to_vec();
    instructions[2].assignments[0].value = c(8);
    let source = program(instructions);
    let plan = ConstantPlan::analyze(&source).unwrap();
    let phi = plan
        .graph()
        .values
        .iter()
        .position(|v| {
            matches!(
                v,
                Definition::Phi {
                    block: 3,
                    register: Reg(1),
                    ..
                }
            )
        })
        .unwrap();
    assert_eq!(plan.values()[phi], V::Unknown);
    if let Some((candidate, _)) = plan.propose(&source) {
        compare(&source, &candidate);
    }
    let unknown = program(vec![ins(
        0,
        vec![set(1, b(B::Add, r(0), c(1)))],
        Control::Return(r(1)),
    )]);
    assert!(
        ConstantPlan::analyze(&unknown)
            .unwrap()
            .propose(&unknown)
            .is_none()
    );
}
#[test]
fn loop_invariant_phi_converges_but_recurrence_counter_stays_unknown() {
    let source = invariant_loop();
    let plan = ConstantPlan::analyze(&source).unwrap();
    let mut invariant = false;
    let mut counter = false;
    for (i, v) in plan.graph().values.iter().enumerate() {
        match v {
            Definition::Phi {
                block: 1,
                register: Reg(1),
                ..
            } => {
                invariant = true;
                assert_eq!(plan.values()[i], V::Known(7));
            }
            Definition::Phi {
                block: 1,
                register: Reg(2),
                ..
            } => {
                counter = true;
                assert_eq!(plan.values()[i], V::Unknown);
            }
            _ => {}
        }
    }
    assert!(invariant && counter);
    let (candidate, _) = plan.propose(&source).unwrap();
    compare(&source, &candidate);
}
#[test]
fn entry_backedge_cannot_prove_a_self_supporting_constant() {
    let source = program(vec![
        ins(
            0,
            vec![set(0, b(B::Add, r(0), c(1)))],
            Control::Branch {
                condition: r(2),
                target: 0,
            },
        ),
        ins(1, vec![], Control::Return(r(0))),
    ]);
    let plan = ConstantPlan::analyze(&source).unwrap();
    let mut forged = plan.values().to_vec();
    for (i, d) in plan.graph().values.iter().enumerate() {
        if matches!(
            d,
            Definition::Phi {
                register: Reg(0),
                ..
            } | Definition::Assignment {
                register: Reg(0),
                ..
            }
        ) {
            forged[i] = V::Known(42);
        }
    }
    assert!(ssa_constants::validate_facts(&source, plan.graph(), &forged).is_err());
    for (i, d) in plan.graph().values.iter().enumerate() {
        if matches!(d, Definition::Initial { .. }) {
            let mut bad = plan.values().to_vec();
            bad[i] = V::Known(0);
            assert!(ssa_constants::validate_facts(&source, plan.graph(), &bad).is_err());
        }
    }
}
#[test]
fn every_operator_and_masked_shift_agree_with_wrapping_ir_at_boundaries() {
    for op in [
        B::Add,
        B::Sub,
        B::Mul,
        B::And,
        B::Or,
        B::Xor,
        B::Shl,
        B::Shr,
        B::Eq,
        B::Ne,
        B::Ult,
        B::Ule,
        B::UMulHigh,
    ] {
        for (value, operand) in [
            (0, 0),
            (1, 65),
            (u64::MAX, 64),
            (1 << 63, u64::MAX),
            (u64::MAX - 1, 3),
        ] {
            let source = diamond(value, op, operand);
            let plan = ConstantPlan::analyze(&source).unwrap();
            let (candidate, _) = plan.propose(&source).unwrap();
            for flag in [0, 1] {
                let mut inputs = [0; 8];
                inputs[0] = flag;
                assert_eq!(
                    source.execute(&inputs, 16).unwrap().value,
                    candidate.execute(&inputs, 16).unwrap().value
                );
            }
        }
    }
}
#[test]
fn later_constant_use_keeps_faulting_load_and_lazy_load_syntax() {
    let source = program(vec![ins(
        0,
        vec![set(
            1,
            Expr::select(Expr::load(r(7), Width::U64), c(7), c(7)),
        )],
        Control::Return(r(1)),
    )]);
    let plan = ConstantPlan::analyze(&source).unwrap();
    let (candidate, _) = plan.propose(&source).unwrap();
    assert_eq!(
        candidate.instructions()[0].assignments,
        source.instructions()[0].assignments
    );
    assert_eq!(candidate.instructions()[0].control, Control::Return(c(7)));
    compare(&source, &candidate);
    let mut bad = candidate.instructions().to_vec();
    bad[0].assignments[0].value = c(7);
    let bad = program(bad);
    assert!(ssa_constants::validate(&source, plan.graph(), plan.values(), &bad).is_err());
    let source = program(vec![ins(
        0,
        vec![
            set(1, c(0)),
            set(2, Expr::select(r(1), Expr::load(r(7), Width::U64), c(11))),
        ],
        Control::Return(r(2)),
    )]);
    let plan = ConstantPlan::analyze(&source).unwrap();
    let (candidate, _) = plan.propose(&source).unwrap();
    assert!(matches!(
        candidate.instructions()[0].assignments[1].value,
        Expr::Select { .. }
    ));
    compare(&source, &candidate);
}
#[test]
fn destination_check_precedes_rhs_fault_and_prior_stores_survive() {
    let source = program(vec![ins(
        0,
        vec![
            set(1, c(7)),
            Assignment {
                destination: Place::Memory {
                    address: r(7),
                    width: Width::U8,
                },
                value: r(1),
            },
            Assignment {
                destination: Place::Memory {
                    address: b(B::Add, r(7), c(8)),
                    width: Width::U64,
                },
                value: Expr::load(c(u64::MAX), Width::U64),
            },
        ],
        Control::Return(r(1)),
    )]);
    let plan = ConstantPlan::analyze(&source).unwrap();
    let (candidate, _) = plan.propose(&source).unwrap();
    compare(&source, &candidate);
}
#[test]
fn checker_rejects_false_facts_mutated_effects_and_changed_control_destinations() {
    let source = diamond(7, B::Add, 5);
    let plan = ConstantPlan::analyze(&source).unwrap();
    let (candidate, _) = plan.propose(&source).unwrap();
    let mut bad = candidate.instructions().to_vec();
    bad[3].control = Control::Return(c(13));
    assert!(ssa_constants::validate(&source, plan.graph(), plan.values(), &program(bad)).is_err());
    let mut bad = candidate.instructions().to_vec();
    bad[0].control = Control::Branch {
        condition: r(0),
        target: 3,
    };
    assert!(ssa_constants::validate(&source, plan.graph(), plan.values(), &program(bad)).is_err());
    let mut bad = candidate.instructions().to_vec();
    bad[1].assignments.clear();
    assert!(ssa_constants::validate(&source, plan.graph(), plan.values(), &program(bad)).is_err());
    let mut facts = plan.values().to_vec();
    let point = plan
        .graph()
        .point(Site {
            instruction: 3,
            assignment: Some(0),
        })
        .unwrap();
    facts[point.definition.unwrap().0] = V::Known(13);
    assert!(ssa_constants::validate_facts(&source, plan.graph(), &facts).is_err());
    let mut graph = plan.graph().clone();
    graph.blocks.clear();
    assert!(ssa_constants::validate(&source, &graph, plan.values(), &candidate).is_err());
}

use nirvana::ir::{
    AccessKind, Assignment, Control, ExecutionError, Expr, IrInstruction, MemoryFault, Place,
    Program, Reg, RunStatus, Width,
};
use nirvana::observe::{Comparison, Contract, Difference};
use nirvana::structure::StructuredFunction;

fn set(index: usize, value: Expr) -> Assignment {
    Assignment {
        destination: Reg(index).into(),
        value,
    }
}
fn store(address: Expr, value: Expr) -> Assignment {
    Assignment {
        destination: Place::Memory {
            address,
            width: Width::U8,
        },
        value,
    }
}
fn program(assignments: Vec<Assignment>, control: Control) -> Program {
    Program::new(
        0,
        2,
        vec![IrInstruction {
            address: 0,
            size: 1,
            assignments,
            control,
        }],
    )
    .unwrap()
}
fn fault(access: AccessKind, address: u64, width: Width) -> RunStatus {
    RunStatus::Fault(MemoryFault {
        access,
        address,
        width,
    })
}

#[test]
fn faults_retain_partial_instruction_writes_and_leave_failed_destination_untouched() {
    let p = program(
        vec![
            set(0, Expr::Const(42)),
            store(Expr::Const(4096), Expr::Const(99)),
            set(1, Expr::load(Expr::Const(4097), Width::U64)),
            store(Expr::Const(4096), Expr::Const(200)),
        ],
        Control::Return(Expr::Const(0)),
    );
    let report = p.run_with_memory(&[3, 7], 4096, &[0; 8], 1).unwrap();
    assert_eq!(report.status, fault(AccessKind::Read, 4097, Width::U64));
    assert_eq!(report.state.registers, [42, 7]);
    assert_eq!(report.state.memory, [99, 0, 0, 0, 0, 0, 0, 0]);
    assert_eq!(report.state.memory_base, 4096);
    assert_eq!(report.state.trace, [0]);
    assert_eq!(report.state.instruction, Some(0));
}

#[test]
fn identical_legacy_errors_can_hide_different_pre_fault_memory() {
    let make = |byte| {
        program(
            vec![
                store(Expr::Const(0), Expr::Const(byte)),
                set(0, Expr::load(Expr::Const(100), Width::U8)),
            ],
            Control::Return(Expr::Const(7)),
        )
    };
    let a = make(1);
    let b = make(2);
    assert_eq!(
        a.execute_with_memory(&[0; 2], 0, &[0], 1),
        b.execute_with_memory(&[0; 2], 0, &[0], 1)
    );
    let left = a.run_with_memory(&[0; 2], 0, &[0], 1).unwrap();
    let right = b.run_with_memory(&[0; 2], 0, &[0], 1).unwrap();
    assert_eq!(
        Contract::return_memory().compare(&left, &right),
        Comparison::Counterexample(Difference::MemoryByte {
            offset: 0,
            left: 1,
            right: 2
        })
    );
}

#[test]
fn load_fault_and_store_fault_at_the_same_address_are_distinct() {
    let a = program(
        vec![set(0, Expr::load(Expr::Const(100), Width::U8))],
        Control::Return(Expr::Const(0)),
    );
    let b = program(
        vec![store(Expr::Const(100), Expr::Const(0))],
        Control::Return(Expr::Const(0)),
    );
    let a = a.run_with_memory(&[0; 2], 0, &[0], 1).unwrap();
    let b = b.run_with_memory(&[0; 2], 0, &[0], 1).unwrap();
    assert_eq!(a.status, fault(AccessKind::Read, 100, Width::U8));
    assert_eq!(b.status, fault(AccessKind::Write, 100, Width::U8));
    assert!(matches!(
        Contract::return_memory().compare(&a, &b),
        Comparison::Counterexample(Difference::Status { .. })
    ));
}

#[test]
fn store_address_and_bounds_are_checked_before_evaluating_the_value() {
    let value = Expr::load(Expr::Const(200), Width::U16);
    let p = program(
        vec![store(Expr::Const(100), value.clone())],
        Control::Return(Expr::Const(0)),
    );
    assert_eq!(
        p.run_with_memory(&[0; 2], 0, &[0], 1).unwrap().status,
        fault(AccessKind::Write, 100, Width::U8)
    );
    let p = program(
        vec![store(Expr::load(Expr::Const(100), Width::U32), value)],
        Control::Return(Expr::Const(0)),
    );
    assert_eq!(
        p.run_with_memory(&[0; 2], 0, &[0], 1).unwrap().status,
        fault(AccessKind::Read, 100, Width::U32)
    );
}

#[test]
fn cutoff_keeps_the_prefix_but_is_not_success_or_proven_divergence() {
    let looping = program(
        vec![store(Expr::Const(0), Expr::Const(1))],
        Control::Jump(0),
    );
    let returning = program(vec![], Control::Return(Expr::Const(42)));
    let zero = looping.run_with_memory(&[5, 6], 0, &[0], 0).unwrap();
    assert_eq!(zero.status, RunStatus::Suspended);
    assert!(zero.state.trace.is_empty());
    assert_eq!(zero.state.instruction, Some(0));
    assert_eq!(zero.state.registers, [5, 6]);
    assert_eq!(zero.state.memory, [0]);
    let looped = looping.run_with_memory(&[5, 6], 0, &[0], 3).unwrap();
    assert_eq!(looped.state.trace, [0, 0, 0]);
    assert_eq!(looped.state.memory, [1]);
    let done = returning.run_with_memory(&[5, 6], 0, &[0], 3).unwrap();
    assert_eq!(
        Contract::return_memory().compare(&looped, &looped),
        Comparison::Inconclusive {
            left_suspended: true,
            right_suspended: true
        }
    );
    assert_eq!(
        Contract::return_memory().compare(&looped, &done),
        Comparison::Inconclusive {
            left_suspended: true,
            right_suspended: false
        }
    );
}

#[test]
fn contracts_distinguish_register_observation_and_instruction_provenance() {
    let a = program(
        vec![set(0, Expr::Const(1))],
        Control::Return(Expr::Const(7)),
    );
    let b = program(
        vec![set(0, Expr::Const(2))],
        Control::Return(Expr::Const(7)),
    );
    let a = a.run_with_memory(&[0; 2], 0, &[], 1).unwrap();
    let b = b.run_with_memory(&[0; 2], 0, &[], 1).unwrap();
    assert_eq!(
        Contract::return_memory().compare(&a, &b),
        Comparison::MatchForInput
    );
    assert!(matches!(
        Contract::full_ir_state().compare(&a, &b),
        Comparison::Counterexample(Difference::Register { index: 0, .. })
    ));
    let p = Program::new(
        10,
        2,
        vec![IrInstruction {
            address: 10,
            size: 1,
            assignments: vec![],
            control: Control::Return(Expr::Const(7)),
        }],
    )
    .unwrap();
    let moved = p.run_with_memory(&[0; 2], 0, &[], 1).unwrap();
    assert_eq!(
        Contract::return_memory().compare(&a, &moved),
        Comparison::MatchForInput
    );
    assert!(matches!(
        Contract::return_memory()
            .with_instruction_trace()
            .compare(&a, &moved),
        Comparison::Counterexample(Difference::InstructionTrace { .. })
    ));
    assert_eq!(Contract::return_memory().id(), "return-memory-v1");
}

#[test]
fn structured_execution_retains_fault_control_and_cutoff_states() {
    for control in [
        Control::Return(Expr::load(Expr::Const(100), Width::U8)),
        Control::Branch {
            condition: Expr::load(Expr::Const(100), Width::U8),
            target: 1,
        },
    ] {
        let p = Program::new(
            0,
            2,
            vec![
                IrInstruction {
                    address: 0,
                    size: 1,
                    assignments: vec![store(Expr::Const(0), Expr::Const(99))],
                    control,
                },
                IrInstruction {
                    address: 1,
                    size: 1,
                    assignments: vec![],
                    control: Control::Return(Expr::Const(7)),
                },
            ],
        )
        .unwrap();
        let tree = StructuredFunction::recover(&p).unwrap();
        for limit in [0, 1, 2] {
            assert_eq!(
                p.run_with_memory(&[0; 2], 0, &[0], limit),
                tree.run_with_memory(&[0; 2], 0, &[0], limit)
            );
        }
    }
}

#[test]
fn reports_keep_legacy_success_and_error_behavior_and_reject_bad_input_shapes() {
    for p in [
        program(vec![], Control::Return(Expr::Const(7))),
        program(
            vec![],
            Control::Return(Expr::load(Expr::Const(100), Width::U64)),
        ),
    ] {
        for limit in [0, 1] {
            let report = p.run_with_memory(&[0; 2], 0, &[0], limit).unwrap();
            assert_eq!(
                report.into_execution(),
                p.execute_with_memory(&[0; 2], 0, &[0], limit)
            );
        }
        assert_eq!(
            p.run_with_memory(&[], 0, &[], 1),
            Err(ExecutionError::RegisterCount {
                expected: 2,
                actual: 0
            })
        );
    }
}

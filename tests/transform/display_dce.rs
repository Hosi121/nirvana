use nirvana::display_dce::{propose, validate};
use nirvana::ir::{
    AccessKind, Assignment, BinaryOp, Control, Expr, IrInstruction, MemoryFault, Place, Program,
    Reg, RunStatus, Width,
};

use crate::support::ir::c;
use crate::support::ir::r;
fn op(op: BinaryOp, a: Expr, b: Expr) -> Expr {
    Expr::binary(op, a, b)
}
fn write(register: usize, value: Expr) -> Assignment {
    Assignment {
        destination: Reg(register).into(),
        value,
    }
}
fn store(address: Expr, width: Width, value: Expr) -> Assignment {
    Assignment {
        destination: Place::Memory { address, width },
        value,
    }
}
fn instruction(address: u64, assignments: Vec<Assignment>, control: Control) -> IrInstruction {
    IrInstruction {
        address,
        size: 1,
        assignments,
        control,
    }
}
fn program(registers: usize, instructions: Vec<IrInstruction>) -> Program {
    Program::new(0, registers, instructions).unwrap()
}
fn rebuild(source: &Program, instructions: Vec<IrInstruction>) -> Program {
    Program::new(
        source.cfg().block(source.cfg().entry()).start,
        source.register_count(),
        instructions,
    )
    .unwrap()
}
fn candidate(source: &Program) -> Program {
    let result = propose(source).expect("bounded proposal");
    assert!(validate(source, &result));
    result
}
fn assignment_count(program: &Program) -> usize {
    program
        .instructions()
        .iter()
        .map(|item| item.assignments.len())
        .sum()
}
fn equivalent(source: &Program, candidate: &Program, inputs: &[u64], base: u64, memory: &[u8]) {
    for limit in [0, 1, 2, 4, 16, 100] {
        let original = source.run_with_memory(inputs, base, memory, limit).unwrap();
        let transformed = candidate
            .run_with_memory(inputs, base, memory, limit)
            .unwrap();
        assert_eq!(original.status, transformed.status);
        assert_eq!(original.state.memory, transformed.state.memory);
        assert_eq!(original.state.memory_base, transformed.state.memory_base);
        assert_eq!(original.state.trace, transformed.state.trace);
        assert_eq!(original.state.instruction, transformed.state.instruction);
        // Internal registers are deliberately excluded from the observation.
    }
}

#[test]
fn removes_overwritten_and_transitively_dead_writes_but_preserves_live_out() {
    let source = program(
        5,
        vec![
            instruction(
                0,
                vec![
                    write(0, c(1)),
                    write(1, r(0)),
                    write(0, c(9)),
                    write(2, r(1)),
                    write(3, c(4)),
                ],
                Control::Next,
            ),
            instruction(
                1,
                vec![write(4, op(BinaryOp::Add, r(0), r(3)))],
                Control::Return(r(4)),
            ),
        ],
    );
    let result = candidate(&source);
    assert_eq!(assignment_count(&result), 3);
    assert_eq!(
        result.instructions()[0].assignments,
        vec![write(0, c(9)), write(3, c(4))]
    );
    equivalent(&source, &result, &[0; 5], 0, &[]);
    assert!(validate(&source, &source));
}

#[test]
fn branch_merge_unions_both_successor_uses() {
    let source = program(
        4,
        vec![
            instruction(
                0,
                vec![write(1, c(11)), write(2, c(22)), write(3, c(99))],
                Control::Branch {
                    condition: r(0),
                    target: 3,
                },
            ),
            instruction(
                1,
                vec![write(1, op(BinaryOp::Add, r(1), c(1)))],
                Control::Jump(4),
            ),
            instruction(3, vec![write(1, r(2))], Control::Jump(4)),
            instruction(4, vec![], Control::Return(r(1))),
        ],
    );
    let result = candidate(&source);
    assert_eq!(
        result.instructions()[0].assignments,
        vec![write(1, c(11)), write(2, c(22))]
    );
    for condition in [0, 1, 2, u64::MAX] {
        equivalent(&source, &result, &[condition, 0, 0, 0], 0, &[]);
    }
}

#[test]
fn loop_carried_values_and_exit_uses_reach_a_fixed_point() {
    let source = program(
        4,
        vec![
            instruction(
                0,
                vec![write(1, c(0)), write(2, c(7)), write(3, c(9))],
                Control::Next,
            ),
            instruction(
                1,
                vec![
                    write(1, op(BinaryOp::Add, r(1), c(1))),
                    write(2, op(BinaryOp::Add, r(2), r(1))),
                ],
                Control::Branch {
                    condition: op(BinaryOp::Ult, r(1), r(0)),
                    target: 1,
                },
            ),
            instruction(2, vec![], Control::Return(r(2))),
        ],
    );
    let result = candidate(&source);
    assert_eq!(assignment_count(&result), 4);
    for iterations in [0, 1, 2, 5, 20] {
        equivalent(&source, &result, &[iterations, 0, 0, 0], 0, &[]);
    }
    let mut malicious = source.instructions().to_vec();
    malicious[1].assignments.remove(0);
    assert!(!validate(&source, &rebuild(&source, malicious)));
}

#[test]
fn preserves_unused_load_faults_and_all_lazy_load_arms() {
    for value in [
        Expr::load(r(0), Width::U16),
        Expr::select(c(1), c(8), Expr::load(r(0), Width::U16)),
        Expr::select(c(0), Expr::load(r(0), Width::U16), c(8)),
        Expr::select(c(1), Expr::load(r(0), Width::U16), c(8)),
    ] {
        let source = program(
            3,
            vec![instruction(
                0,
                vec![write(0, c(0x1000)), write(1, value), write(2, c(9))],
                Control::Return(c(7)),
            )],
        );
        let result = candidate(&source);
        assert_eq!(
            assignment_count(&result),
            2,
            "retain syntactic load and its register dependencies"
        );
        equivalent(&source, &result, &[0; 3], 0x1000, &[5, 6]);
        equivalent(&source, &result, &[0; 3], 0, &[]);
        let mut malicious = source.instructions().to_vec();
        malicious[0].assignments.remove(1);
        assert!(!validate(&source, &rebuild(&source, malicious)));
    }
}

#[test]
fn preserves_store_address_then_range_check_then_rhs_fault_order() {
    let source = program(
        4,
        vec![instruction(
            0,
            vec![
                write(0, c(0x1000)),
                store(r(0), Width::U8, c(0xaa)),
                write(1, c(0x1001)),
                write(2, c(0x2000)),
                write(3, c(0x3000)),
                store(
                    Expr::load(r(1), Width::U8),
                    Width::U32,
                    Expr::load(r(2), Width::U16),
                ),
                write(0, c(99)),
            ],
            Control::Return(c(0)),
        )],
    );
    let result = candidate(&source);
    assert_eq!(assignment_count(&result), 5);
    for memory in [vec![], vec![0, 0], vec![0; 8]] {
        equivalent(&source, &result, &[0; 4], 0x1000, &memory);
    }
    let report = result.run_with_memory(&[0; 4], 0x1000, &[0; 8], 1).unwrap();
    assert_eq!(report.state.memory[0], 0xaa);
    assert_eq!(
        report.status,
        RunStatus::Fault(MemoryFault {
            access: AccessKind::Write,
            address: 0,
            width: Width::U32
        })
    );

    // A valid store destination allows the RHS load to become the first fault.
    let source = program(
        2,
        vec![instruction(
            0,
            vec![
                write(0, c(0x1000)),
                write(1, c(0x2000)),
                store(r(0), Width::U8, Expr::load(r(1), Width::U64)),
            ],
            Control::Return(c(0)),
        )],
    );
    let result = candidate(&source);
    equivalent(&source, &result, &[0; 2], 0x1000, &[3; 8]);
    assert_eq!(
        result
            .run_with_memory(&[0; 2], 0x1000, &[3; 8], 1)
            .unwrap()
            .status,
        RunStatus::Fault(MemoryFault {
            access: AccessKind::Read,
            address: 0x2000,
            width: Width::U64
        })
    );
}

#[test]
fn preserves_aliasing_partial_writes_and_pre_fault_memory() {
    let source = program(
        3,
        vec![instruction(
            0,
            vec![
                write(0, c(0x1000)),
                write(1, c(0x1001)),
                write(2, c(123)),
                store(r(0), Width::U32, c(0x12345678)),
                store(r(1), Width::U16, c(0xabcd)),
                store(c(0x2000), Width::U8, c(1)),
            ],
            Control::Return(Expr::load(r(0), Width::U32)),
        )],
    );
    let result = candidate(&source);
    equivalent(&source, &result, &[0; 3], 0x1000, &[0; 8]);
    let report = result.run_with_memory(&[0; 3], 0x1000, &[0; 8], 1).unwrap();
    assert_eq!(&report.state.memory[..4], &[0x78, 0xcd, 0xab, 0x12]);
    assert!(matches!(report.status, RunStatus::Fault(_)));
}

#[test]
fn rejects_metadata_control_store_load_and_assignment_tampering() {
    let source = program(
        3,
        vec![
            instruction(
                0,
                vec![
                    write(0, c(0)),
                    write(1, Expr::load(r(0), Width::U8)),
                    store(r(0), Width::U8, r(1)),
                    write(2, c(9)),
                ],
                Control::Next,
            ),
            instruction(1, vec![], Control::Return(r(1))),
        ],
    );
    let originals = source.instructions();
    let mut edits = Vec::new();
    let mut changed = originals.to_vec();
    changed[0].assignments.remove(2);
    edits.push(changed);
    let mut changed = originals.to_vec();
    changed[0].assignments.remove(1);
    edits.push(changed);
    let mut changed = originals.to_vec();
    changed[0].assignments.remove(0);
    edits.push(changed);
    let mut changed = originals.to_vec();
    changed[0].assignments.swap(1, 2);
    edits.push(changed);
    let mut changed = originals.to_vec();
    changed[0].assignments[2].value = c(8);
    edits.push(changed);
    let mut changed = originals.to_vec();
    changed[0].assignments.push(write(2, c(9)));
    edits.push(changed);
    let mut changed = originals.to_vec();
    changed[1].control = Control::Return(c(0));
    edits.push(changed);
    let mut changed = originals.to_vec();
    changed[0].control = Control::Jump(1);
    edits.push(changed);
    let mut changed = originals.to_vec();
    changed[1].size = 2;
    edits.push(changed);
    let mut changed = originals.to_vec();
    changed[1].address = 2;
    changed[0].control = Control::Jump(2);
    edits.push(changed);
    for changed in edits {
        assert!(!validate(&source, &rebuild(&source, changed)));
    }
    let changed_entry = Program::new(1, 3, originals.to_vec()).unwrap();
    assert!(!validate(&source, &changed_entry));
    let changed_registers = Program::new(0, 4, originals.to_vec()).unwrap();
    assert!(!validate(&source, &changed_registers));
}

#[test]
fn identical_candidate_and_ambiguous_duplicate_assignments_are_safe() {
    let source = program(
        1,
        vec![instruction(
            0,
            vec![write(0, c(3)), write(0, c(3))],
            Control::Return(r(0)),
        )],
    );
    assert!(validate(&source, &source));
    // Greedy identity matching may conservatively decline removal of a duplicate.
    if let Some(result) = propose(&source) {
        assert!(validate(&source, &result));
        equivalent(&source, &result, &[9], 0, &[]);
    }
}

#[test]
fn resource_excess_declines_before_recursive_ir_operations() {
    let registers = program(4097, vec![instruction(0, vec![], Control::Return(c(0)))]);
    assert!(propose(&registers).is_none());
    assert!(!validate(&registers, &registers));
    let instructions = program(
        1,
        (0..16_385)
            .map(|address| {
                instruction(
                    address,
                    vec![],
                    if address == 16_384 {
                        Control::Return(c(0))
                    } else {
                        Control::Next
                    },
                )
            })
            .collect(),
    );
    assert!(propose(&instructions).is_none());
    assert!(!validate(&instructions, &instructions));
    let assignments = program(
        1,
        vec![instruction(
            0,
            vec![write(0, c(0)); 16_385],
            Control::Return(c(0)),
        )],
    );
    assert!(propose(&assignments).is_none());
    assert!(!validate(&assignments, &assignments));
    let mut deep = c(0);
    for _ in 0..129 {
        deep = op(BinaryOp::Add, deep, c(1));
    }
    let deep = program(
        1,
        vec![instruction(0, vec![write(0, deep)], Control::Return(c(0)))],
    );
    assert!(propose(&deep).is_none());
    assert!(!validate(&deep, &deep));
    let mut tree = c(1);
    for _ in 0..18 {
        tree = op(BinaryOp::Add, tree.clone(), tree);
    }
    let nodes = program(
        1,
        vec![instruction(0, vec![write(0, tree)], Control::Return(c(0)))],
    );
    assert!(propose(&nodes).is_none());
    assert!(!validate(&nodes, &nodes));

    let small = program(1, vec![instruction(0, vec![], Control::Return(c(0)))]);
    assert!(!validate(&small, &deep));
    assert!(!validate(&small, &nodes));
}

#[test]
fn accepts_high_register_numbers_and_declines_state_or_fixed_point_excess() {
    let source = program(
        4096,
        vec![instruction(
            0,
            vec![write(4095, c(7)), write(4094, c(9))],
            Control::Return(r(4095)),
        )],
    );
    let result = candidate(&source);
    assert_eq!(assignment_count(&result), 1);
    equivalent(&source, &result, &vec![0; 4096], 0, &[]);

    // Below the instruction cap, but above the explicit liveness state cap.
    let state = program(
        1,
        (0..11_000)
            .map(|address| {
                instruction(
                    address,
                    vec![],
                    if address == 10_999 {
                        Control::Return(c(0))
                    } else {
                        Control::Next
                    },
                )
            })
            .collect(),
    );
    assert!(propose(&state).is_none());
    assert!(!validate(&state, &state));

    // Reverse-address control flow propagates one instruction per sweep.
    // This finite program exceeds the visit cap rather than looping forever.
    let visits = Program::new(
        399,
        1,
        (0..400)
            .map(|address| {
                instruction(
                    address,
                    vec![],
                    if address == 0 {
                        Control::Return(r(0))
                    } else {
                        Control::Jump(address - 1)
                    },
                )
            })
            .collect(),
    )
    .unwrap();
    assert!(propose(&visits).is_none());
    assert!(!validate(&visits, &visits));

    // Extra assignments exhaust work before exhausting fixed-point visits.
    let work = Program::new(
        255,
        2,
        (0..256)
            .map(|address| {
                instruction(
                    address,
                    vec![write(1, c(1)); 8],
                    if address == 0 {
                        Control::Return(r(0))
                    } else {
                        Control::Jump(address - 1)
                    },
                )
            })
            .collect(),
    )
    .unwrap();
    assert!(propose(&work).is_none());
    assert!(!validate(&work, &work));
}

#[test]
fn preserves_faulting_control_even_when_both_branch_edges_match() {
    let source = program(
        3,
        vec![
            instruction(
                0,
                vec![write(0, c(0x1000)), write(1, c(99)), write(2, c(123))],
                Control::Branch {
                    condition: Expr::load(r(0), Width::U16),
                    target: 1,
                },
            ),
            instruction(1, vec![], Control::Return(c(7))),
        ],
    );
    let result = candidate(&source);
    assert_eq!(assignment_count(&result), 1);
    equivalent(&source, &result, &[0; 3], 0x1000, &[0, 1]);
    equivalent(&source, &result, &[0; 3], 0, &[]);
    let mut changed = source.instructions().to_vec();
    changed[0].assignments.remove(0);
    assert!(!validate(&source, &rebuild(&source, changed)));
}

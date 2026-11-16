use nirvana::ir::{
    Assignment, Control, ExecutionError, Expr, IrInstruction, Place, Program, Reg, Width,
};
use nirvana::structure::StructuredFunction;

fn instruction(address: u64, assignments: Vec<Assignment>, control: Control) -> IrInstruction {
    IrInstruction {
        address,
        size: 1,
        assignments,
        control,
    }
}

#[test]
fn unaligned_little_endian_loads_and_stores_preserve_neighboring_bytes() {
    let program = Program::new(
        0,
        1,
        vec![instruction(
            0,
            vec![
                Assignment {
                    destination: Place::Memory {
                        address: Expr::Const(0x1001),
                        width: Width::U32,
                    },
                    value: Expr::Const(0x123456789a),
                },
                Assignment {
                    destination: Reg(0).into(),
                    value: Expr::load(Expr::Const(0x1000), Width::U64),
                },
            ],
            Control::Return(Expr::Register(Reg(0))),
        )],
    )
    .unwrap();
    let initial = [0xaa; 8];
    let result = program
        .execute_with_memory(&[0], 0x1000, &initial, 1)
        .unwrap();
    assert_eq!(
        result.memory,
        [0xaa, 0x9a, 0x78, 0x56, 0x34, 0xaa, 0xaa, 0xaa]
    );
    assert_eq!(
        result.value,
        u64::from_le_bytes(result.memory.clone().try_into().unwrap())
    );
    assert_eq!(initial, [0xaa; 8]);
    assert_eq!(
        StructuredFunction::recover(&program)
            .unwrap()
            .execute_with_memory(&[0], 0x1000, &initial, 1)
            .unwrap(),
        result
    );
}

#[test]
fn out_of_bounds_and_wrapping_memory_addresses_are_errors() {
    for address in [0xfff, 0x1001, u64::MAX] {
        let program = Program::new(
            0,
            0,
            vec![instruction(
                0,
                vec![],
                Control::Return(Expr::load(Expr::Const(address), Width::U64)),
            )],
        )
        .unwrap();
        assert_eq!(
            program.execute_with_memory(&[], 0x1000, &[0; 8], 1),
            Err(ExecutionError::MemoryAccess {
                address,
                width: Width::U64
            })
        );
    }
}

#[test]
fn identical_branch_targets_do_not_erase_a_faulting_condition() {
    let program = Program::new(
        0,
        0,
        vec![
            instruction(
                0,
                vec![],
                Control::Branch {
                    condition: Expr::load(Expr::Const(1), Width::U8),
                    target: 1,
                },
            ),
            instruction(1, vec![], Control::Return(Expr::Const(42))),
        ],
    )
    .unwrap();
    let original = program.execute_with_memory(&[], 0x1000, &[0; 8], 2);
    assert!(matches!(original, Err(ExecutionError::MemoryAccess { .. })));
    assert_eq!(
        StructuredFunction::recover(&program)
            .unwrap()
            .execute_with_memory(&[], 0x1000, &[0; 8], 2),
        original
    );
    assert!(
        nirvana::emit::emit_c(&program)
            .code
            .contains("(void)(nirvana_load")
    );
}

#[test]
fn select_evaluates_only_the_chosen_memory_operand() {
    let program = Program::new(
        0,
        0,
        vec![instruction(
            0,
            vec![],
            Control::Return(Expr::select(
                Expr::Const(1),
                Expr::Const(42),
                Expr::load(Expr::Const(u64::MAX), Width::U64),
            )),
        )],
    )
    .unwrap();
    assert_eq!(program.execute(&[], 1).unwrap().value, 42);
}

#[test]
fn memory_address_registers_are_validated() {
    let result = Program::new(
        0,
        1,
        vec![instruction(
            0,
            vec![Assignment {
                destination: Place::Memory {
                    address: Expr::Register(Reg(1)),
                    width: Width::U8,
                },
                value: Expr::Const(0),
            }],
            Control::Return(Expr::Const(0)),
        )],
    );
    assert!(matches!(
        result,
        Err(nirvana::ir::ProgramError::InvalidRegister { .. })
    ));
}

#[test]
fn a_mapped_access_cannot_wrap_the_u64_address_space() {
    let program = Program::new(
        0,
        0,
        vec![instruction(
            0,
            vec![],
            Control::Return(Expr::load(Expr::Const(u64::MAX - 3), Width::U64)),
        )],
    )
    .unwrap();
    assert!(matches!(
        program.execute_with_memory(&[], u64::MAX - 3, &[0; 8], 1),
        Err(ExecutionError::MemoryAccess { .. })
    ));
}

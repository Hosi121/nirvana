use nirvana::hir::ViewPath;
use nirvana::ir::{
    AccessKind, Assignment, BinaryOp, Control, Expr, IrInstruction, MemoryFault, Program, Reg,
    RunStatus, Width,
};

fn object(name: &str, base: Expr) -> ViewPath {
    ViewPath::Object {
        name: name.into(),
        base,
    }
}

fn field(base: ViewPath, offset: u64) -> ViewPath {
    ViewPath::Field {
        base: Box::new(base),
        offset,
    }
}

fn index(base: ViewPath, index: Expr, stride: u64) -> ViewPath {
    ViewPath::Index {
        base: Box::new(base),
        index,
        stride,
    }
}

fn program(register_count: usize, assignments: Vec<Assignment>, result: Expr) -> Program {
    Program::new(
        0,
        register_count,
        vec![IrInstruction {
            address: 0,
            size: 1,
            assignments,
            control: Control::Return(result),
        }],
    )
    .unwrap()
}

#[test]
fn explicit_paths_lower_to_the_existing_ir_without_simplification() {
    let base = Expr::Register(Reg(0));
    let root = object("record", base.clone());
    let path = index(field(root.clone(), 3), Expr::Register(Reg(1)), 8);
    let address = Expr::binary(
        BinaryOp::Add,
        Expr::binary(BinaryOp::Add, base, Expr::Const(3)),
        Expr::binary(BinaryOp::Mul, Expr::Register(Reg(1)), Expr::Const(8)),
    );
    assert_eq!(path.address(), address);
    assert_eq!(
        path.load(Width::U16),
        Expr::load(address.clone(), Width::U16)
    );
    assert_eq!(
        path.store(Width::U32, Expr::Const(42)),
        Assignment {
            destination: nirvana::ir::Place::Memory {
                address,
                width: Width::U32,
            },
            value: Expr::Const(42),
        }
    );
    assert_ne!(root, object("other name", Expr::Register(Reg(0))));
    assert_eq!(
        root.address(),
        object("other name", Expr::Register(Reg(0))).address()
    );
}

#[test]
fn field_and_index_views_alias_at_every_width_and_preserve_neighboring_bytes() {
    for width in [Width::U8, Width::U16, Width::U32, Width::U64] {
        let destination = field(object("record", Expr::Const(0x1000)), 1);
        let alias = index(
            object("array", Expr::Register(Reg(0))),
            Expr::Register(Reg(1)),
            1,
        );
        let value = 0x8877_6655_4433_2211_u64;
        let program = program(
            2,
            vec![destination.store(width, Expr::Const(value))],
            alias.load(width),
        );
        let initial = [0xaa; 12];
        let execution = program
            .execute_with_memory(&[0x1000, 1], 0x1000, &initial, 1)
            .unwrap();
        let mut expected = initial;
        expected[1..1 + width.bytes()].copy_from_slice(&value.to_le_bytes()[..width.bytes()]);
        assert_eq!(execution.memory, expected, "{width:?}");
        assert_eq!(execution.value, value & width.mask(), "{width:?}");
        assert_eq!(initial, [0xaa; 12]);
    }
}

#[test]
fn overlapping_views_share_bytes_without_an_ownership_boundary() {
    let root = object("record", Expr::Const(0x1000));
    let low_word = field(root.clone(), 0);
    let middle_byte = index(root, Expr::Const(1), 1);
    let program = program(
        0,
        vec![
            low_word.store(Width::U32, Expr::Const(0x4433_2211)),
            middle_byte.store(Width::U8, Expr::Const(0xff)),
        ],
        low_word.load(Width::U32),
    );
    let execution = program
        .execute_with_memory(&[], 0x1000, &[0; 4], 1)
        .unwrap();
    assert_eq!(execution.memory, [0x11, 0xff, 0x33, 0x44]);
    assert_eq!(execution.value, 0x4433_ff11);
}

#[test]
fn field_and_index_address_arithmetic_wraps_modulo_u64() {
    let paths = [
        field(object("field", Expr::Const(u64::MAX)), 2),
        index(object("sum", Expr::Const(u64::MAX)), Expr::Const(1), 2),
        index(object("product", Expr::Const(3)), Expr::Const(u64::MAX), 2),
    ];
    for path in paths {
        let program = program(
            0,
            vec![path.store(Width::U8, Expr::Const(0x5a))],
            path.load(Width::U8),
        );
        let execution = program.execute_with_memory(&[], 1, &[0], 1).unwrap();
        assert_eq!(execution.value, 0x5a);
        assert_eq!(execution.memory, [0x5a]);
    }
}

#[test]
fn wrapping_address_arithmetic_does_not_allow_an_access_to_wrap() {
    let path = field(object("end", Expr::Const(u64::MAX - 4)), 1);
    let program = program(0, vec![], path.load(Width::U64));
    let report = program
        .run_with_memory(&[], u64::MAX - 3, &[0; 8], 1)
        .unwrap();
    assert_eq!(
        report.status,
        RunStatus::Fault(MemoryFault {
            access: AccessKind::Read,
            address: u64::MAX - 3,
            width: Width::U64,
        })
    );
}

#[test]
fn faulting_store_keeps_prior_effects_and_checks_destination_before_value() {
    let root = object("record", Expr::Const(0x1000));
    let invalid = field(root.clone(), 3);
    let program = program(
        1,
        vec![
            root.store(Width::U16, Expr::Const(0x2211)),
            Assignment {
                destination: Reg(0).into(),
                value: Expr::Const(7),
            },
            invalid.store(
                Width::U16,
                object("invalid value", Expr::Const(0x2000)).load(Width::U64),
            ),
            root.store(Width::U8, Expr::Const(0xff)),
        ],
        Expr::Const(0),
    );
    let report = program
        .run_with_memory(&[0], 0x1000, &[0xaa; 4], 1)
        .unwrap();
    assert_eq!(
        report.status,
        RunStatus::Fault(MemoryFault {
            access: AccessKind::Write,
            address: 0x1003,
            width: Width::U16,
        })
    );
    assert_eq!(report.state.memory, [0x11, 0x22, 0xaa, 0xaa]);
    assert_eq!(report.state.registers, [7]);
    assert_eq!(report.state.trace, [0]);
    assert_eq!(report.state.instruction, Some(0));
}

#[test]
fn valid_store_does_not_change_bytes_when_its_value_faults() {
    let root = object("record", Expr::Const(0x1000));
    let program = program(
        0,
        vec![root.store(
            Width::U16,
            object("invalid value", Expr::Const(0x2000)).load(Width::U8),
        )],
        Expr::Const(0),
    );
    let report = program.run_with_memory(&[], 0x1000, &[0xaa; 4], 1).unwrap();
    assert_eq!(
        report.status,
        RunStatus::Fault(MemoryFault {
            access: AccessKind::Read,
            address: 0x2000,
            width: Width::U8,
        })
    );
    assert_eq!(report.state.memory, [0xaa; 4]);
}

#[test]
fn faulting_base_is_evaluated_before_a_faulting_index() {
    let path = index(
        object("indirect", Expr::load(Expr::Const(0x2000), Width::U64)),
        Expr::load(Expr::Const(0x3000), Width::U32),
        8,
    );
    let program = program(0, vec![], path.load(Width::U16));
    let report = program.run_with_memory(&[], 0x1000, &[0; 8], 1).unwrap();
    assert_eq!(
        report.status,
        RunStatus::Fault(MemoryFault {
            access: AccessKind::Read,
            address: 0x2000,
            width: Width::U64,
        })
    );
}

#[test]
fn zero_stride_does_not_erase_a_faulting_index() {
    let path = index(
        object("array", Expr::Const(0x1000)),
        Expr::load(Expr::Const(0x2000), Width::U32),
        0,
    );
    let program = program(0, vec![], path.load(Width::U8));
    let report = program.run_with_memory(&[], 0x1000, &[42], 1).unwrap();
    assert_eq!(
        report.status,
        RunStatus::Fault(MemoryFault {
            access: AccessKind::Read,
            address: 0x2000,
            width: Width::U32,
        })
    );
}

#[test]
fn reused_views_observe_sequential_register_and_memory_changes() {
    let pointer = object("pointer", Expr::Const(0x1000));
    let indirect = index(
        object("indirect", pointer.load(Width::U64)),
        Expr::Register(Reg(0)),
        1,
    );
    let program = program(
        1,
        vec![
            pointer.store(Width::U64, Expr::Const(0x1008)),
            indirect.store(Width::U8, Expr::Const(0x11)),
            pointer.store(Width::U64, Expr::Const(0x1009)),
            Assignment {
                destination: Reg(0).into(),
                value: Expr::Const(1),
            },
            indirect.store(Width::U8, Expr::Const(0x22)),
        ],
        indirect.load(Width::U8),
    );
    let execution = program
        .execute_with_memory(&[0], 0x1000, &[0; 12], 1)
        .unwrap();
    assert_eq!(&execution.memory[..8], &0x1009_u64.to_le_bytes());
    assert_eq!(&execution.memory[8..], &[0x11, 0, 0x22, 0]);
    assert_eq!(execution.value, 0x22);
}

#[test]
fn select_keeps_faulting_views_lazy_in_values_and_addresses() {
    let valid = object("valid", Expr::Const(0x1000));
    let invalid = object("invalid", Expr::Const(0x2000));
    let chosen_address = object(
        "selected address",
        Expr::select(Expr::Register(Reg(0)), valid.address(), invalid.address()),
    );
    let program = program(
        1,
        vec![chosen_address.store(
            Width::U8,
            Expr::select(
                Expr::Register(Reg(0)),
                Expr::Const(42),
                invalid.load(Width::U64),
            ),
        )],
        Expr::select(
            Expr::Register(Reg(0)),
            valid.load(Width::U8),
            invalid.load(Width::U64),
        ),
    );
    let execution = program.execute_with_memory(&[1], 0x1000, &[0], 1).unwrap();
    assert_eq!(execution.value, 42);
    assert_eq!(execution.memory, [42]);
    let report = program.run_with_memory(&[0], 0x1000, &[0], 1).unwrap();
    assert_eq!(
        report.status,
        RunStatus::Fault(MemoryFault {
            access: AccessKind::Write,
            address: 0x2000,
            width: Width::U8,
        })
    );
    assert_eq!(report.state.memory, [0]);
}

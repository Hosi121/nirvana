//! The signed analysis is bound to the selected final display and C locals.
use nirvana::dataflow::signed_width;
use nirvana::ir::{
    Assignment, BinaryOp as B, Control, Expr, IrInstruction, Place, Program, Reg, UnaryOp, Width,
};
use nirvana::readable::{
    ReadableC, ReadableOptions, SignedStorageProvenance, emit_middle_c_with_options,
    emit_middle_c_with_storage_provenance, emit_readable_c_with_options,
    emit_readable_c_with_storage_provenance,
};

fn r(n: usize) -> Expr {
    Expr::Register(Reg(n))
}
fn c(n: u64) -> Expr {
    Expr::Const(n)
}
fn b(op: B, a: Expr, z: Expr) -> Expr {
    Expr::binary(op, a, z)
}
fn signed(value: Expr) -> Expr {
    Expr::unary(UnaryOp::SignExtend(Width::U32), value)
}
fn set(n: usize, value: Expr) -> Assignment {
    Assignment {
        destination: Reg(n).into(),
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

fn sources() -> Vec<Program> {
    vec![
        Program::new(
            0,
            3,
            vec![
                instruction(
                    0,
                    vec![set(1, signed(r(0)))],
                    Control::Branch {
                        condition: b(B::Eq, b(B::And, r(1), c(1)), c(0)),
                        target: 2,
                    },
                ),
                instruction(
                    1,
                    vec![],
                    Control::Return(b(B::Add, r(1), b(B::SDiv, r(1), c(31)))),
                ),
                instruction(
                    2,
                    vec![],
                    Control::Return(b(B::Xor, r(1), b(B::AShr, r(1), c(1)))),
                ),
            ],
        )
        .unwrap(),
        Program::new(
            0,
            8,
            vec![instruction(
                0,
                vec![
                    set(1, signed(Expr::load(r(7), Width::U32))),
                    Assignment {
                        destination: Place::Memory {
                            address: b(B::Add, r(7), c(8)),
                            width: Width::U64,
                        },
                        value: r(1),
                    },
                ],
                Control::Return(b(B::Add, r(1), b(B::AShr, r(1), c(1)))),
            )],
        )
        .unwrap(),
        Program::new(
            0,
            3,
            vec![
                instruction(0, vec![set(1, signed(r(0))), set(2, c(0))], Control::Next),
                instruction(
                    1,
                    vec![
                        set(1, signed(b(B::Add, r(1), c(1)))),
                        set(2, b(B::Add, r(2), c(1))),
                    ],
                    Control::Branch {
                        condition: b(B::Ult, r(2), c(3)),
                        target: 1,
                    },
                ),
                instruction(
                    2,
                    vec![],
                    Control::Return(b(B::Xor, r(1), b(B::AShr, r(1), c(1)))),
                ),
            ],
        )
        .unwrap(),
    ]
}

fn check(ordinary: &ReadableC, captured: &ReadableC) {
    assert_eq!(ordinary.code, captured.code);
    assert_eq!(ordinary.parameters, captured.parameters);
    assert_eq!(ordinary.locals, captured.locals);
    assert!(matches!(
        ordinary.signed_storage_provenance,
        SignedStorageProvenance::NotCaptured
    ));
    let SignedStorageProvenance::Captured(snapshot) = &captured.signed_storage_provenance else {
        panic!("small selected signed sources must have captured checked facts");
    };
    signed_width::validate(&snapshot.source, &snapshot.widths).unwrap();
    assert!(
        captured
            .locals
            .iter()
            .any(|local| local.signed_width.is_some()),
        "exercise actual signed local selection"
    );
    for local in &captured.locals {
        for &member in &local.registers {
            assert!(member.0 < snapshot.source.register_count());
            if let Some(width) = local.signed_width {
                assert!(snapshot.widths.width(member) <= width);
            }
        }
    }
}

#[test]
fn selected_signed_capture_keeps_readable_and_middle_c_identical() {
    let options = ReadableOptions {
        coalesce_locals: true,
        compact_memory: true,
        ..ReadableOptions::default()
    };
    for source in sources() {
        check(
            &emit_readable_c_with_options(&source, options).unwrap(),
            &emit_readable_c_with_storage_provenance(&source, options).unwrap(),
        );
        let middle = nirvana::middle_ir::Function::from_low(&source).unwrap();
        check(
            &emit_middle_c_with_options(&middle, options).unwrap(),
            &emit_middle_c_with_storage_provenance(&middle, options).unwrap(),
        );
    }
}

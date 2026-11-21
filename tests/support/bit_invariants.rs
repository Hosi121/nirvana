//! Shared effectful memory invariants for analysis and generated-C checks.
use super::ir::{c, r};
use nirvana::ir::{
    Assignment, BinaryOp as B, Control, Expr, IrInstruction, Place, Program, Reg, Width,
};
fn b(op: B, a: Expr, z: Expr) -> Expr {
    Expr::binary(op, a, z)
}
fn set(n: usize, value: Expr) -> Assignment {
    Assignment {
        destination: Reg(n).into(),
        value,
    }
}
fn address(offset: u64) -> Expr {
    b(B::Add, r(7), c(offset))
}
fn store(offset: u64, width: Width, value: Expr) -> Assignment {
    Assignment {
        destination: Place::Memory {
            address: address(offset),
            width,
        },
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
fn tag(value: Expr) -> Expr {
    b(B::Or, b(B::And, value, c(15)), c(128))
}
fn bit(value: Expr) -> Expr {
    b(B::And, value, c(128))
}
fn finish() -> IrInstruction {
    ins(
        4,
        vec![
            set(2, Expr::load(address(8), Width::U16)),
            store(
                16,
                Width::U64,
                Expr::select(
                    Expr::load(address(24), Width::U64),
                    bit(r(2)),
                    Expr::load(address(40), Width::U64),
                ),
            ),
        ],
        Control::Return(bit(r(2))),
    )
}
pub fn memory_programs() -> [Program; 5] {
    let straight = vec![
        ins(
            0,
            vec![
                set(0, Expr::load(r(7), Width::U64)),
                set(1, tag(r(0))),
                store(8, Width::U16, r(1)),
            ],
            Control::Jump(1),
        ),
        ins(1, vec![set(1, c(0))], Control::Jump(4)),
        finish(),
    ];
    let diamond = vec![
        ins(
            0,
            vec![set(0, Expr::load(r(7), Width::U64))],
            Control::Branch {
                condition: r(0),
                target: 2,
            },
        ),
        ins(1, vec![store(8, Width::U16, c(129))], Control::Jump(4)),
        ins(2, vec![store(8, Width::U16, c(131))], Control::Jump(4)),
        finish(),
    ];
    let looped = vec![
        ins(
            0,
            vec![
                set(0, Expr::load(r(7), Width::U64)),
                set(1, tag(r(0))),
                store(8, Width::U16, r(1)),
                set(3, b(B::And, r(0), c(3))),
            ],
            Control::Jump(1),
        ),
        ins(
            1,
            vec![set(1, Expr::load(address(8), Width::U16))],
            Control::Branch {
                condition: r(3),
                target: 3,
            },
        ),
        ins(2, vec![], Control::Jump(4)),
        ins(
            3,
            vec![
                store(8, Width::U16, tag(b(B::Add, r(1), c(1)))),
                set(3, b(B::Sub, r(3), c(1))),
            ],
            Control::Jump(1),
        ),
        finish(),
    ];
    let wide_finish = || {
        ins(
            4,
            vec![
                set(2, Expr::load(address(8), Width::U16)),
                store(
                    16,
                    Width::U64,
                    Expr::select(
                        Expr::load(address(24), Width::U64),
                        r(2),
                        Expr::load(address(40), Width::U64),
                    ),
                ),
            ],
            Control::Return(bit(r(2))),
        )
    };
    let partial = vec![
        ins(
            0,
            vec![
                set(0, Expr::load(r(7), Width::U64)),
                set(1, tag(r(0))),
                store(8, Width::U8, r(1)),
            ],
            Control::Jump(1),
        ),
        ins(1, vec![set(1, c(0))], Control::Jump(4)),
        wide_finish(),
    ];
    let alias = vec![
        ins(
            0,
            vec![
                set(0, Expr::load(r(7), Width::U64)),
                set(1, tag(r(0))),
                set(
                    6,
                    b(B::Add, address(8), b(B::Sub, b(B::And, r(0), c(3)), c(1))),
                ),
                store(8, Width::U16, r(1)),
                Assignment {
                    destination: Place::Memory {
                        address: r(6),
                        width: Width::U8,
                    },
                    value: c(128),
                },
            ],
            Control::Jump(4),
        ),
        wide_finish(),
    ];
    [straight, diamond, looped, partial, alias]
        .map(|instructions| Program::new(0, 8, instructions).unwrap())
}

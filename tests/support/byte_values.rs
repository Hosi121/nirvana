//! Saved-word programs shared by symbolic value recovery and C observers.
use super::ir::{c, r};
use nirvana::ir::{
    Assignment, BinaryOp as B, Control, Expr, IrInstruction, Place, Program, Reg, UnaryOp as U,
    Width,
};
fn b(op: B, a: Expr, z: Expr) -> Expr {
    Expr::binary(op, a, z)
}
fn at(n: u64) -> Expr {
    b(B::Add, r(7), c(n))
}
fn load(n: u64, w: Width) -> Expr {
    Expr::load(at(n), w)
}
fn set(n: usize, value: Expr) -> Assignment {
    Assignment {
        destination: Reg(n).into(),
        value,
    }
}
fn store(n: u64, width: Width, value: Expr) -> Assignment {
    Assignment {
        destination: Place::Memory {
            address: at(n),
            width,
        },
        value,
    }
}
fn slice(n: u8, w: Width) -> Expr {
    Expr::unary(U::Extract { start: n, width: w }, r(0))
}
fn ins(address: u64, assignments: Vec<Assignment>, control: Control) -> IrInstruction {
    IrInstruction {
        address,
        size: 1,
        assignments,
        control,
    }
}
fn program(rows: Vec<IrInstruction>) -> Program {
    Program::new(0, 8, rows).unwrap()
}
pub fn programs() -> Vec<Program> {
    let shifted = program(vec![
        ins(0, vec![set(0, load(0, Width::U64))], Control::Next),
        ins(
            1,
            vec![store(32, Width::U64, r(0)), set(0, c(0))],
            Control::Next,
        ),
        ins(
            2,
            vec![set(2, load(35, Width::U16)), set(3, load(38, Width::U8))],
            Control::Return(b(B::Add, r(2), r(3))),
        ),
    ]);
    let split = program(vec![
        ins(0, vec![set(0, load(0, Width::U64))], Control::Next),
        ins(
            1,
            vec![
                store(32, Width::U16, slice(0, Width::U16)),
                store(34, Width::U16, slice(16, Width::U16)),
                set(0, c(0)),
            ],
            Control::Next,
        ),
        ins(2, vec![set(2, load(32, Width::U32))], Control::Return(r(2))),
    ]);
    let inserted = program(vec![
        ins(
            0,
            vec![set(0, load(0, Width::U64)), set(6, load(8, Width::U64))],
            Control::Next,
        ),
        ins(
            1,
            vec![
                store(
                    32,
                    Width::U16,
                    b(
                        B::Insert {
                            start: 8,
                            width: Width::U8,
                        },
                        r(0),
                        r(6),
                    ),
                ),
                set(0, c(0)),
                set(6, c(0)),
            ],
            Control::Next,
        ),
        ins(
            2,
            vec![set(2, load(32, Width::U8)), set(3, load(33, Width::U8))],
            Control::Return(b(B::Or, r(2), b(B::Shl, r(3), c(8)))),
        ),
    ]);
    let may = program(vec![
        ins(0, vec![set(0, load(0, Width::U64))], Control::Next),
        ins(
            1,
            vec![
                store(32, Width::U8, r(0)),
                Assignment {
                    destination: Place::Memory {
                        address: b(
                            B::Add,
                            at(32),
                            b(B::Mul, b(B::And, load(8, Width::U64), c(3)), c(8)),
                        ),
                        width: Width::U8,
                    },
                    value: r(0),
                },
                set(0, c(0)),
            ],
            Control::Next,
        ),
        ins(2, vec![set(2, load(32, Width::U8))], Control::Return(r(2))),
    ]);
    let phi = program(vec![
        ins(
            0,
            vec![set(0, load(0, Width::U64)), set(1, load(24, Width::U64))],
            Control::Branch {
                condition: r(1),
                target: 2,
            },
        ),
        ins(
            1,
            vec![store(32, Width::U32, r(0)), set(0, c(0))],
            Control::Jump(3),
        ),
        ins(
            2,
            vec![store(32, Width::U64, r(0)), set(0, c(0))],
            Control::Jump(3),
        ),
        ins(3, vec![set(2, load(33, Width::U16))], Control::Return(r(2))),
    ]);
    let looped = program(vec![
        ins(
            0,
            vec![
                set(0, load(0, Width::U64)),
                set(1, b(B::And, load(8, Width::U64), c(3))),
                store(32, Width::U64, r(0)),
            ],
            Control::Jump(1),
        ),
        ins(
            1,
            vec![set(2, load(35, Width::U16))],
            Control::Branch {
                condition: r(1),
                target: 3,
            },
        ),
        ins(2, vec![], Control::Return(r(2))),
        ins(
            3,
            vec![store(32, Width::U64, r(0)), set(1, b(B::Sub, r(1), c(1)))],
            Control::Jump(1),
        ),
    ]);
    vec![shifted, split, inserted, may, phi, looped]
}

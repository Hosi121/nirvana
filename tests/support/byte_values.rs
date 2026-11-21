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
    let transformed = program(vec![
        ins(0, vec![set(0, load(0, Width::U64))], Control::Next),
        ins(
            1,
            vec![
                set(0, b(B::Xor, r(0), c(1))),
                store(32, Width::U64, r(0)),
                set(0, c(0)),
            ],
            Control::Next,
        ),
        ins(
            2,
            vec![set(2, load(32, Width::U8)), set(3, load(33, Width::U8))],
            Control::Return(b(B::Add, r(2), r(3))),
        ),
    ]);
    let mut result = vec![shifted, split, inserted, may, phi, looped, transformed];
    result.extend(producer_programs());
    result.extend(after_loop_programs());
    result.extend(stored_expression_programs());
    result.extend(invariant_loop_programs());
    result
}

/// Disjoint stores whose contiguous source bits cross SSA producer definitions.
pub fn producer_programs() -> Vec<Program> {
    [
        b(B::Shr, r(0), c(16)),
        b(B::AShr, r(0), c(16)),
        b(B::Shr, b(B::And, r(0), c(0xffff_ffff)), c(16)),
        Expr::unary(
            U::Extract {
                start: 16,
                width: Width::U16,
            },
            r(0),
        ),
        b(B::Shr, b(B::Shr, r(0), c(65)), c(15)),
    ]
    .into_iter()
    .map(|producer| {
        program(vec![
            ins(0, vec![set(6, producer)], Control::Next),
            ins(
                1,
                vec![
                    store(0, Width::U16, r(0)),
                    store(2, Width::U16, r(6)),
                    set(0, c(0)),
                    set(6, c(0)),
                ],
                Control::Next,
            ),
            ins(2, vec![set(2, load(0, Width::U32))], Control::Return(r(2))),
        ])
    })
    .collect()
}

/// Values created in the single-visit exit of a loop, rather than its prefix.
pub fn after_loop_programs() -> Vec<Program> {
    [b(B::Add, r(0), r(1)), load(0, Width::U64)]
        .into_iter()
        .map(|value| {
            program(vec![
                ins(0, vec![set(3, b(B::And, r(1), c(3)))], Control::Jump(1)),
                ins(
                    1,
                    vec![],
                    Control::Branch {
                        condition: r(3),
                        target: 3,
                    },
                ),
                ins(
                    2,
                    vec![
                        set(6, value),
                        store(16, Width::U64, r(6)),
                        set(6, c(0)),
                        set(2, load(17, Width::U16)),
                    ],
                    Control::Return(r(2)),
                ),
                ins(3, vec![set(3, b(B::Sub, r(3), c(1)))], Control::Jump(1)),
            ])
        })
        .collect()
}

/// A single saved pure expression supplies several later byte views.
pub fn stored_expression_programs() -> Vec<Program> {
    [
        b(B::Add, r(0), r(1)),
        b(B::Mul, r(0), r(1)),
        b(B::Xor, r(0), r(1)),
        b(
            B::Insert {
                start: 8,
                width: Width::U8,
            },
            r(0),
            r(6),
        ),
        b(B::SDiv, r(0), r(1)),
        Expr::select(r(6), b(B::Add, r(0), r(1)), b(B::Sub, r(0), r(1))),
    ]
    .into_iter()
    .map(|value| {
        program(vec![
            ins(
                0,
                vec![
                    set(0, load(0, Width::U64)),
                    set(1, load(8, Width::U64)),
                    set(6, load(16, Width::U64)),
                ],
                Control::Next,
            ),
            ins(
                1,
                vec![
                    store(32, Width::U64, value),
                    set(0, c(0)),
                    set(1, c(0)),
                    set(6, c(0)),
                ],
                Control::Next,
            ),
            ins(
                2,
                vec![set(2, load(33, Width::U16)), set(3, load(37, Width::U8))],
                Control::Return(b(B::Add, r(2), r(3))),
            ),
        ])
    })
    .collect()
}

/// Repeated definitions depend only on values read before the loop.
pub fn invariant_loop_programs() -> Vec<Program> {
    [false, true]
        .into_iter()
        .map(|register| {
            let value = b(B::Add, r(0), r(1));
            let mut body = if register {
                vec![set(6, value), store(32, Width::U64, r(6))]
            } else {
                vec![store(32, Width::U64, value)]
            };
            body.extend([set(2, load(33, Width::U16)), set(3, b(B::Sub, r(3), c(1)))]);
            program(vec![
                ins(
                    0,
                    vec![
                        set(0, load(0, Width::U64)),
                        set(1, load(8, Width::U64)),
                        set(3, b(B::Add, b(B::And, load(8, Width::U64), c(3)), c(1))),
                    ],
                    Control::Next,
                ),
                ins(
                    1,
                    body,
                    Control::Branch {
                        condition: r(3),
                        target: 1,
                    },
                ),
                ins(2, vec![], Control::Return(r(2))),
            ])
        })
        .collect()
}

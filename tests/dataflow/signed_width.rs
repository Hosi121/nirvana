use crate::support::ir::{c, r};
use nirvana::{
    dataflow::signed_width::SignedWidths,
    ir::{
        Assignment, BinaryOp as B, Control, Expr, IrInstruction, Program, Reg, UnaryOp as U, Width,
    },
};
fn set(n: usize, value: Expr) -> Assignment {
    Assignment {
        destination: Reg(n).into(),
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
fn se(e: Expr, w: Width) -> Expr {
    Expr::unary(U::SignExtend(w), e)
}
fn b(op: B, a: Expr, z: Expr) -> Expr {
    Expr::binary(op, a, z)
}

#[test]
fn phi_loops_close_over_signed_words_and_keep_the_virtual_entry_unknown() {
    let p = Program::new(
        0,
        3,
        vec![
            ins(
                0,
                vec![set(1, se(r(0), Width::U8)), set(2, c(0))],
                Control::Next,
            ),
            ins(
                1,
                vec![
                    set(1, b(B::AShr, r(1), c(1))),
                    set(2, b(B::Add, r(2), c(1))),
                ],
                Control::Branch {
                    condition: b(B::Ult, r(2), c(4)),
                    target: 1,
                },
            ),
            ins(2, vec![], Control::Return(r(1))),
        ],
    )
    .unwrap();
    assert_eq!(SignedWidths::analyze(&p).width(Reg(1)), Width::U8);
    let entry = Program::new(
        0,
        3,
        vec![
            ins(
                0,
                vec![],
                Control::Branch {
                    condition: r(2),
                    target: 2,
                },
            ),
            ins(1, vec![set(1, se(r(0), Width::U8))], Control::Jump(0)),
            ins(2, vec![], Control::Return(r(1))),
        ],
    )
    .unwrap();
    assert_eq!(SignedWidths::analyze(&entry).width(Reg(1)), Width::U64);
}

#[test]
fn copies_keep_their_own_ssa_value_after_an_unsigned_overwrite() {
    let p = Program::new(
        0,
        4,
        vec![ins(
            0,
            vec![
                set(1, se(r(0), Width::U32)),
                set(2, r(1)),
                set(
                    1,
                    Expr::unary(
                        U::Extract {
                            start: 0,
                            width: Width::U32,
                        },
                        r(0),
                    ),
                ),
            ],
            Control::Return(b(B::Xor, r(1), r(2))),
        )],
    )
    .unwrap();
    let facts = SignedWidths::analyze(&p);
    assert_eq!(facts.width(Reg(1)), Width::U64);
    assert_eq!(facts.width(Reg(2)), Width::U32);
    let too_many = Program::new(
        0,
        nirvana::ssa::MAX_REGISTERS + 1,
        vec![ins(
            0,
            vec![set(1, se(r(0), Width::U8))],
            Control::Return(r(1)),
        )],
    )
    .unwrap();
    assert_eq!(SignedWidths::analyze(&too_many).width(Reg(1)), Width::U64);
    assert_eq!(facts.width(Reg(usize::MAX)), Width::U64);
}

#[test]
fn reported_bounds_match_independent_signed_interpretations_across_operations() {
    let mut values = vec![
        0,
        1,
        127,
        128,
        255,
        32767,
        32768,
        65535,
        1 << 31,
        1 << 63,
        u64::MAX,
    ];
    let mut seed = 0x8981_33f2_9571_ff77u64;
    for _ in 0..128 {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        values.push(seed);
    }
    for width in [Width::U8, Width::U16, Width::U32] {
        let left = se(r(0), width);
        let mut expressions = vec![
            left.clone(),
            b(B::AShr, left.clone(), r(1)),
            Expr::select(r(1), left.clone(), se(r(1), Width::U16)),
        ];
        for op in [B::And, B::Or, B::Xor] {
            expressions.push(b(op, left.clone(), se(r(1), Width::U16)));
        }
        for d in [3i64, -31, 0, 1, -1] {
            for op in [B::SDiv, B::SRem] {
                expressions.push(b(op, left.clone(), c(d as u64)));
            }
        }
        for expression in expressions {
            let p = Program::new(
                0,
                3,
                vec![ins(0, vec![set(2, expression)], Control::Return(r(2)))],
            )
            .unwrap();
            let bound = SignedWidths::analyze(&p).width(Reg(2));
            for &x in &values {
                for y in [0, 1, 63, 64, 128, u64::MAX] {
                    let actual = p.execute(&[x, y, 0], 1).unwrap().value;
                    let extended = match bound {
                        Width::U8 => actual as i8 as i64 as u64,
                        Width::U16 => actual as i16 as i64 as u64,
                        Width::U32 => actual as i32 as i64 as u64,
                        Width::U64 => actual,
                    };
                    assert_eq!(actual, extended, "{width:?}/{bound:?}/{x}/{y}");
                }
            }
        }
    }
}

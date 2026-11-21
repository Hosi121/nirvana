//! Insert memory cases shared by checked execution and block proofs.
use super::ir::{c, r};
use nirvana::ir::{
    Assignment, BinaryOp as B, Control, Expr, IrInstruction, Place, Program, Reg, Width,
};
fn b(op: B, a: Expr, z: Expr) -> Expr {
    Expr::binary(op, a, z)
}
pub fn memory_program(op: B) -> Program {
    let load = |offset| Expr::load(b(B::Add, r(7), c(offset)), Width::U64);
    Program::new(
        0,
        32,
        vec![
            IrInstruction {
                address: 0,
                size: 1,
                assignments: vec![Assignment {
                    destination: Place::Memory {
                        address: c(0x103f),
                        width: Width::U8,
                    },
                    value: c(0xa1),
                }],
                control: Control::Next,
            },
            IrInstruction {
                address: 1,
                size: 1,
                assignments: vec![Assignment {
                    destination: Reg(0).into(),
                    value: b(op, load(0), Expr::select(load(24), load(8), load(16))),
                }],
                control: Control::Next,
            },
            IrInstruction {
                address: 2,
                size: 1,
                assignments: vec![Assignment {
                    destination: Place::Memory {
                        address: b(B::Add, r(7), c(32)),
                        width: Width::U64,
                    },
                    value: b(op, load(40), load(48)),
                }],
                control: Control::Return(b(op, load(56), r(0))),
            },
        ],
    )
    .unwrap()
}
fn expand(e: &Expr) -> Expr {
    match e {
        Expr::Binary(B::Insert { start, width }, a, z) => {
            let a = expand(a);
            let z = expand(z);
            if *start >= 64 {
                return b(B::Or, a, b(B::And, z, c(0)));
            }
            let mask = ((((1u128 << width.bits()) - 1) << *start) & u128::from(u64::MAX)) as u64;
            b(
                B::Or,
                b(B::And, a, c(!mask)),
                b(B::And, b(B::Shl, z, c(u64::from(*start))), c(mask)),
            )
        }
        Expr::Binary(op, a, z) => b(*op, expand(a), expand(z)),
        Expr::Unary(op, v) => Expr::unary(*op, expand(v)),
        Expr::Select {
            condition,
            taken,
            not_taken,
        } => Expr::select(expand(condition), expand(taken), expand(not_taken)),
        Expr::Load { address, width } => Expr::load(expand(address), *width),
        _ => e.clone(),
    }
}
pub fn expanded(source: &Program) -> Program {
    let mut instructions = source.instructions().to_vec();
    for i in &mut instructions {
        for a in &mut i.assignments {
            a.value = expand(&a.value);
        }
        if let Control::Return(e) = &mut i.control {
            *e = expand(e);
        }
    }
    Program::new(0, source.register_count(), instructions).unwrap()
}

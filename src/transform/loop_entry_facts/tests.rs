use super::*;
use crate::model::ir::{IrInstruction, Program, Width};

#[test]
fn trip_bound_uses_the_captured_ssa_load_before_a_register_overwrite() {
    let r = |n| Expr::Register(Reg(n));
    let source = Program::new(
        0,
        3,
        vec![IrInstruction {
            address: 0,
            size: 1,
            assignments: vec![
                Assignment {
                    destination: Reg(0).into(),
                    value: Expr::load(r(2), Width::U64),
                },
                Assignment {
                    destination: Reg(1).into(),
                    value: Expr::binary(
                        BinaryOp::Add,
                        Expr::binary(BinaryOp::And, r(0), Expr::Const(3)),
                        Expr::Const(1),
                    ),
                },
                Assignment {
                    destination: Reg(0).into(),
                    value: Expr::Const(u64::MAX),
                },
            ],
            control: Control::Return(r(1)),
        }],
    )
    .unwrap();
    let discovery = crate::dataflow::lane_patterns::discover(&source).unwrap();
    let value = discovery
        .read_identity(
            Site {
                instruction: 0,
                assignment: None,
            },
            Reg(1),
        )
        .unwrap();
    let mut bounds = Bounds {
        discovery: &discovery,
        source: &source,
        remaining: 512,
        cache: BTreeMap::new(),
    };
    assert_eq!(bounds.value(value, 0), Some((1, 4)));
    let mut exhausted = Bounds {
        remaining: 1,
        ..bounds
    };
    exhausted.cache.clear();
    assert_eq!(exhausted.value(value, 0), None);
}

#[test]
fn wrapping_trip_arithmetic_keeps_the_full_word_interval() {
    let source = Program::new(
        0,
        2,
        vec![IrInstruction {
            address: 0,
            size: 1,
            assignments: vec![Assignment {
                destination: Reg(1).into(),
                value: Expr::binary(
                    BinaryOp::Add,
                    Expr::binary(BinaryOp::And, Expr::Register(Reg(0)), Expr::Const(3)),
                    Expr::Const(u64::MAX),
                ),
            }],
            control: Control::Return(Expr::Register(Reg(1))),
        }],
    )
    .unwrap();
    let discovery = crate::dataflow::lane_patterns::discover(&source).unwrap();
    let value = discovery
        .read_identity(
            Site {
                instruction: 0,
                assignment: None,
            },
            Reg(1),
        )
        .unwrap();
    let mut bounds = Bounds {
        discovery: &discovery,
        source: &source,
        remaining: 512,
        cache: BTreeMap::new(),
    };
    assert_eq!(bounds.value(value, 0), Some((0, u64::MAX)));
}

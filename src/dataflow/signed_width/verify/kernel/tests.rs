use super::*;
use crate::model::ir::{Control, Expr, IrInstruction, Program, Reg};

fn execute(expression: Expr, inputs: &[u64]) -> u64 {
    Program::new(
        0,
        inputs.len(),
        vec![IrInstruction {
            address: 0,
            size: 1,
            assignments: vec![],
            control: Control::Return(expression),
        }],
    )
    .unwrap()
    .execute(inputs, 1)
    .unwrap()
    .value
}

fn binary(op: B, a: u64, b: u64) -> u64 {
    execute(
        Expr::binary(op, Expr::Register(Reg(0)), Expr::Register(Reg(1))),
        &[a, b],
    )
}

#[test]
fn independent_exact_kernel_matches_executable_word_boundaries_for_every_operator() {
    let mut operations = vec![
        B::Add,
        B::Sub,
        B::Mul,
        B::And,
        B::Or,
        B::Xor,
        B::Shl,
        B::Shr,
        B::AShr,
        B::Eq,
        B::Ne,
        B::Ult,
        B::Ule,
        B::UMulHigh,
        B::SMulHigh,
        B::UDiv,
        B::URem,
        B::SDiv,
        B::SRem,
    ];
    for width in [Width::U8, Width::U16, Width::U32, Width::U64] {
        for start in [0, 1, 7, 31, 32, 60, 63, 64, 255] {
            operations.push(B::Insert { start, width });
        }
    }
    let values = [
        0,
        1,
        2,
        63,
        64,
        127,
        128,
        255,
        65535,
        1 << 31,
        (1 << 63) - 1,
        1 << 63,
        (1 << 63) + 1,
        u64::MAX - 1,
        u64::MAX,
    ];
    for op in operations {
        for a in values {
            for b in values {
                assert_eq!(
                    constant_binary(op, a, b),
                    binary(op, a, b),
                    "{op:?}/{a}/{b}"
                );
            }
        }
    }
    for width in [Width::U8, Width::U16, Width::U32, Width::U64] {
        let mut operations = vec![U::SignExtend(width)];
        operations
            .extend([0, 1, 7, 8, 31, 32, 60, 63, 64, 255].map(|start| U::Extract { start, width }));
        for op in operations {
            for value in values {
                let actual = execute(Expr::unary(op, Expr::Register(Reg(0))), &[value]);
                assert_eq!(constant_unary(op, value), actual, "{op:?}/{value}");
            }
        }
    }
}

#[test]
fn signed_intervals_cover_negative_divisions_remainders_shifts_and_bitwise_prefixes() {
    for width in [Width::U8, Width::U16, Width::U32, Width::U64] {
        let input = Range::storage(width);
        let endpoints = [
            input.lo,
            input.lo + 1,
            -127,
            -2,
            -1,
            0,
            1,
            2,
            127,
            input.hi - 1,
            input.hi,
        ];
        for a in endpoints
            .into_iter()
            .filter(|&x| input.lo <= x && x <= input.hi)
        {
            for divisor in [0, 1, -1, 2, -2, 31, -31, 1i128 << 63, -(1i128 << 63)] {
                let divisor = word(divisor);
                for op in [B::SDiv, B::SRem] {
                    let cap = super::binary(op, input, Range::exact(divisor));
                    assert!(
                        cap.contains(Range::exact(binary(op, word(a), divisor))),
                        "{width:?}/{op:?}/{a}/{divisor}"
                    );
                }
            }
            for count in [0, 1, 63, 64, 65, 127, u64::MAX] {
                let actual = Range::exact(binary(B::AShr, word(a), count));
                assert!(super::binary(B::AShr, input, Range::exact(count)).contains(actual));
                assert!(super::binary(B::AShr, input, Range::FULL).contains(actual));
            }
            for other in [Width::U8, Width::U16, Width::U32, Width::U64] {
                let right = Range::storage(other);
                for b in [right.lo, right.lo + 1, -1, 0, 1, right.hi] {
                    for op in [B::And, B::Or, B::Xor] {
                        let actual = Range::exact(binary(op, word(a), word(b)));
                        assert!(
                            super::binary(op, input, right).contains(actual),
                            "{width:?}/{other:?}/{op:?}/{a}/{b}"
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn extraction_loads_and_sign_extension_distinguish_positive_unsigned_values() {
    assert!(!Range::storage(Width::U8).contains(Range::exact(128)));
    assert!(!Range::storage(Width::U8).contains(load(Width::U8)));
    assert!(Range::storage(Width::U16).contains(load(Width::U8)));
    assert!(!Range::storage(Width::U16).contains(load(Width::U16)));
    assert!(Range::storage(Width::U32).contains(load(Width::U16)));
    for width in [Width::U8, Width::U16, Width::U32, Width::U64] {
        for start in [0, 1, 7, 31, 32, 60, 63, 64, 255] {
            let op = U::Extract { start, width };
            let cap = unary(op, Range::FULL);
            for input in [0, 1, 255, 65535, 1 << 63, u64::MAX] {
                assert!(cap.contains(Range::exact(execute(
                    Expr::unary(op, Expr::Register(Reg(0))),
                    &[input]
                ))));
            }
        }
        assert_eq!(
            unary(U::SignExtend(width), Range::FULL),
            Range::storage(width)
        );
    }
    assert_eq!(
        unary(U::SignExtend(Width::U16), Range::storage(Width::U8)),
        Range::storage(Width::U8)
    );
}

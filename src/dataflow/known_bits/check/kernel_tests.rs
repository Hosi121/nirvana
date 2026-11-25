use super::*;
use crate::model::ir::Width;

fn binary_ops() -> Vec<B> {
    let mut ops = vec![
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
        for start in [0, 1, 7, 8, 31, 32, 56, 63, 64, 65, 127, 128, 255] {
            ops.push(B::Insert { start, width });
        }
    }
    ops
}

fn unary_ops() -> Vec<UnaryOp> {
    let mut ops = Vec::new();
    for width in [Width::U8, Width::U16, Width::U32, Width::U64] {
        ops.push(UnaryOp::SignExtend(width));
        for start in [0, 1, 7, 8, 31, 32, 56, 63, 64, 65, 127, 128, 255] {
            ops.push(UnaryOp::Extract { start, width });
        }
    }
    ops
}

fn boundary_words() -> Vec<u64> {
    let mut values = vec![
        0,
        1,
        2,
        3,
        u64::MAX,
        u64::MAX - 1,
        0xaaaa_aaaa_aaaa_aaaa,
        0x5555_5555_5555_5555,
    ];
    for bit in [3, 7, 8, 15, 16, 31, 32, 62, 63] {
        let n = 1u64 << bit;
        values.extend([n - 1, n, n + 1, u64::MAX - n]);
    }
    values.sort_unstable();
    values.dedup();
    values
}

fn ternary_cubes(positions: [u32; 4], background: u64) -> Vec<KnownBits> {
    (0..81)
        .map(|mut code| {
            let mut zero = !background;
            let mut one = background;
            for bit in positions {
                let mask = 1u64 << bit;
                zero &= !mask;
                one &= !mask;
                match code % 3 {
                    0 => zero |= mask,
                    1 => one |= mask,
                    _ => {}
                }
                code /= 3;
            }
            KnownBits::new(zero, one).unwrap()
        })
        .collect()
}

fn cubes() -> Vec<KnownBits> {
    let mut result = vec![KnownBits::UNKNOWN];
    result.extend(boundary_words().into_iter().map(KnownBits::constant));
    for bits in 0..=64 {
        result.push(KnownBits::new(low(bits), 0).unwrap());
        result.push(KnownBits::new(!low(bits), 0).unwrap());
    }
    result.extend([
        KnownBits::new(0, 1 << 63).unwrap(),
        KnownBits::new(1 << 63, 1).unwrap(),
        KnownBits::new(0xaaaa_aaaa_aaaa_aaaa, 0).unwrap(),
        KnownBits::new(0, 0x5555_5555_5555_5555).unwrap(),
        KnownBits::new(0, 64).unwrap(), // Known upper shift bits are ignored.
    ]);
    for positions in [
        [0, 1, 2, 3],
        [0, 7, 31, 63],
        [15, 16, 32, 63],
        [60, 61, 62, 63],
    ] {
        for background in [0, u64::MAX, 0xaaaa_aaaa_aaaa_aaaa] {
            result.extend(ternary_cubes(positions, background));
        }
    }
    result
}

fn examples(cube: KnownBits) -> Vec<u64> {
    let free = !(cube.zero | cube.one);
    if free.count_ones() > 4 {
        return vec![
            cube.one,
            !cube.zero,
            cube.one | (free & 0xaaaa_aaaa_aaaa_aaaa),
            cube.one | (free & 0x5555_5555_5555_5555),
        ];
    }
    let mut result = vec![cube.one];
    for bit in 0..64 {
        if free & (1 << bit) != 0 {
            let count = result.len();
            for i in 0..count {
                result.push(result[i] | (1 << bit));
            }
        }
    }
    result
}

#[test]
fn constants_match_ir_at_arithmetic_and_clipping_boundaries() {
    let words = boundary_words();
    for op in unary_ops() {
        for &value in &words {
            assert_eq!(
                unary(op, KnownBits::constant(value)).number(),
                Some(op.evaluate(value)),
                "{op:?} {value:#x}"
            );
        }
    }
    for op in binary_ops() {
        for &left in &words {
            for &right in &words {
                assert_eq!(
                    binary(op, KnownBits::constant(left), KnownBits::constant(right)).number(),
                    Some(op.evaluate(left, right)),
                    "{op:?} {left:#x} {right:#x}"
                );
            }
        }
    }
}

#[test]
fn every_rule_retains_exact_producer_precision_and_work_decisions_on_bit_cubes() {
    let cubes = cubes();
    let ops = binary_ops();
    let unary_ops = unary_ops();
    // Explicit constants ensure that zero, +/-1, power-of-two, and signed
    // boundary branches are exercised with every kind of nonconstant input.
    let divisors = [0, 1, 2, 4, 8, 63, 64, 65, 1 << 63, u64::MAX];
    for (i, &left) in cubes.iter().enumerate() {
        for &op in &unary_ops {
            let proof = unary(op, left);
            assert_eq!(proof, KnownBits::unary(op, left), "{op:?} {left:?}");
        }
        let right_indices = [
            i,
            (i * 17 + 1) % cubes.len(),
            (i * 31 + 7) % cubes.len(),
            (i * 61 + 13) % cubes.len(),
        ];
        let rights = right_indices
            .into_iter()
            .map(|index| cubes[index])
            .chain(divisors.into_iter().map(KnownBits::constant));
        for right in rights {
            for &op in &ops {
                let proof = binary(op, left, right);
                assert_eq!(proof.zero & proof.one, 0, "{op:?} {left:?} {right:?}");
                assert_eq!(
                    proof,
                    KnownBits::binary(op, left, right),
                    "precision: {op:?} {left:?} {right:?}: {proof:?}"
                );
            }
        }
    }
}

#[test]
fn cube_masks_cover_real_ir_results_including_unknown_sign_and_shift_bits() {
    let cubes = cubes();
    let ops = binary_ops();
    for (i, &left) in cubes.iter().enumerate() {
        let values = examples(left);
        for op in unary_ops() {
            let proof = unary(op, left);
            for &value in &values {
                assert!(
                    proof.contains(op.evaluate(value)),
                    "{op:?} {left:?} {value:#x}"
                );
            }
        }
        if i % 5 != 0 {
            continue;
        }
        for right in [
            cubes[(i * 37 + 3) % cubes.len()],
            cubes[(i * 71 + 11) % cubes.len()],
        ] {
            let right_values = examples(right);
            for &op in &ops {
                let proof = binary(op, left, right);
                for &a in &values {
                    for &b in &right_values {
                        assert!(
                            proof.contains(op.evaluate(a, b)),
                            "unsound: {op:?} {left:?} {right:?}: {a:#x} {b:#x} -> {proof:?}"
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn lower_prefix_carry_and_borrow_are_exact_for_all_four_bit_cubes() {
    for positions in [[0, 1, 2, 3], [0, 1, 31, 63]] {
        let cubes = ternary_cubes(positions, 0);
        for &left in &cubes {
            let left_values = examples(left);
            for &right in &cubes {
                let right_values = examples(right);
                for op in [B::Add, B::Sub] {
                    let mut exact = None;
                    for &a in &left_values {
                        for &b in &right_values {
                            let value = KnownBits::constant(op.evaluate(a, b));
                            exact = Some(exact.map_or(value, |old: KnownBits| old.join(value)));
                        }
                    }
                    assert_eq!(
                        binary(op, left, right),
                        exact.unwrap(),
                        "{op:?} {left:?} {right:?}"
                    );
                }
            }
        }
    }
}

#[test]
fn total_division_high_products_and_masked_sign_fill_have_fixed_examples() {
    let negative = KnownBits::new(0, 1 << 63).unwrap();
    let nonnegative = KnownBits::new(1 << 63, 0).unwrap();
    assert_eq!(
        binary(B::SDiv, negative, KnownBits::constant(0)),
        KnownBits::constant(1)
    );
    assert_eq!(
        binary(B::SDiv, nonnegative, KnownBits::constant(0)),
        KnownBits::constant(u64::MAX)
    );
    assert_eq!(
        binary(B::SDiv, KnownBits::UNKNOWN, KnownBits::constant(0)),
        KnownBits::new(0, 1).unwrap()
    );
    for op in [B::URem, B::SRem] {
        assert_eq!(binary(op, negative, KnownBits::constant(0)), negative);
    }
    let even_negative = KnownBits::new(15, 1 << 63).unwrap();
    assert_eq!(
        binary(B::SRem, even_negative, KnownBits::constant(u64::MAX - 7)),
        KnownBits::constant(0)
    );
    let count = KnownBits::new(63, 64).unwrap(); // All compatible counts are zero modulo 64.
    for op in [B::Shl, B::Shr, B::AShr] {
        assert_eq!(binary(op, negative, count), negative);
    }
    assert_eq!(
        binary(B::AShr, negative, KnownBits::constant(127)),
        KnownBits::constant(u64::MAX)
    );
    assert_eq!(
        binary(B::AShr, nonnegative, KnownBits::constant(127)),
        KnownBits::constant(0)
    );
    for op in [B::UMulHigh, B::SMulHigh] {
        assert_eq!(
            binary(op, KnownBits::UNKNOWN, KnownBits::constant(0)),
            KnownBits::constant(0)
        );
    }
}

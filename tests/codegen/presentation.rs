use std::cell::Cell;

use nirvana::ir::{
    Assignment, BinaryOp as B, Control, Expr, IrInstruction, Place, Program, Reg, RunStatus, Width,
};
use nirvana::presentation::normalize;

use crate::support::ir::c;
use crate::support::ir::r;
fn b(op: B, left: Expr, right: Expr) -> Expr {
    Expr::binary(op, left, right)
}
fn load(address: Expr, width: Width) -> Expr {
    Expr::load(address, width)
}

fn nodes(expression: &Expr) -> usize {
    let mut pending = vec![expression];
    let mut count = 0;
    while let Some(expression) = pending.pop() {
        count += 1;
        match expression {
            Expr::Const(_) | Expr::Register(_) => {}
            Expr::Binary(_, left, right) => {
                pending.push(right);
                pending.push(left);
            }
            Expr::Load { address, .. } => pending.push(address),
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => {
                pending.push(not_taken);
                pending.push(taken);
                pending.push(condition);
            }
        }
    }
    count
}

fn load_widths(expression: &Expr) -> Vec<Width> {
    let mut pending = vec![expression];
    let mut widths = Vec::new();
    while let Some(expression) = pending.pop() {
        match expression {
            Expr::Const(_) | Expr::Register(_) => {}
            Expr::Binary(_, left, right) => {
                pending.push(right);
                pending.push(left);
            }
            Expr::Load { address, width } => {
                widths.push(*width);
                pending.push(address);
            }
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => {
                pending.push(not_taken);
                pending.push(taken);
                pending.push(condition);
            }
        }
    }
    widths
}

fn program(expression: Expr) -> Program {
    Program::new(
        0,
        3,
        vec![IrInstruction {
            address: 0,
            size: 1,
            assignments: vec![],
            control: Control::Return(expression),
        }],
    )
    .unwrap()
}

fn check(expression: &Expr, widths: [Width; 3]) {
    let lookup = |Reg(index): Reg| widths.get(index).copied().unwrap_or(Width::U64);
    let changed = normalize(expression, lookup);
    assert!(
        nodes(&changed) <= nodes(expression),
        "{expression:?} -> {changed:?}"
    );
    assert_eq!(
        normalize(&changed, lookup),
        changed,
        "not idempotent: {expression:?}"
    );
    assert_eq!(
        load_widths(&changed),
        load_widths(expression),
        "load list: {expression:?}"
    );
    let before = program(expression.clone());
    let after = program(changed);
    let boundaries = [
        0,
        1,
        7,
        63,
        64,
        127,
        128,
        255,
        256,
        65535,
        65536,
        u32::MAX as u64,
        1 << 32,
        1 << 63,
        u64::MAX,
    ];
    let memory: Vec<u8> = (0..32).map(|index| (index * 17) as u8).collect();
    for (index, &value) in boundaries.iter().enumerate() {
        for address in [0, 0x1000, 0x1001, 0x101f, u64::MAX] {
            let input = [
                value & widths[0].mask(),
                boundaries[(index * 7 + 3) % boundaries.len()] & widths[1].mask(),
                address & widths[2].mask(),
            ];
            for (base, bytes) in [
                (0x1000, memory.as_slice()),
                (0, &[][..]),
                (u64::MAX - 7, &memory[..8]),
            ] {
                for limit in [0, 1] {
                    assert_eq!(
                        before.run_with_memory(&input, base, bytes, limit),
                        after.run_with_memory(&input, base, bytes, limit),
                        "expression={expression:?}, input={input:?}, base={base:#x}, limit={limit}",
                    );
                }
            }
        }
    }
}

#[test]
fn narrow_register_masks_are_removed_or_tightened_without_zero_assumptions() {
    for width in [Width::U8, Width::U16, Width::U32, Width::U64] {
        for mask in [
            0,
            255,
            65535,
            u32::MAX as u64,
            u64::MAX,
            0xffff_0000,
            0xffff_ffff_ffff_ff00,
        ] {
            let expression = b(B::And, r(0), c(mask));
            let result = normalize(&expression, |_| width);
            let expected = if width.mask() & !mask == 0 {
                r(0)
            } else if width.mask() & mask == 0 {
                c(0)
            } else {
                b(B::And, r(0), c(width.mask() & mask))
            };
            assert_eq!(result, expected, "width={width:?}, mask={mask:#x}");
            check(&expression, [width, Width::U64, Width::U64]);
            check(&b(B::And, c(mask), r(0)), [width, Width::U64, Width::U64]);
        }
    }
    let wide = b(B::And, r(0), c(0xffff_ffff_0000_0000));
    assert_eq!(normalize(&wide, |_| Width::U64), wide);
}

#[test]
fn certified_remainder_ranges_use_bit_hulls_and_keep_real_clips() {
    let quotient = b(B::Shr, b(B::UMulHigh, r(0), c(0xcccc_cccc_cccc_cccd)), c(3));
    let remainder = b(B::Sub, r(0), b(B::Mul, quotient, c(10)));
    assert_eq!(
        normalize(&b(B::And, remainder.clone(), c(15)), |_| Width::U64),
        remainder
    );
    // The numeric upper bound 9 has hull 15. Using 9 as a bitmask would
    // incorrectly turn (2 % 10) & 9 == 0 into 2 % 10 == 2.
    let clipped = b(B::And, remainder.clone(), c(9));
    assert_eq!(normalize(&clipped, |_| Width::U64), clipped);
    assert_ne!(normalize(&clipped, |_| Width::U64), remainder);
    for mask in [0, 1, 2, 3, 7, 9, 15, 255, u32::MAX as u64, u64::MAX] {
        check(&b(B::And, remainder.clone(), c(mask)), [Width::U64; 3]);
    }
    let lane = b(B::And, r(0), c(u32::MAX as u64));
    let narrow_quotient = b(B::Shr, b(B::Mul, lane.clone(), c(0xcccc_cccd)), c(35));
    let narrow_remainder = b(B::Sub, lane, b(B::Mul, narrow_quotient.clone(), c(10)));
    let sum = b(B::Add, narrow_quotient, narrow_remainder);
    let masked = b(B::And, sum.clone(), c(u32::MAX as u64));
    assert_eq!(normalize(&masked, |_| Width::U64), sum);
    check(&masked, [Width::U64; 3]);
    // A separate quotient register carries no arithmetic certificate.
    let unknown = b(B::And, b(B::Sub, r(0), b(B::Mul, r(1), c(10))), c(15));
    assert_eq!(normalize(&unknown, |_| Width::U64), unknown);
    check(&unknown, [Width::U64; 3]);
}

#[test]
fn adjacent_power_of_two_scales_fold_after_masks_without_moving_loads() {
    let operands = [
        r(0),
        load(r(2), Width::U16),
        Expr::select(r(0), load(r(2), Width::U8), r(1)),
    ];
    for operand in operands {
        for factor in [0, 3, 5, 9, 1 << 31, u64::MAX] {
            for scale in [2, 4, 8, 1 << 32, 1 << 63] {
                let expression = b(B::Mul, b(B::Mul, operand.clone(), c(factor)), c(scale));
                check(&expression, [Width::U64; 3]);
            }
        }
    }
    let revealed = b(
        B::Mul,
        b(B::And, b(B::Mul, r(0), c(5)), c(u32::MAX as u64)),
        c(2),
    );
    assert_eq!(normalize(&revealed, |_| Width::U8), b(B::Mul, r(0), c(10)));
    check(&revealed, [Width::U8, Width::U64, Width::U64]);
    let clipped = b(B::Mul, b(B::And, b(B::Mul, r(0), c(5)), c(255)), c(2));
    check(&clipped, [Width::U64; 3]);
    assert_ne!(normalize(&clipped, |_| Width::U64), b(B::Mul, r(0), c(10)));
    let non_power = b(B::And, b(B::Mul, b(B::Mul, r(0), c(3)), c(3)), c(31));
    check(&non_power, [Width::U8, Width::U64, Width::U64]);
}

#[test]
fn partial_register_merges_drop_only_proven_zero_high_parts() {
    let expression = b(
        B::Or,
        b(B::And, r(0), c(0xffff_ffff_0000_0000)),
        b(B::And, r(1), c(0xffff_ffff)),
    );
    let widths = [Width::U16, Width::U8, Width::U64];
    assert_eq!(normalize(&expression, |Reg(index)| widths[index]), r(1));
    check(&expression, widths);
    let byte_update = b(
        B::And,
        b(
            B::Or,
            b(B::And, r(0), c(0xffff_ffff_ffff_ff00)),
            b(B::And, r(1), c(255)),
        ),
        c(65535),
    );
    assert_eq!(
        normalize(&byte_update, |Reg(index)| widths[index]),
        b(B::Or, b(B::And, r(0), c(0xff00)), r(1))
    );
    check(&byte_update, widths);
}

#[test]
fn possible_one_masks_propagate_through_shifts_boolean_values_and_arithmetic() {
    let cases = [
        b(B::And, b(B::Shl, r(0), c(8)), c(0xffff)),
        b(B::And, b(B::Shr, r(1), c(8)), c(255)),
        b(B::And, b(B::Eq, r(0), r(1)), c(1)),
        b(B::And, b(B::Add, r(0), r(0)), c(65535)),
        b(B::And, b(B::Mul, r(0), r(1)), c(0xffff_ffff)),
        b(B::And, b(B::UMulHigh, r(0), r(1)), c(0xffff)),
        b(
            B::And,
            b(B::Shr, b(B::And, r(1), c(0x8000)), r(0)),
            c(65535),
        ),
    ];
    for expression in cases {
        let result = normalize(&expression, |_| Width::U8);
        assert!(
            nodes(&result) < nodes(&expression),
            "{expression:?} -> {result:?}"
        );
        check(&expression, [Width::U8, Width::U8, Width::U64]);
    }
}

#[test]
fn loads_keep_their_count_order_and_faults_even_when_the_result_is_known_zero() {
    let first = load(c(0x2000), Width::U16);
    let second = load(c(0x3000), Width::U8);
    let cases = [
        b(B::And, first.clone(), c(0)),
        b(B::And, first.clone(), c(0xffff_0000)),
        b(B::And, c(0), first.clone()),
        b(B::Mul, c(0), first.clone()),
        b(B::UMulHigh, first.clone(), c(0)),
        b(B::Or, c(u64::MAX), first.clone()),
        b(
            B::Or,
            b(B::And, first.clone(), c(0xffff_0000)),
            b(B::And, second.clone(), c(0)),
        ),
        b(B::Eq, first.clone(), first.clone()),
        load(load(r(2), Width::U64), Width::U16),
        b(
            B::And,
            load(b(B::And, r(2), c(u64::MAX)), Width::U16),
            c(u32::MAX as u64),
        ),
    ];
    for expression in cases {
        check(&expression, [Width::U16, Width::U8, Width::U64]);
    }
    let masked = b(B::And, first.clone(), c(0xffff_0000));
    assert_eq!(normalize(&masked, |_| Width::U16), b(B::And, first, c(0)));
}

#[test]
fn lazy_selects_keep_faulting_conditions_and_even_unselected_loads() {
    let fault = load(c(u64::MAX), Width::U64);
    let cases = [
        Expr::select(fault.clone(), r(0), r(0)),
        Expr::select(fault.clone(), c(0), c(0)),
        Expr::select(c(1), r(0), fault.clone()),
        Expr::select(c(0), fault.clone(), r(0)),
        Expr::select(r(0), load(r(2), Width::U8), load(c(0x2000), Width::U16)),
        Expr::select(b(B::And, load(r(2), Width::U8), c(0)), fault.clone(), r(0)),
        Expr::select(r(0), load(r(2), Width::U16), load(r(2), Width::U16)),
    ];
    for expression in cases {
        assert!(matches!(
            normalize(&expression, |_| Width::U16),
            Expr::Select { .. }
        ));
        check(&expression, [Width::U16, Width::U8, Width::U64]);
    }
}

#[test]
fn masked_shift_counts_and_wrapping_64_bit_values_are_preserved() {
    for count in [0, 1, 31, 32, 63, 64, 65, 128, u64::MAX] {
        for op in [B::Shl, B::Shr] {
            check(&b(op, r(0), c(count)), [Width::U64, Width::U64, Width::U64]);
            check(
                &b(B::And, b(op, load(r(2), Width::U64), c(count)), c(u64::MAX)),
                [Width::U64; 3],
            );
        }
    }
    for op in [B::Add, B::Sub, B::Mul, B::UMulHigh] {
        check(
            &b(B::And, b(op, r(0), r(1)), c(u32::MAX as u64)),
            [Width::U64; 3],
        );
    }
}

#[test]
fn first_fault_and_prior_guest_memory_writes_are_identical() {
    let expression = b(
        B::Or,
        b(B::And, load(c(0x2000), Width::U16), c(0xffff_0000)),
        load(c(0x3000), Width::U8),
    );
    let make = |expression| {
        Program::new(
            0,
            3,
            vec![IrInstruction {
                address: 0,
                size: 1,
                assignments: vec![Assignment {
                    destination: Place::Memory {
                        address: c(0x1000),
                        width: Width::U8,
                    },
                    value: c(0xa5),
                }],
                control: Control::Return(expression),
            }],
        )
        .unwrap()
    };
    let before = make(expression.clone());
    let after = make(normalize(&expression, |_| Width::U16));
    let expected = before.run_with_memory(&[0; 3], 0x1000, &[0; 8], 1).unwrap();
    assert_eq!(
        after.run_with_memory(&[0; 3], 0x1000, &[0; 8], 1).unwrap(),
        expected
    );
    assert_eq!(expected.state.memory[0], 0xa5);
    let RunStatus::Fault(fault) = expected.status else {
        panic!("expected fault")
    };
    assert_eq!(fault.address, 0x2000);
    assert_eq!(fault.width, Width::U16);
    assert_eq!(fault.access, nirvana::ir::AccessKind::Read);
}

#[test]
fn normalized_store_addresses_preserve_destination_checks_before_rhs_faults() {
    let address = b(B::And, r(0), c(u32::MAX as u64));
    let make = |address| {
        Program::new(
            0,
            3,
            vec![IrInstruction {
                address: 0,
                size: 1,
                assignments: vec![
                    Assignment {
                        destination: Place::Memory {
                            address: c(0x1000),
                            width: Width::U8,
                        },
                        value: c(0xa5),
                    },
                    Assignment {
                        destination: Place::Memory {
                            address,
                            width: Width::U64,
                        },
                        value: load(c(0x3000), Width::U16),
                    },
                ],
                control: Control::Return(c(0)),
            }],
        )
        .unwrap()
    };
    let before = make(address.clone());
    let after = make(normalize(&address, |_| Width::U16));
    for pointer in [0, 0x1000, 0x1001, 0xffff] {
        let expected = before
            .run_with_memory(&[pointer, 0, 0], 0x1000, &[0; 8], 1)
            .unwrap();
        assert_eq!(
            after
                .run_with_memory(&[pointer, 0, 0], 0x1000, &[0; 8], 1)
                .unwrap(),
            expected
        );
        assert_eq!(expected.state.memory[0], 0xa5);
        let RunStatus::Fault(fault) = expected.status else {
            panic!("expected fault")
        };
        if pointer == 0x1000 {
            assert_eq!(
                (fault.access, fault.address, fault.width),
                (nirvana::ir::AccessKind::Read, 0x3000, Width::U16)
            );
        } else {
            assert_eq!(
                (fault.access, fault.address, fault.width),
                (nirvana::ir::AccessKind::Write, pointer, Width::U64)
            );
        }
    }
}

#[test]
fn resource_fallback_is_unchanged_and_never_queries_register_widths() {
    let calls = Cell::new(0);
    let width = |_| {
        calls.set(calls.get() + 1);
        Width::U8
    };
    let mut deep = r(0);
    for _ in 0..260 {
        deep = b(B::And, deep, c(255));
    }
    let changed = normalize(&deep, width);
    assert_eq!(changed, deep);
    assert_eq!(calls.get(), 0);
    fn tree(depth: usize) -> Expr {
        if depth == 0 {
            r(0)
        } else {
            b(B::And, tree(depth - 1), tree(depth - 1))
        }
    }
    let large = tree(16);
    assert!(nodes(&large) > 65_536);
    let changed = normalize(&large, width);
    assert_eq!(changed, large);
    assert_eq!(calls.get(), 0);
}

#[test]
fn generated_masked_input_executions_preserve_results_faults_and_load_structure() {
    fn random(seed: &mut u64) -> u64 {
        *seed ^= *seed << 13;
        *seed ^= *seed >> 7;
        *seed ^= *seed << 17;
        *seed
    }
    const OPERATIONS: [B; 13] = [
        B::Add,
        B::Sub,
        B::Mul,
        B::And,
        B::Or,
        B::Xor,
        B::Shl,
        B::Shr,
        B::Eq,
        B::Ne,
        B::Ult,
        B::Ule,
        B::UMulHigh,
    ];
    const NUMBERS: [u64; 16] = [
        0,
        1,
        7,
        31,
        32,
        63,
        64,
        65,
        128,
        255,
        65535,
        u32::MAX as u64,
        0xffff_0000,
        0xffff_ffff_0000_0000,
        1 << 63,
        u64::MAX,
    ];
    fn expression(seed: &mut u64, depth: usize) -> Expr {
        if depth == 0 {
            return if random(seed) & 1 == 0 {
                r(random(seed) as usize % 3)
            } else {
                c(NUMBERS[random(seed) as usize % NUMBERS.len()])
            };
        }
        match random(seed) % 6 {
            0 => {
                let address = if random(seed) & 1 == 0 {
                    r(2)
                } else {
                    c(0x1000 + (random(seed) & 31))
                };
                load(
                    address,
                    [Width::U8, Width::U16, Width::U32, Width::U64][random(seed) as usize % 4],
                )
            }
            1 => {
                let condition = expression(seed, depth - 1);
                let taken = expression(seed, depth - 1);
                let not_taken = expression(seed, depth - 1);
                Expr::select(condition, taken, not_taken)
            }
            _ => {
                let op = OPERATIONS[random(seed) as usize % OPERATIONS.len()];
                let left = expression(seed, depth - 1);
                let right = if random(seed) & 1 == 0 {
                    expression(seed, depth - 1)
                } else {
                    c(NUMBERS[random(seed) as usize % NUMBERS.len()])
                };
                b(op, left, right)
            }
        }
    }
    let mut seed = 0x9123_abcd_ef78_5462;
    let profiles = [
        [Width::U8, Width::U16, Width::U64],
        [Width::U16, Width::U32, Width::U64],
        [Width::U32, Width::U64, Width::U64],
        [Width::U64; 3],
    ];
    let mut smaller = 0;
    for _ in 0..120 {
        let expression = b(
            B::And,
            expression(&mut seed, 4),
            c(NUMBERS[random(&mut seed) as usize % NUMBERS.len()]),
        );
        for widths in profiles {
            let changed = normalize(&expression, |Reg(index)| widths[index]);
            smaller += usize::from(nodes(&changed) < nodes(&expression));
            check(&expression, widths);
        }
    }
    assert!(smaller > 100, "non-vacuous shrinking cases: {smaller}");
}

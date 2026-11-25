use nirvana::ir::{Assignment, BinaryOp, Control, Expr, IrInstruction, Place, Program, Reg, Width};
use nirvana::reduce::reduce;
use nirvana::value_width::ValueWidths;

use crate::support::ir::c;
use crate::support::ir::r;

#[test]
fn copied_guard_operands_keep_checked_facts_within_the_source_budget() {
    let registers = 1001;
    let p = program(
        registers,
        vec![
            i(
                0,
                (1..registers).map(|reg| set(reg, r(reg - 1))).collect(),
                Control::Branch {
                    condition: binary(BinaryOp::Ult, r(registers - 1), c(256)),
                    target: 2,
                },
            ),
            i(1, vec![], Control::Return(c(0))),
            i(2, vec![], Control::Return(c(1))),
        ],
    );
    let widths = ValueWidths::analyze(&p);
    assert!(widths.verification().is_ok(), "{:?}", widths.verification());
    let target = p.cfg().block_at(2).unwrap().index();
    assert_eq!(widths.incoming().unwrap()[target], Some(vec![8; registers]));
    // These values were read before the guard. The edge condition cannot
    // retroactively narrow their source-entry storage observations.
    assert!(
        widths
            .widths()
            .unwrap()
            .iter()
            .all(|&width| width == Width::U64)
    );
}

fn binary(op: BinaryOp, left: Expr, right: Expr) -> Expr {
    Expr::binary(op, left, right)
}
fn set(register: usize, value: Expr) -> Assignment {
    Assignment {
        destination: Reg(register).into(),
        value,
    }
}
fn load(width: Width, address: u64) -> Expr {
    Expr::load(c(address), width)
}
fn i(address: u64, assignments: Vec<Assignment>, control: Control) -> IrInstruction {
    IrInstruction {
        address,
        size: 1,
        assignments,
        control,
    }
}
fn program(registers: usize, instructions: Vec<IrInstruction>) -> Program {
    Program::new(0, registers, instructions).unwrap()
}
fn straight(registers: usize, assignments: Vec<Assignment>) -> Program {
    program(registers, vec![i(0, assignments, Control::Return(c(0)))])
}
fn expression_width(expression: Expr) -> Width {
    ValueWidths::analyze(&straight(1, vec![set(0, expression)])).width(Reg(0))
}

#[test]
fn overwritten_initial_values_can_narrow_but_unknown_reads_cannot() {
    let p = straight(
        6,
        vec![
            set(0, c(7)),
            set(1, r(0)),
            set(2, r(3)),
            set(3, c(1)),
            set(4, binary(BinaryOp::And, r(5), c(255))),
        ],
    );
    let widths = ValueWidths::analyze(&p);
    for register in [0, 1, 4] {
        assert_eq!(widths.width(Reg(register)), Width::U8);
    }
    for register in [2, 3, 5, 6, usize::MAX] {
        assert_eq!(widths.width(Reg(register)), Width::U64);
    }
    assert_eq!(ValueWidths::default().width(Reg(0)), Width::U64);
}

#[test]
fn constants_and_loads_choose_the_smallest_fitting_unsigned_storage() {
    for (value, width) in [
        (0, Width::U8),
        (255, Width::U8),
        (256, Width::U16),
        (65535, Width::U16),
        (65536, Width::U32),
        (u32::MAX as u64, Width::U32),
        (u32::MAX as u64 + 1, Width::U64),
        (u64::MAX, Width::U64),
    ] {
        assert_eq!(expression_width(c(value)), width, "constant={value}");
    }
    for width in [Width::U8, Width::U16, Width::U32, Width::U64] {
        assert_eq!(expression_width(load(width, 0)), width);
    }
}

#[test]
fn division_storage_bounds_cover_zero_divisors_and_narrow_remainders() {
    fn storage(maximum: u64) -> Width {
        if maximum <= u8::MAX as u64 {
            Width::U8
        } else if maximum <= u16::MAX as u64 {
            Width::U16
        } else if maximum <= u32::MAX as u64 {
            Width::U32
        } else {
            Width::U64
        }
    }
    for width in [Width::U8, Width::U16, Width::U32, Width::U64] {
        for op in [
            BinaryOp::UDiv,
            BinaryOp::URem,
            BinaryOp::SDiv,
            BinaryOp::SRem,
        ] {
            for divisor in [
                Some(0),
                Some(1),
                Some(2),
                Some(3),
                Some(256),
                Some(1 << 63),
                Some(u64::MAX),
                None,
            ] {
                let value = binary(
                    op,
                    binary(BinaryOp::And, r(0), c(width.mask())),
                    divisor.map_or_else(|| r(1), c),
                );
                let p = program(3, vec![i(0, vec![set(2, value)], Control::Return(r(2)))]);
                let inferred = ValueWidths::analyze(&p).width(Reg(2));
                let maximum = match (op, divisor) {
                    (BinaryOp::UDiv, Some(d)) if d != 0 => width.mask() / d,
                    (BinaryOp::UDiv, _) | (BinaryOp::SDiv, _) => u64::MAX,
                    _ => width.mask(),
                };
                assert_eq!(inferred, storage(maximum), "{op:?}/{width:?}/{divisor:?}");
                for x in [0, 1, 127, 128, 255, 256, 0x7fff_ffff, 0x8000_0000, u64::MAX] {
                    for d in [0, 1, 3, 256, 1 << 63, u64::MAX] {
                        let expected = crate::support::ir::division_value(
                            op,
                            x & width.mask(),
                            divisor.unwrap_or(d),
                        );
                        assert_eq!(p.execute(&[x, d, 0], 1).unwrap().value, expected);
                        assert_eq!(expected & !inferred.mask(), 0);
                    }
                }
            }
        }
    }
}

#[test]
fn all_writes_count_even_when_a_later_narrow_value_is_the_only_read() {
    let p = program(
        1,
        vec![i(
            0,
            vec![set(0, load(Width::U32, 0)), set(0, load(Width::U8, 0))],
            Control::Return(r(0)),
        )],
    );
    assert_eq!(ValueWidths::analyze(&p).width(Reg(0)), Width::U32);
    let p = straight(1, vec![set(0, c(u64::MAX)), set(0, c(0))]);
    assert_eq!(ValueWidths::analyze(&p).width(Reg(0)), Width::U64);
}

#[test]
fn unsigned_products_and_additions_cover_promotion_overflow_boundaries() {
    let p = program(
        4,
        vec![i(
            0,
            vec![
                set(0, load(Width::U16, 0)),
                set(1, load(Width::U16, 2)),
                set(2, binary(BinaryOp::Mul, r(0), r(1))),
                set(3, binary(BinaryOp::Add, r(0), r(1))),
            ],
            Control::Return(r(2)),
        )],
    );
    let widths = ValueWidths::analyze(&p);
    assert_eq!(widths.width(Reg(0)), Width::U16);
    assert_eq!(widths.width(Reg(1)), Width::U16);
    assert_eq!(widths.width(Reg(2)), Width::U32);
    assert_eq!(widths.width(Reg(3)), Width::U32);
    let result = p.execute_with_memory(&[0; 4], 0, &[255; 4], 1).unwrap();
    assert_eq!(result.value, 65535 * 65535);
    assert!(result.value > i32::MAX as u64);
    assert_eq!(result.value & !widths.width(Reg(2)).mask(), 0);
    assert_eq!(
        expression_width(binary(BinaryOp::Mul, c(0), c(u64::MAX))),
        Width::U8
    );
    assert_eq!(
        expression_width(binary(BinaryOp::Add, c(0), c(65535))),
        Width::U16
    );
    assert_eq!(
        expression_width(binary(BinaryOp::Add, c(65535), c(1))),
        Width::U32
    );
    assert_eq!(
        expression_width(binary(BinaryOp::Sub, c(255), c(0))),
        Width::U8
    );
    assert_eq!(
        expression_width(binary(BinaryOp::Sub, c(1), c(1))),
        Width::U64
    );
}

#[test]
fn bitwise_comparison_and_high_product_bounds_are_conservative() {
    for op in [BinaryOp::Eq, BinaryOp::Ne, BinaryOp::Ult, BinaryOp::Ule] {
        assert_eq!(expression_width(binary(op, c(u64::MAX), c(0))), Width::U8);
    }
    assert_eq!(
        expression_width(binary(BinaryOp::And, c(u64::MAX), c(255))),
        Width::U8
    );
    for op in [BinaryOp::Or, BinaryOp::Xor] {
        assert_eq!(expression_width(binary(op, c(0xffff), c(255))), Width::U16);
    }
    for (left, right, width) in [
        (u32::MAX as u64, u32::MAX as u64, Width::U8),
        (u64::MAX, 255, Width::U8),
        (u64::MAX, 65535, Width::U16),
        (u64::MAX, u32::MAX as u64, Width::U32),
        (u64::MAX, u64::MAX, Width::U64),
    ] {
        assert_eq!(
            expression_width(binary(BinaryOp::UMulHigh, c(left), c(right))),
            width
        );
    }
}

#[test]
fn constant_shift_counts_are_masked_with_63_and_dynamic_shifts_are_safe() {
    for (op, left_width, shift, result_width) in [
        (BinaryOp::Shr, Width::U64, 64, Width::U64),
        (BinaryOp::Shr, Width::U16, 128, Width::U16),
        (BinaryOp::Shr, Width::U64, 63, Width::U8),
        (BinaryOp::Shr, Width::U32, 24, Width::U8),
        (BinaryOp::Shl, Width::U8, 7, Width::U16),
        (BinaryOp::Shl, Width::U8, 24, Width::U32),
        (BinaryOp::Shl, Width::U8, 25, Width::U64),
        (BinaryOp::Shl, Width::U8, 64, Width::U8),
    ] {
        assert_eq!(
            expression_width(binary(op, load(left_width, 0), c(shift))),
            result_width
        );
    }
    for (op, expected) in [(BinaryOp::Shl, Width::U64), (BinaryOp::Shr, Width::U8)] {
        let p = straight(
            3,
            vec![set(1, load(Width::U8, 0)), set(2, binary(op, r(1), r(0)))],
        );
        assert_eq!(ValueWidths::analyze(&p).width(Reg(2)), expected);
    }
    let p = straight(2, vec![set(1, binary(BinaryOp::Shl, c(0), r(0)))]);
    assert_eq!(ValueWidths::analyze(&p).width(Reg(1)), Width::U8);
}

#[test]
fn address_and_control_reads_observe_unknown_entry_values() {
    let p = program(
        4,
        vec![
            i(
                0,
                vec![
                    Assignment {
                        destination: Place::Memory {
                            address: r(0),
                            width: Width::U8,
                        },
                        value: c(0),
                    },
                    set(0, c(0)),
                    set(1, Expr::load(r(2), Width::U8)),
                    set(2, c(0)),
                ],
                Control::Branch {
                    condition: r(3),
                    target: 1,
                },
            ),
            i(1, vec![set(3, c(1))], Control::Return(r(1))),
        ],
    );
    let widths = ValueWidths::analyze(&p);
    assert_eq!(widths.width(Reg(1)), Width::U8);
    for register in [0, 2, 3] {
        assert_eq!(widths.width(Reg(register)), Width::U64);
    }
}

#[test]
fn diamonds_merge_point_bounds_and_unreachable_writes_are_ignored() {
    let p = program(
        3,
        vec![
            i(
                0,
                vec![],
                Control::Branch {
                    condition: r(0),
                    target: 2,
                },
            ),
            i(1, vec![set(1, load(Width::U8, 0))], Control::Jump(3)),
            i(2, vec![set(1, load(Width::U16, 0))], Control::Jump(3)),
            i(3, vec![set(2, r(1))], Control::Return(r(2))),
            i(4, vec![set(1, c(u64::MAX))], Control::Jump(3)),
        ],
    );
    let widths = ValueWidths::analyze(&p);
    assert_eq!(widths.width(Reg(0)), Width::U64);
    assert_eq!(widths.width(Reg(1)), Width::U16);
    assert_eq!(widths.width(Reg(2)), Width::U16);
}

#[test]
fn loops_grow_to_a_fixed_point_and_masks_preserve_narrow_invariants() {
    for (step, width) in [
        (binary(BinaryOp::Add, r(0), c(1)), Width::U64),
        (
            binary(BinaryOp::And, binary(BinaryOp::Add, r(0), c(1)), c(255)),
            Width::U8,
        ),
    ] {
        let p = program(
            2,
            vec![
                i(0, vec![set(0, c(0))], Control::Jump(1)),
                i(
                    1,
                    vec![set(0, step)],
                    Control::Branch {
                        condition: r(1),
                        target: 1,
                    },
                ),
                i(2, vec![], Control::Return(r(0))),
            ],
        );
        assert_eq!(ValueWidths::analyze(&p).width(Reg(0)), width);
    }
    // Entry backedges cannot overwrite the unknown initial boundary. A read
    // before the entry write must keep the register's storage at U64.
    let p = program(
        2,
        vec![
            i(
                0,
                vec![set(1, r(0)), set(0, c(0))],
                Control::Branch {
                    condition: r(1),
                    target: 0,
                },
            ),
            i(1, vec![], Control::Return(c(0))),
        ],
    );
    assert_eq!(ValueWidths::analyze(&p).width(Reg(0)), Width::U64);
    assert_eq!(ValueWidths::analyze(&p).width(Reg(1)), Width::U64);
}

#[test]
fn lazy_selects_are_bounded_without_mutating_or_removing_memory_effects() {
    let p = straight(
        3,
        vec![
            set(
                0,
                Expr::select(c(1), load(Width::U8, 0), load(Width::U16, u64::MAX)),
            ),
            set(1, Expr::select(r(2), c(0), c(255))),
        ],
    );
    let original = p.instructions().to_vec();
    let widths = ValueWidths::analyze(&p);
    assert_eq!(widths.width(Reg(0)), Width::U16);
    assert_eq!(widths.width(Reg(1)), Width::U8);
    assert_eq!(widths.width(Reg(2)), Width::U64);
    assert_eq!(p.instructions(), original);
    assert!(p.execute_with_memory(&[0; 3], 0, &[255], 1).is_ok());
}

#[test]
fn reduced_value_registers_narrow_without_zero_initialization_assumptions() {
    let p = program(
        2,
        vec![i(
            0,
            vec![set(1, load(Width::U16, 0))],
            Control::Return(r(1)),
        )],
    );
    let reduced = reduce(&p).unwrap();
    let widths = ValueWidths::analyze(reduced.program());
    let destination = reduced.program().instructions()[0].assignments[0]
        .destination
        .clone();
    let Place::Register(register) = destination else {
        panic!("load result register")
    };
    assert!(register.0 >= p.register_count());
    assert_eq!(widths.width(register), Width::U16);
}

#[test]
fn resource_failure_discards_every_previously_inferred_width() {
    let p = straight(250_001, vec![set(0, c(1))]);
    assert_eq!(ValueWidths::analyze(&p).width(Reg(0)), Width::U64);
    let mut deep = c(1);
    for _ in 0..260 {
        deep = binary(BinaryOp::Add, deep, c(0));
    }
    let p = program(
        1,
        vec![
            i(0, vec![set(0, c(1))], Control::Next),
            i(1, vec![], Control::Return(deep)),
        ],
    );
    assert_eq!(ValueWidths::analyze(&p).width(Reg(0)), Width::U64);
}

#[test]
fn generated_concrete_prefix_results_fit_every_inferred_storage_width() {
    let operations = [
        BinaryOp::Add,
        BinaryOp::Sub,
        BinaryOp::Mul,
        BinaryOp::And,
        BinaryOp::Or,
        BinaryOp::Xor,
        BinaryOp::Shl,
        BinaryOp::Shr,
        BinaryOp::Eq,
        BinaryOp::Ne,
        BinaryOp::Ult,
        BinaryOp::Ule,
        BinaryOp::UMulHigh,
    ];
    let constants = [0, 1, 7, 63, 64, 128, 255, 65535, u32::MAX as u64, u64::MAX];
    let mut random_state = 0x8172_1234_abcd_ef01u64;
    let mut random = || {
        random_state ^= random_state << 13;
        random_state ^= random_state >> 7;
        random_state ^= random_state << 17;
        random_state
    };
    let mut checked = 0;
    let mut narrow = 0;
    for _ in 0..16 {
        let mut assignments = vec![
            set(0, load(Width::U8, 0)),
            set(1, load(Width::U16, 1)),
            set(2, load(Width::U32, 3)),
            set(3, load(Width::U64, 7)),
        ];
        for register in 4..52 {
            let left = r(random() as usize % register);
            let right = if random() & 1 == 0 {
                c(constants[random() as usize % constants.len()])
            } else {
                r(random() as usize % register)
            };
            let value = if random() % 7 == 0 {
                Expr::select(r(random() as usize % register), left, right)
            } else {
                binary(
                    operations[random() as usize % operations.len()],
                    left,
                    right,
                )
            };
            assignments.push(set(register, value));
        }
        let p = straight(52, assignments.clone());
        let widths = ValueWidths::analyze(&p);
        for fill in [0, 1, 0x55, 0xaa, 0xff] {
            let mut memory = vec![fill; 16];
            for byte in &mut memory {
                if random() & 1 == 0 {
                    *byte = random() as u8;
                }
            }
            // Prefixes return each assignment result using the existing IR
            // interpreter, rather than duplicating its expression evaluator.
            for point in 1..=assignments.len() {
                let register = point - 1;
                let prefix = program(
                    52,
                    vec![i(
                        0,
                        assignments[..point].to_vec(),
                        Control::Return(r(register)),
                    )],
                );
                let execution = prefix
                    .execute_with_memory(&[u64::MAX; 52], 0, &memory, 1)
                    .unwrap();
                let width = widths.width(Reg(register));
                assert_eq!(
                    execution.value & !width.mask(),
                    0,
                    "point={point}, value={}, width={width:?}, assignments={assignments:?}",
                    execution.value,
                );
                checked += 1;
                narrow += usize::from(width != Width::U64);
            }
        }
    }
    assert_eq!(checked, 4_160);
    assert!(narrow > 1_000, "narrow concrete checks: {narrow}");
}

#[test]
fn concrete_loop_replays_fit_the_inferred_invariant_width() {
    let p = program(
        2,
        vec![
            i(0, vec![set(0, c(0))], Control::Jump(1)),
            i(
                1,
                vec![
                    set(
                        0,
                        binary(BinaryOp::And, binary(BinaryOp::Add, r(0), c(1)), c(255)),
                    ),
                    set(1, binary(BinaryOp::Sub, r(1), c(1))),
                ],
                Control::Branch {
                    condition: r(1),
                    target: 1,
                },
            ),
            i(2, vec![], Control::Return(r(0))),
        ],
    );
    let widths = ValueWidths::analyze(&p);
    assert_eq!(widths.width(Reg(0)), Width::U8);
    assert_eq!(widths.width(Reg(1)), Width::U64);
    for iterations in [1, 2, 17, 255, 256, 300, 1_024] {
        let execution = p.execute(&[u64::MAX, iterations], 2_000).unwrap();
        assert_eq!(execution.value, iterations & 255);
        for (register, value) in execution.registers.iter().enumerate() {
            assert_eq!(value & !widths.width(Reg(register)).mask(), 0);
        }
    }
}

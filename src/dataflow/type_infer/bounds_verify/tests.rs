use super::*;
use crate::dataflow::ssa::{Site, ValueId};
use crate::model::ir::{Assignment, IrInstruction, Reg};

fn c(value: u64) -> Expr {
    Expr::Const(value)
}
fn r(register: usize) -> Expr {
    Expr::Register(Reg(register))
}
fn b(operation: BinaryOp, left: Expr, right: Expr) -> Expr {
    Expr::binary(operation, left, right)
}
fn set(register: usize, value: Expr) -> Assignment {
    Assignment {
        destination: Reg(register).into(),
        value,
    }
}
fn instruction(address: u64, assignments: Vec<Assignment>, control: Control) -> IrInstruction {
    IrInstruction {
        address,
        size: 1,
        assignments,
        control,
    }
}
fn program(instructions: Vec<IrInstruction>) -> Program {
    Program::new(0, 8, instructions).unwrap()
}
fn straight(assignments: Vec<Assignment>, result: Expr) -> Program {
    program(vec![instruction(0, assignments, Control::Return(result))])
}
fn assignment(graph: &SsaFunction, instruction: u64, assignment: usize) -> ValueId {
    graph
        .point(Site {
            instruction,
            assignment: Some(assignment),
        })
        .unwrap()
        .definition
        .unwrap()
}
fn phi(graph: &SsaFunction, block: u64, register: usize) -> ValueId {
    ValueId(
        graph
            .values
            .iter()
            .position(|definition| {
                matches!(definition, Definition::Phi { block: owner, register: Reg(r), .. }
                    if *owner == block && *r == register)
            })
            .unwrap(),
    )
}
fn masked(register: usize, bits: u32) -> Expr {
    b(BinaryOp::And, r(register), c(((1u128 << bits) - 1) as u64))
}

/// The expected bit pattern is supplied by hand, independently of the bound
/// interpreter. A witness reaching its highest bit must reject one fewer bit.
fn witness(expression: Expr, bits: u8, input: &[u64], expected: u64) {
    let source = straight(vec![set(6, expression)], r(6));
    let mut registers = [0u64; 8];
    registers[..input.len()].copy_from_slice(input);
    assert_eq!(source.execute(&registers, 1).unwrap().value, expected);
    let graph = SsaFunction::build(&source).unwrap();
    let mut candidate = vec![64; graph.values.len()];
    assert!(validate(&source, &graph, &candidate).is_ok());
    let result = assignment(&graph, 0, 0);
    candidate[result.0] = bits;
    assert!(validate(&source, &graph, &candidate).is_ok(), "{bits} bits");
    assert!(u128::from(expected) < (1u128 << bits));
    if bits > 0 && u128::from(expected) >= 1u128 << (bits - 1) {
        candidate[result.0] -= 1;
        assert!(validate(&source, &graph, &candidate).is_err());
    }
}

#[test]
fn unsigned_arithmetic_high_products_and_comparisons_have_execution_witnesses() {
    use BinaryOp as B;
    for (expression, bits, input, expected) in [
        (b(B::Add, masked(0, 8), masked(1, 8)), 9, [255, 255], 510),
        (b(B::Sub, c(0), c(1)), 64, [0, 0], u64::MAX),
        (b(B::Sub, masked(0, 8), c(0)), 8, [255, 0], 255),
        (
            b(B::Mul, masked(0, 8), masked(1, 8)),
            16,
            [255, 255],
            65_025,
        ),
        (b(B::Mul, r(0), c(0)), 0, [u64::MAX, 0], 0),
        (b(B::And, r(0), c(255)), 8, [u64::MAX, 0], 255),
        (b(B::Or, masked(0, 8), masked(1, 8)), 8, [85, 170], 255),
        (b(B::Xor, masked(0, 8), masked(1, 8)), 8, [85, 170], 255),
        (
            b(B::UMulHigh, masked(0, 32), masked(1, 32)),
            0,
            [u64::MAX, u64::MAX],
            0,
        ),
        (
            b(B::UMulHigh, masked(0, 33), masked(1, 32)),
            1,
            [u64::MAX, u64::MAX],
            1,
        ),
        (
            b(B::UMulHigh, r(0), r(1)),
            64,
            [u64::MAX, u64::MAX],
            u64::MAX - 1,
        ),
        (b(B::SMulHigh, r(0), r(1)), 64, [u64::MAX, 1], u64::MAX),
        (b(B::Eq, r(0), r(1)), 1, [7, 7], 1),
        (b(B::Ne, r(0), r(1)), 1, [7, 8], 1),
        (b(B::Ult, r(0), r(1)), 1, [7, 8], 1),
        (b(B::Ule, r(0), r(1)), 1, [7, 7], 1),
    ] {
        witness(expression, bits, &input, expected);
    }
    witness(b(B::Add, c(u64::MAX), c(1)), 64, &[], 0);
    witness(b(B::Mul, c(u64::MAX), c(u64::MAX)), 64, &[], 1);
}

#[test]
fn total_division_zero_edges_signed_remainders_and_quotient_caps_are_checked() {
    use BinaryOp as B;
    witness(b(B::UDiv, c(0), c(0)), 64, &[], u64::MAX);
    witness(b(B::UDiv, c(0), r(0)), 64, &[0], u64::MAX);
    witness(b(B::UDiv, masked(0, 8), c(256)), 0, &[255], 0);
    witness(b(B::UDiv, r(0), c(1 << 63)), 1, &[u64::MAX], 1);
    witness(b(B::UDiv, r(0), c(1)), 64, &[u64::MAX], u64::MAX);
    witness(b(B::URem, masked(0, 8), c(0)), 8, &[255], 255);
    witness(b(B::SRem, masked(0, 8), c(0)), 8, &[255], 255);
    // (-2^63) % (-3) = -2. The unsigned remainder pattern exceeds the
    // dividend's numeric cap; an unconditional SRem => A would be unsound.
    witness(
        b(B::SRem, c(1 << 63), c(u64::MAX - 2)),
        64,
        &[],
        u64::MAX - 1,
    );
    witness(b(B::SDiv, c(0), c(0)), 64, &[], u64::MAX);
    witness(b(B::SDiv, c(1 << 63), c(u64::MAX)), 64, &[], 1 << 63);
}

#[test]
fn numeric_caps_require_possible_bit_hulls_before_or_xor_and_insert() {
    use BinaryOp as B;
    let q = |register| b(B::UDiv, masked(register, 8), c(127));
    // q ranges over 0,1,2 and has numeric cap 2. Raw caps 2|2 (or 2^2)
    // miss possible value 3; dividing by 3 turns that error into false zero.
    for operation in [B::Or, B::Xor] {
        witness(
            b(B::UDiv, b(operation, q(0), q(1)), c(3)),
            1,
            &[127, 254],
            1,
        );
    }
    // Clearing bits 1..8 from raw cap 2 loses possible input 1.
    witness(
        b(
            B::Insert {
                start: 1,
                width: Width::U8,
            },
            q(0),
            c(0),
        ),
        1,
        &[127],
        1,
    );
    for cap in 0..=255u128 {
        for value in 0..=cap {
            assert_eq!(value & !hull(cap), 0);
        }
    }
}

#[test]
fn literal_shift_counts_wrap_but_extract_and_insert_positions_do_not() {
    use BinaryOp as B;
    for count in [0, 1, 63, 64, 65, 127, 128, u64::MAX] {
        let shift = (count & 63) as u8;
        witness(b(B::Shl, c(1), c(count)), shift + 1, &[], 1 << shift);
        witness(
            b(B::Shr, c(u64::MAX), c(count)),
            64 - shift,
            &[],
            u64::MAX >> shift,
        );
        // Arithmetic shift of MIN gives an increasing prefix of one bits.
        witness(
            b(B::AShr, c(1 << 63), c(count)),
            64,
            &[],
            u64::MAX << (63 - shift),
        );
    }
    witness(b(B::Shl, c(0), r(0)), 0, &[65], 0);
    witness(b(B::Shl, c(1), r(0)), 64, &[63], 1 << 63);
    witness(b(B::Shr, masked(0, 8), r(1)), 8, &[255, 0], 255);
    witness(b(B::AShr, masked(0, 8), r(1)), 8, &[255, 0], 255);
    for start in [64, 65, 255] {
        witness(
            Expr::unary(
                UnaryOp::Extract {
                    start,
                    width: Width::U64,
                },
                r(0),
            ),
            0,
            &[u64::MAX],
            0,
        );
        witness(
            b(
                B::Insert {
                    start,
                    width: Width::U64,
                },
                c(255),
                r(0),
            ),
            8,
            &[u64::MAX],
            255,
        );
    }
    witness(
        b(
            B::Insert {
                start: 63,
                width: Width::U16,
            },
            c(0),
            c(1),
        ),
        64,
        &[],
        1 << 63,
    );
}

#[test]
fn signed_cast_thresholds_and_clipped_static_slices_cover_every_word_width() {
    for w in [Width::U8, Width::U16, Width::U32, Width::U64] {
        let size = width(w);
        let sign = 1u64 << (size - 1);
        witness(
            Expr::unary(UnaryOp::SignExtend(w), c(sign - 1)),
            (size - 1) as u8,
            &[],
            sign - 1,
        );
        witness(
            Expr::unary(UnaryOp::SignExtend(w), c(sign)),
            64,
            &[],
            ((1u128 << 64) - u128::from(sign)) as u64,
        );
        if size < 64 {
            // A deliberately conservative old-style bound remains accepted.
            witness(
                Expr::unary(UnaryOp::SignExtend(w), c(1 << size)),
                64,
                &[],
                0,
            );
        }
        for start in [0, 1, 7, 8, 31, 32, 60, 63, 64, 65, 127, 255] {
            let mut expected = 0u64;
            let mut expected_bits = 0;
            // Per-bit witness: all source bits inside the word are one;
            // positions outside it contribute zero, without modulo reduction.
            for bit in 0..size {
                if u32::from(start) + bit < 64 {
                    expected |= 1u64 << bit;
                    expected_bits += 1;
                }
            }
            witness(
                Expr::unary(UnaryOp::Extract { start, width: w }, r(0)),
                expected_bits,
                &[u64::MAX],
                expected,
            );
        }
    }
}

#[test]
fn store_load_select_and_control_points_consume_all_ordered_source_reads() {
    let source = straight(
        vec![
            Assignment {
                destination: Place::Memory {
                    address: Expr::select(r(0), r(1), r(2)),
                    width: Width::U8,
                },
                value: b(
                    BinaryOp::Insert {
                        start: 64,
                        width: Width::U8,
                    },
                    r(3),
                    Expr::load(r(4), Width::U8),
                ),
            },
            set(6, Expr::load(b(BinaryOp::Add, r(0), r(1)), Width::U16)),
        ],
        Expr::select(r(2), r(6), r(5)),
    );
    let graph = SsaFunction::build(&source).unwrap();
    let bits = vec![64; graph.values.len()];
    let checked = validate(&source, &graph, &bits).unwrap();
    assert_eq!(checked.values, graph.values.len());
    assert_eq!(checked.assignments, 1);
    assert_eq!(checked.expressions, 16);
    assert_eq!(
        checked.phi_inputs,
        graph
            .values
            .iter()
            .map(|definition| match definition {
                Definition::Phi { inputs, .. } => inputs.len(),
                _ => 0,
            })
            .sum::<usize>()
    );
    for point_index in 0..graph.blocks[0].points.len() {
        let mut missing = graph.clone();
        missing.blocks[0].points[point_index].reads.pop().unwrap();
        assert!(validate(&source, &missing, &bits).is_err());
    }
    let mut swapped = graph.clone();
    swapped.blocks[0].points[0].reads.swap(0, 1);
    assert!(validate(&source, &swapped, &bits).is_err());
}

#[test]
fn successful_load_bounds_follow_width_without_restricting_address_values() {
    for (w, byte_count) in [
        (Width::U8, 1),
        (Width::U16, 2),
        (Width::U32, 4),
        (Width::U64, 8),
    ] {
        let source = straight(vec![set(6, Expr::load(r(0), w))], r(6));
        let graph = SsaFunction::build(&source).unwrap();
        let mut bits = vec![64; graph.values.len()];
        assert!(validate(&source, &graph, &bits).is_ok());
        let loaded = assignment(&graph, 0, 0);
        bits[loaded.0] = (byte_count * 8) as u8;
        assert!(validate(&source, &graph, &bits).is_ok());
        let mut input = [0; 8];
        input[0] = 4096;
        let observed = source
            .execute_with_memory(&input, 4096, &vec![255; byte_count], 1)
            .unwrap()
            .value;
        assert_eq!(u128::from(observed), (1u128 << (byte_count * 8)) - 1);
        bits[loaded.0] -= 1;
        assert!(validate(&source, &graph, &bits).is_err());
    }
}

#[test]
fn virtual_initial_edge_is_not_replaced_by_a_narrow_loop_backedge() {
    let source = program(vec![
        instruction(
            0,
            vec![set(6, r(0)), set(0, c(0))],
            Control::Branch {
                condition: r(7),
                target: 0,
            },
        ),
        instruction(1, vec![], Control::Return(r(6))),
    ]);
    let graph = SsaFunction::build(&source).unwrap();
    let mut bits = vec![64; graph.values.len()];
    bits[assignment(&graph, 0, 1).0] = 0;
    assert!(validate(&source, &graph, &bits).is_ok());
    let mut input = [0; 8];
    input[0] = u64::MAX;
    assert_eq!(source.execute(&input, 2).unwrap().value, u64::MAX);
    let entry = phi(&graph, 0, 0);
    let mut narrowed = bits.clone();
    narrowed[entry.0] = 0;
    assert!(validate(&source, &graph, &narrowed).is_err());
    let mut missing = graph.clone();
    let Definition::Phi { inputs, .. } = &mut missing.values[entry.0] else {
        panic!()
    };
    assert!(inputs.iter().any(|input| input.predecessor.is_none()));
    inputs.retain(|input| input.predecessor.is_some());
    assert!(validate(&source, &missing, &bits).is_err());
    for (index, definition) in graph.values.iter().enumerate() {
        if matches!(definition, Definition::Initial { .. }) {
            let mut narrowed = bits.clone();
            narrowed[index] = 63;
            assert!(validate(&source, &graph, &narrowed).is_err());
        }
    }
}

#[test]
fn every_diamond_phi_alternative_and_its_source_predecessor_are_required() {
    let source = program(vec![
        instruction(
            0,
            vec![],
            Control::Branch {
                condition: r(7),
                target: 2,
            },
        ),
        instruction(1, vec![set(0, c(0))], Control::Jump(3)),
        instruction(2, vec![set(0, c(u64::MAX))], Control::Jump(3)),
        instruction(3, vec![set(6, r(0))], Control::Return(r(6))),
    ]);
    let graph = SsaFunction::build(&source).unwrap();
    let mut bits = vec![64; graph.values.len()];
    bits[assignment(&graph, 1, 0).0] = 0;
    assert!(validate(&source, &graph, &bits).is_ok());
    let mut input = [0; 8];
    input[7] = 1;
    assert_eq!(source.execute(&input, 3).unwrap().value, u64::MAX);
    let joined = phi(&graph, 3, 0);
    let mut narrowed = bits.clone();
    narrowed[joined.0] = 0;
    assert!(validate(&source, &graph, &narrowed).is_err());
    for duplicate in [false, true] {
        let mut bad = graph.clone();
        let Definition::Phi { inputs, .. } = &mut bad.values[joined.0] else {
            panic!()
        };
        if duplicate {
            inputs[1] = inputs[0];
        } else {
            inputs.pop();
        }
        assert!(validate(&source, &bad, &bits).is_err());
    }
}

#[test]
fn sequential_reads_cannot_borrow_the_identity_of_a_later_overwrite() {
    let source = straight(
        vec![
            set(2, c(255)),
            set(3, r(2)),
            set(2, c(0)),
            set(
                6,
                b(
                    BinaryOp::Insert {
                        start: 64,
                        width: Width::U8,
                    },
                    r(3),
                    r(2),
                ),
            ),
        ],
        r(6),
    );
    let graph = SsaFunction::build(&source).unwrap();
    let mut bits = vec![64; graph.values.len()];
    for (index, bound) in [(0, 8), (1, 8), (2, 0), (3, 8)] {
        bits[assignment(&graph, 0, index).0] = bound;
    }
    assert!(validate(&source, &graph, &bits).is_ok());
    assert_eq!(source.execute(&[0; 8], 1).unwrap().value, 255);
    let mut bad = graph.clone();
    bad.blocks[0].points[1].reads[0].value = assignment(&graph, 0, 2);
    assert!(validate(&source, &bad, &bits).is_err());
    let mut extra = graph.clone();
    let read = extra.blocks[0].points[1].reads[0];
    extra.blocks[0].points[1].reads.push(read);
    assert!(validate(&source, &extra, &bits).is_err());
}

#[test]
fn invalid_dimensions_source_depth_and_work_return_no_partial_evidence() {
    let source = straight(vec![set(6, c(0))], r(6));
    let graph = SsaFunction::build(&source).unwrap();
    let bits = vec![64; graph.values.len()];
    assert!(validate(&source, &graph, &bits).is_ok());
    assert!(validate(&source, &graph, &bits[..bits.len() - 1]).is_err());
    let mut invalid = bits.clone();
    invalid[0] = 65;
    assert!(validate(&source, &graph, &invalid).is_err());
    let mut oversized = graph.clone();
    oversized.values.resize(
        ssa::MAX_VALUES + 1,
        Definition::Initial { register: Reg(0) },
    );
    assert!(validate(&source, &oversized, &vec![64; oversized.values.len()]).is_err());
    assert!(
        validate_bounded(&source, &graph, &bits, 0)
            .unwrap_err()
            .contains("work limit")
    );
    let mut expression = c(0);
    for _ in 0..ssa::MAX_DEPTH {
        expression = Expr::unary(
            UnaryOp::Extract {
                start: 0,
                width: Width::U64,
            },
            expression,
        );
    }
    let deep = straight(vec![set(6, expression)], r(6));
    assert!(
        validate(&deep, &graph, &bits)
            .unwrap_err()
            .contains("expression size")
    );
}

use super::*;
use crate::model::ir::Assignment;

fn r(index: usize) -> Expr {
    Expr::Register(Reg(index))
}

fn c(value: u64) -> Expr {
    Expr::Const(value)
}

fn add(left: Expr, right: Expr) -> Expr {
    Expr::binary(BinaryOp::Add, left, right)
}

fn sub(left: Expr, right: Expr) -> Expr {
    Expr::binary(BinaryOp::Sub, left, right)
}

fn set(register: usize, value: Expr) -> Assignment {
    Assignment {
        destination: Reg(register).into(),
        value,
    }
}

fn store(address: Expr, width: Width, value: Expr) -> Assignment {
    Assignment {
        destination: Place::Memory { address, width },
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

fn source(registers: usize, instructions: Vec<IrInstruction>) -> Program {
    Program::new(0, registers, instructions).unwrap()
}

fn straight(registers: usize, assignments: Vec<Assignment>, result: Expr) -> Program {
    source(
        registers,
        vec![instruction(0, assignments, Control::Return(result))],
    )
}

fn candidate(program: &Program) -> StackAnalysis {
    // Exercise the actual producer result directly; the public constructor may
    // itself be gated by this checker, and corruption must happen afterwards.
    StackAnalysis::analyze_bounded(program, Reg(0)).unwrap()
}

fn fact(candidate: &mut StackAnalysis, address: u64, point: usize, register: usize) -> &mut Value {
    &mut candidate.points.get_mut(&address).unwrap()[point][register]
}

fn addressed_source() -> Program {
    straight(
        2,
        vec![
            set(1, sub(r(0), c(8))),
            store(r(1), Width::U64, Expr::load(add(r(0), c(8)), Width::U8)),
        ],
        Expr::load(r(1), Width::U16),
    )
}

#[test]
fn producer_facts_and_exact_evidence_are_accepted() {
    let program = addressed_source();
    let candidate = candidate(&program);
    let checked = validate(&program, Reg(0), &candidate).unwrap();
    assert_eq!(
        checked.evidence(),
        ValidationEvidence {
            instructions: 1,
            points: 3,
            known_values: 5,
            accesses: 3,
            edges: 0,
        }
    );
    assert_eq!(checked.accesses(), candidate.accesses());
    assert_eq!(checked.offset_before(0, 1, &r(1)).unwrap(), Some(-8));
    assert_eq!(checked.offset_before(0, 0, &r(1)).unwrap(), None);
    assert_eq!(checked.offset_before(1, 0, &r(0)).unwrap(), None);
    assert_eq!(checked.offset_before(0, 3, &r(0)).unwrap(), None);
    assert_eq!(checked.offset_before(0, 0, &r(999)).unwrap(), None);
}

#[test]
fn all_unknown_and_selective_weakening_are_accepted_with_matching_accesses() {
    let program = addressed_source();
    let original = candidate(&program);
    let mut coarse = original.clone();
    for states in coarse.points.values_mut() {
        for state in states {
            state.fill(Value::Unknown);
        }
    }
    // Stale accesses are positive claims and must be removed with their facts.
    assert!(validate(&program, Reg(0), &coarse).is_err());
    coarse.accesses.clear();
    let checked = validate(&program, Reg(0), &coarse).unwrap();
    assert_eq!(checked.evidence().known_values, 0);
    assert_eq!(checked.offset_before(0, 0, &r(0)).unwrap(), None);

    let mut coarse = original;
    for state in coarse.points.get_mut(&0).unwrap().iter_mut().skip(1) {
        state[1] = Value::Unknown;
    }
    coarse.accesses.retain(|a| a.width == Width::U8);
    let checked = validate(&program, Reg(0), &coarse).unwrap();
    assert_eq!(checked.evidence().known_values, 3);
    assert_eq!(checked.evidence().accesses, 1);
}

#[test]
fn malformed_point_and_register_dimensions_are_rejected() {
    let program = addressed_source();
    let original = candidate(&program);
    let mut cases = Vec::new();
    let mut bad = original.clone();
    bad.points.remove(&0);
    cases.push(bad);
    let mut bad = original.clone();
    bad.points.insert(1, original.points[&0].clone());
    cases.push(bad);
    let mut bad = original.clone();
    bad.points.get_mut(&0).unwrap().pop();
    cases.push(bad);
    let mut bad = original.clone();
    bad.points
        .get_mut(&0)
        .unwrap()
        .push(vec![Value::Unknown; 2]);
    cases.push(bad);
    let mut bad = original.clone();
    bad.points.get_mut(&0).unwrap()[0].pop();
    cases.push(bad);
    let mut bad = original;
    bad.points.get_mut(&0).unwrap()[0].push(Value::Unknown);
    cases.push(bad);
    for (index, bad) in cases.iter().enumerate() {
        assert!(validate(&program, Reg(0), bad).is_err(), "case {index}");
    }
}

#[test]
fn fabricated_initial_inputs_and_wrong_stack_register_are_rejected() {
    let program = straight(3, vec![], c(0));
    let original = candidate(&program);
    for claimed in [Value::Stack(0), Value::Constant(0)] {
        let mut bad = original.clone();
        *fact(&mut bad, 0, 0, 1) = claimed;
        assert!(validate(&program, Reg(0), &bad).is_err());
    }
    assert!(validate(&program, Reg(1), &original).is_err());
    assert!(validate(&program, Reg(3), &original).is_err());
}

#[test]
fn a_self_supporting_entry_loop_still_obeys_the_virtual_boundary() {
    let program = source(
        3,
        vec![
            instruction(
                0,
                vec![set(1, r(0))],
                Control::Branch {
                    condition: r(2),
                    target: 0,
                },
            ),
            instruction(1, vec![], Control::Return(c(0))),
        ],
    );
    let mut bad = candidate(&program);
    assert!(validate(&program, Reg(0), &bad).is_ok());
    // This value agrees with the real backedge and its local definition, but
    // is absent from the original entry inputs.
    *fact(&mut bad, 0, 0, 1) = Value::Stack(0);
    assert!(
        validate(&program, Reg(0), &bad)
            .unwrap_err()
            .contains("entry boundary")
    );
}

#[test]
fn an_entry_backedge_cannot_retain_a_changing_stack_pointer() {
    let program = source(
        2,
        vec![
            instruction(
                0,
                vec![set(0, sub(r(0), c(8)))],
                Control::Branch {
                    condition: r(1),
                    target: 0,
                },
            ),
            instruction(1, vec![], Control::Return(c(0))),
        ],
    );
    let mut bad = candidate(&program);
    *fact(&mut bad, 0, 0, 0) = Value::Stack(0);
    *fact(&mut bad, 0, 1, 0) = Value::Stack((-8i64) as u64);
    assert!(
        validate(&program, Reg(0), &bad)
            .unwrap_err()
            .contains("source successor")
    );
}

#[test]
fn every_source_branch_arm_constrains_a_join() {
    let program = source(
        3,
        vec![
            instruction(
                0,
                vec![],
                Control::Branch {
                    condition: r(2),
                    target: 2,
                },
            ),
            instruction(1, vec![set(1, sub(r(0), c(8)))], Control::Jump(3)),
            instruction(2, vec![set(1, sub(r(0), c(16)))], Control::Jump(3)),
            instruction(3, vec![], Control::Return(c(0))),
        ],
    );
    let mut bad = candidate(&program);
    assert_eq!(
        validate(&program, Reg(0), &bad).unwrap().evidence().edges,
        4
    );
    *fact(&mut bad, 3, 0, 1) = Value::Stack((-8i64) as u64);
    assert!(
        validate(&program, Reg(0), &bad)
            .unwrap_err()
            .contains("source successor")
    );
}

#[test]
fn duplicate_branch_destinations_remain_two_checked_edges() {
    let program = source(
        2,
        vec![
            instruction(
                0,
                vec![],
                Control::Branch {
                    condition: r(1),
                    target: 1,
                },
            ),
            instruction(1, vec![], Control::Return(c(0))),
        ],
    );
    let candidate = candidate(&program);
    assert_eq!(
        validate(&program, Reg(0), &candidate)
            .unwrap()
            .evidence()
            .edges,
        2
    );
}

#[test]
fn ordered_overwrites_and_unchanged_registers_cannot_forge_facts() {
    let program = straight(
        3,
        vec![
            set(1, sub(r(0), c(8))),
            set(1, r(2)),
            store(r(1), Width::U64, c(7)),
        ],
        c(0),
    );
    let original = candidate(&program);
    let mut bad = original.clone();
    *fact(&mut bad, 0, 2, 1) = Value::Stack((-8i64) as u64);
    assert!(
        validate(&program, Reg(0), &bad)
            .unwrap_err()
            .contains("ordered assignment")
    );
    let mut bad = original;
    *fact(&mut bad, 0, 1, 0) = Value::Stack(8);
    assert!(
        validate(&program, Reg(0), &bad)
            .unwrap_err()
            .contains("ordered assignment")
    );
}

#[test]
fn candidates_are_checked_against_the_actual_source_arithmetic() {
    let original = straight(2, vec![set(1, sub(r(0), c(8)))], c(0));
    let changed = straight(2, vec![set(1, sub(r(0), c(16)))], c(0));
    let candidate = candidate(&original);
    assert!(validate(&original, Reg(0), &candidate).is_ok());
    assert!(validate(&changed, Reg(0), &candidate).is_err());
}

#[test]
fn wrapping_constants_and_stack_offsets_keep_their_bit_patterns() {
    let program = straight(
        3,
        vec![
            set(1, c(u64::MAX)),
            set(2, add(r(0), r(1))),
            set(2, sub(r(2), r(1))),
        ],
        c(0),
    );
    let original = candidate(&program);
    let checked = validate(&program, Reg(0), &original).unwrap();
    assert_eq!(checked.offset_before(0, 2, &r(2)).unwrap(), Some(-1));
    assert_eq!(checked.offset_before(0, 3, &r(2)).unwrap(), Some(0));
    assert_eq!(
        checked.offset_before(0, 0, &add(c(1 << 63), r(0))).unwrap(),
        Some(i64::MIN)
    );
    assert_eq!(offset_before(&original, 0, 2, &r(2)), Some(-1));
    for claimed in [Value::Constant(u64::MAX), Value::Stack(1)] {
        let mut bad = original.clone();
        *fact(&mut bad, 0, 2, 2) = claimed;
        assert!(validate(&program, Reg(0), &bad).is_err());
    }
}

#[test]
fn unsupported_coefficients_and_intermediate_cancellation_remain_unknown() {
    for expression in [
        add(r(0), r(0)),
        sub(c(0), r(0)),
        sub(r(0), r(0)),
        add(sub(r(0), r(0)), r(0)),
        add(r(0), Expr::binary(BinaryOp::Mul, c(2), c(3))),
    ] {
        let program = straight(2, vec![set(1, expression.clone())], c(0));
        let mut bad = candidate(&program);
        let checked = validate(&program, Reg(0), &bad).unwrap();
        assert_eq!(checked.offset_before(0, 0, &expression).unwrap(), None);
        *fact(&mut bad, 0, 1, 1) = Value::Stack(0);
        assert!(validate(&program, Reg(0), &bad).is_err());
    }
}

#[test]
fn narrow_unary_operations_cannot_preserve_an_arbitrary_stack_value() {
    for op in [
        UnaryOp::SignExtend(Width::U8),
        UnaryOp::SignExtend(Width::U16),
        UnaryOp::SignExtend(Width::U32),
        UnaryOp::Extract {
            start: 0,
            width: Width::U8,
        },
        UnaryOp::Extract {
            start: 0,
            width: Width::U16,
        },
        UnaryOp::Extract {
            start: 0,
            width: Width::U32,
        },
        UnaryOp::Extract {
            start: 1,
            width: Width::U64,
        },
        UnaryOp::Extract {
            start: 64,
            width: Width::U64,
        },
    ] {
        let expression = Expr::unary(op, r(0));
        let program = straight(2, vec![set(1, expression.clone())], c(0));
        let mut bad = candidate(&program);
        assert_eq!(
            validate(&program, Reg(0), &bad)
                .unwrap()
                .offset_before(0, 0, &expression)
                .unwrap(),
            None
        );
        *fact(&mut bad, 0, 1, 1) = Value::Stack(0);
        assert!(validate(&program, Reg(0), &bad).is_err(), "{op:?}");
    }
}

#[test]
fn constant_width_semantics_and_full_width_identities_are_accepted() {
    for (op, input, expected) in [
        (UnaryOp::SignExtend(Width::U8), 0x80, (-128i64) as u64),
        (UnaryOp::SignExtend(Width::U16), 0x8000, (-32768i64) as u64),
        (
            UnaryOp::SignExtend(Width::U32),
            0x8000_0000,
            (-2147483648i64) as u64,
        ),
        (
            UnaryOp::Extract {
                start: 8,
                width: Width::U16,
            },
            0x112233,
            0x1122,
        ),
        (
            UnaryOp::Extract {
                start: 64,
                width: Width::U64,
            },
            u64::MAX,
            0,
        ),
        (
            UnaryOp::Extract {
                start: 255,
                width: Width::U8,
            },
            u64::MAX,
            0,
        ),
    ] {
        let program = straight(
            3,
            vec![set(1, Expr::unary(op, c(input))), set(2, add(r(0), r(1)))],
            c(0),
        );
        let original = candidate(&program);
        assert_eq!(original.points[&0][1][1], Value::Constant(expected));
        assert_eq!(
            validate(&program, Reg(0), &original)
                .unwrap()
                .offset_before(0, 2, &r(2))
                .unwrap(),
            Some(expected as i64)
        );
        let mut bad = original;
        *fact(&mut bad, 0, 1, 1) = Value::Constant(expected ^ 1);
        assert!(validate(&program, Reg(0), &bad).is_err());
    }
    for op in [
        UnaryOp::SignExtend(Width::U64),
        UnaryOp::Extract {
            start: 0,
            width: Width::U64,
        },
    ] {
        let program = straight(2, vec![set(1, Expr::unary(op, r(0)))], c(0));
        let original = candidate(&program);
        assert_eq!(
            validate(&program, Reg(0), &original)
                .unwrap()
                .offset_before(0, 1, &r(1))
                .unwrap(),
            Some(0)
        );
    }
}

#[test]
fn impure_select_conditions_and_unselected_arms_cannot_supply_affine_facts() {
    for expression in [
        Expr::select(Expr::load(c(u64::MAX), Width::U8), r(0), r(0)),
        Expr::select(c(1), r(0), Expr::load(r(0), Width::U64)),
        Expr::select(
            Expr::binary(BinaryOp::Mul, Expr::load(r(0), Width::U8), c(0)),
            r(0),
            r(0),
        ),
    ] {
        let program = straight(2, vec![set(1, expression.clone())], c(0));
        let mut bad = candidate(&program);
        assert_eq!(
            validate(&program, Reg(0), &bad)
                .unwrap()
                .offset_before(0, 0, &expression)
                .unwrap(),
            None
        );
        *fact(&mut bad, 0, 1, 1) = Value::Stack(0);
        assert!(validate(&program, Reg(0), &bad).is_err());
    }
    let program = straight(
        2,
        vec![set(1, Expr::select(r(1), r(0), add(r(0), c(0))))],
        c(0),
    );
    let candidate = candidate(&program);
    assert_eq!(
        validate(&program, Reg(0), &candidate)
            .unwrap()
            .offset_before(0, 1, &r(1))
            .unwrap(),
        Some(0)
    );
}

#[test]
fn every_access_field_and_occurrence_is_source_bound() {
    let program = addressed_source();
    let original = candidate(&program);
    let mut cases = Vec::new();
    for index in 0..original.accesses.len() {
        for field in 0..5 {
            let mut bad = original.clone();
            let access = &mut bad.accesses[index];
            match field {
                0 => access.instruction += 1,
                1 => access.assignment += 1,
                2 => access.offset ^= 1,
                3 => {
                    access.width = if access.width == Width::U64 {
                        Width::U8
                    } else {
                        Width::U64
                    }
                }
                _ => {
                    access.kind = if access.kind == AccessKind::Read {
                        AccessKind::Write
                    } else {
                        AccessKind::Read
                    }
                }
            }
            cases.push(bad);
        }
        let mut bad = original.clone();
        bad.accesses.remove(index);
        cases.push(bad);
    }
    let mut bad = original.clone();
    bad.accesses.swap(0, 2);
    cases.push(bad);
    let mut bad = original.clone();
    bad.accesses.insert(0, original.accesses[0]);
    cases.push(bad);
    for (index, bad) in cases.iter().enumerate() {
        assert!(validate(&program, Reg(0), bad).is_err(), "case {index}");
    }
}

#[test]
fn nested_address_loads_and_both_control_arms_are_retained() {
    let program = straight(
        3,
        vec![
            store(
                Expr::load(r(0), Width::U64),
                Width::U32,
                Expr::load(sub(r(0), c(4)), Width::U8),
            ),
            set(
                1,
                Expr::load(Expr::load(add(r(0), c(16)), Width::U64), Width::U64),
            ),
        ],
        Expr::select(
            Expr::load(add(r(0), c(2)), Width::U16),
            Expr::load(add(r(0), c(3)), Width::U32),
            Expr::load(add(r(0), c(4)), Width::U64),
        ),
    );
    let original = candidate(&program);
    assert_eq!(
        validate(&program, Reg(0), &original)
            .unwrap()
            .evidence()
            .accesses,
        6
    );
    for index in 0..original.accesses.len() {
        let mut bad = original.clone();
        bad.accesses.remove(index);
        assert!(validate(&program, Reg(0), &bad).is_err());
    }
}

#[test]
fn identical_lazy_arm_accesses_are_not_deduplicated() {
    let program = straight(
        2,
        vec![],
        Expr::select(
            r(1),
            Expr::load(r(0), Width::U8),
            Expr::load(r(0), Width::U8),
        ),
    );
    let mut bad = candidate(&program);
    assert_eq!(bad.accesses[0], bad.accesses[1]);
    assert!(validate(&program, Reg(0), &bad).is_ok());
    bad.accesses.pop();
    assert!(validate(&program, Reg(0), &bad).is_err());
}

#[test]
fn unreachable_instructions_cannot_add_facts_and_need_not_pass_new_expression_limits() {
    let mut deep = r(0);
    for _ in 0..MAX_EXPRESSION_DEPTH + 4 {
        deep = add(deep, c(0));
    }
    let program = source(
        2,
        vec![
            instruction(0, vec![], Control::Return(c(0))),
            instruction(1, vec![], Control::Return(deep)),
        ],
    );
    let mut bad = candidate(&program);
    assert_eq!(
        validate(&program, Reg(0), &bad)
            .unwrap()
            .evidence()
            .instructions,
        1
    );
    bad.points.insert(1, vec![vec![Value::Unknown; 2]]);
    assert!(validate(&program, Reg(0), &bad).is_err());
}

#[test]
fn reachable_depth_and_global_dense_bounds_fail_without_partial_evidence() {
    let mut deep = r(0);
    for _ in 0..MAX_EXPRESSION_DEPTH + 4 {
        deep = add(deep, c(0));
    }
    let small = straight(1, vec![], c(0));
    let candidate = candidate(&small);
    assert!(
        validate(&small, Reg(0), &candidate)
            .unwrap()
            .offset_before(0, 0, &deep)
            .is_err()
    );
    assert_eq!(offset_before(&candidate, 0, 0, &deep), None);
    // Collection must inspect addresses even though value checking treats a
    // load itself as an opaque impure node.
    let program = straight(1, vec![], Expr::load(deep, Width::U8));
    assert!(validate(&program, Reg(0), &candidate).is_err());
    let huge = straight(MAX_STATE_CELLS / 4 + 1, vec![], c(0));
    assert!(validate(&huge, Reg(0), &StackAnalysis::default()).is_err());
    assert!(term(&r(0), &[Value::Stack(0)], &mut ExpressionWork(0), 0).is_err());
    assert!(Work(0).take(1).is_err());
}

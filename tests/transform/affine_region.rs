use nirvana::affine_region;
use nirvana::{ir, structure};

use affine_region::{AffineError, MAX_EXPRESSION_DEPTH, MAX_NODES, validate};
use ir::{Assignment, BinaryOp, Control, Expr, IrInstruction, Place, Program, Reg, Width};
use std::collections::BTreeMap;
use structure::Node;

use crate::support::ir::c;
use crate::support::ir::r;
fn b(op: BinaryOp, a: Expr, z: Expr) -> Expr {
    Expr::binary(op, a, z)
}
fn set(id: usize, value: Expr) -> Assignment {
    Assignment {
        destination: Reg(id).into(),
        value,
    }
}
fn step(assignments: Vec<Assignment>) -> Node {
    Node::Step {
        address: 10,
        assignments,
    }
}
fn branch(condition: Expr, taken: Vec<Node>, not_taken: Vec<Node>) -> Node {
    Node::If {
        condition,
        taken,
        not_taken,
    }
}
fn prefix() -> Vec<Node> {
    vec![step(vec![
        set(0, c(0)),
        set(1, Expr::load(r(9), Width::U64)),
        set(2, b(BinaryOp::And, r(8), c(7))),
    ])]
}
fn guard() -> Node {
    branch(b(BinaryOp::Ult, r(0), r(2)), vec![], vec![Node::Break])
}
fn increment() -> Node {
    step(vec![
        set(1, b(BinaryOp::Add, r(1), r(0))),
        set(0, b(BinaryOp::Add, r(0), c(1))),
    ])
}
fn ordinary() -> Vec<Node> {
    vec![Node::Loop(vec![guard(), increment(), Node::Continue])]
}
fn paired() -> Node {
    Node::Loop(vec![
        guard(),
        step(vec![
            set(
                1,
                b(
                    BinaryOp::Add,
                    r(1),
                    b(BinaryOp::Add, b(BinaryOp::Mul, r(0), c(2)), c(1)),
                ),
            ),
            set(0, b(BinaryOp::Add, r(0), c(2))),
        ]),
        Node::Continue,
    ])
}
fn unrolled() -> Vec<Node> {
    vec![branch(
        b(BinaryOp::And, r(2), c(1)),
        vec![increment(), paired()],
        vec![paired()],
    )]
}
const INPUTS: [Reg; 3] = [Reg(0), Reg(1), Reg(2)];
const OBSERVED: [Reg; 2] = [Reg(0), Reg(1)];

fn ir_value(value: Expr, input: &[u64]) -> u64 {
    Program::new(
        0,
        input.len(),
        vec![IrInstruction {
            address: 0,
            size: 1,
            assignments: vec![],
            control: Control::Return(value),
        }],
    )
    .unwrap()
    .execute(input, 1)
    .unwrap()
    .value
}
fn expression(value: &Expr, registers: &BTreeMap<usize, u64>) -> u64 {
    match value {
        Expr::Const(value) => *value,
        Expr::Register(reg) => registers[&reg.0],
        Expr::Select {
            condition,
            taken,
            not_taken,
        } => expression(
            if expression(condition, registers) != 0 {
                taken
            } else {
                not_taken
            },
            registers,
        ),
        Expr::Load { .. } => panic!("pure replay excludes memory"),
        Expr::Binary(op, a, z) => ir_value(
            b(
                *op,
                c(expression(a, registers)),
                c(expression(z, registers)),
            ),
            &[],
        ),
    }
}
#[derive(Clone, Copy, Eq, PartialEq)]
enum Flow {
    Normal,
    Break,
    Continue,
}
fn execute(nodes: &[Node], registers: &mut BTreeMap<usize, u64>, fuel: &mut usize) -> Flow {
    for node in nodes {
        *fuel = fuel.checked_sub(1).expect("independent replay fuel");
        match node {
            Node::Step { assignments, .. } => {
                for assignment in assignments {
                    let Place::Register(reg) = assignment.destination else {
                        panic!("pure replay")
                    };
                    let value = expression(&assignment.value, registers);
                    registers.insert(reg.0, value);
                }
            }
            Node::If {
                condition,
                taken,
                not_taken,
            } => {
                let selected = if expression(condition, registers) != 0 {
                    taken
                } else {
                    not_taken
                };
                let flow = execute(selected, registers, fuel);
                if flow != Flow::Normal {
                    return flow;
                }
            }
            Node::Loop(body) => loop {
                if execute(body, registers, fuel) == Flow::Break {
                    break;
                }
            },
            Node::Evaluate(value) => {
                expression(value, registers);
            }
            Node::Break => return Flow::Break,
            Node::Continue => return Flow::Continue,
            _ => panic!("pure replay excludes return/nonlocal transfer"),
        }
    }
    Flow::Normal
}
fn replay(original: &[Node], candidate: &[Node], input: &[(Reg, u64)]) {
    let mut left: BTreeMap<_, _> = input.iter().map(|(reg, value)| (reg.0, *value)).collect();
    let mut right = left.clone();
    assert!(execute(original, &mut left, &mut 10000) == Flow::Normal);
    assert!(execute(candidate, &mut right, &mut 10000) == Flow::Normal);
    assert_eq!(left, right);
}

#[test]
fn arbitrary_loaded_accumulator_sum_and_parity_unroll_are_exact_under_all_finite_controls() {
    let prefix = prefix();
    let original = unrolled();
    let candidate = ordinary();
    let before = (prefix.clone(), original.clone(), candidate.clone());
    let evidence = validate(&prefix, &original, &candidate, &INPUTS, &OBSERVED, Reg(1)).unwrap();
    assert_eq!(evidence.cases, 8);
    assert_eq!(
        evidence.inputs,
        vec![(Reg(0), vec![0]), (Reg(2), (0..8).collect())]
    );
    assert_eq!(evidence.symbolic_input, Reg(1));
    assert_eq!(evidence.observed, OBSERVED);
    assert_eq!(
        evidence.maxima,
        vec![(Reg(0), 7), (Reg(1), u64::MAX), (Reg(2), 7)]
    );
    let mut seeds = vec![
        0,
        1,
        127,
        255,
        65535,
        1 << 31,
        1 << 63,
        u64::MAX - 21,
        u64::MAX - 1,
        u64::MAX,
    ];
    let mut generated = 0x8137_ace4_fa25_951du64;
    for _ in 0..32 {
        generated = generated
            .wrapping_mul(0x9e37_79b9_7f4a_7c15)
            .wrapping_add(0x1357);
        seeds.push(generated);
    }
    for limit in 0..8 {
        for &seed in &seeds {
            let input = [(Reg(0), 0), (Reg(1), seed), (Reg(2), limit)];
            replay(&original, &candidate, &input);
            let mut final_state = input.into_iter().map(|(r, v)| (r.0, v)).collect();
            execute(&candidate, &mut final_state, &mut 10000);
            assert_eq!(
                final_state[&1],
                seed.wrapping_add(limit * limit.saturating_sub(1) / 2)
            );
        }
    }
    assert_eq!((prefix, original, candidate), before);
}

fn check_expression(original: Expr, candidate: Expr) {
    let left = vec![step(vec![set(1, original.clone())])];
    let right = vec![step(vec![set(1, candidate.clone())])];
    let evidence = validate(&[], &left, &right, &[Reg(1)], &[Reg(1)], Reg(1)).unwrap();
    assert_eq!(evidence.cases, 1);
    assert!(evidence.inputs.is_empty());
    for seed in [0, 1, 7, 255, 1 << 63, u64::MAX - 1, u64::MAX] {
        assert_eq!(
            ir_value(original.clone(), &[0, seed]),
            ir_value(candidate.clone(), &[0, seed])
        );
    }
}

#[test]
fn exact_affine_wrapping_scaling_shifts_and_tested_zero_max_identities() {
    check_expression(
        b(BinaryOp::Add, b(BinaryOp::Add, r(1), c(u64::MAX)), c(2)),
        b(BinaryOp::Add, r(1), c(1)),
    );
    check_expression(
        b(BinaryOp::Sub, b(BinaryOp::Mul, c(3), r(1)), r(1)),
        b(BinaryOp::Mul, r(1), c(2)),
    );
    check_expression(
        b(BinaryOp::Mul, b(BinaryOp::Add, r(1), c(7)), c(u64::MAX)),
        b(BinaryOp::Sub, c(0), b(BinaryOp::Add, r(1), c(7))),
    );
    for count in [0, 1, 63, 64, 65, u64::MAX] {
        check_expression(
            b(BinaryOp::Shl, r(1), c(count)),
            b(
                BinaryOp::Mul,
                r(1),
                c(1u64.wrapping_shl((count & 63) as u32)),
            ),
        );
    }
    check_expression(b(BinaryOp::Shr, r(1), c(64)), r(1));
    for (op, constant, expected) in [
        (BinaryOp::And, 0, c(0)),
        (BinaryOp::And, u64::MAX, r(1)),
        (BinaryOp::Or, 0, r(1)),
        (BinaryOp::Or, u64::MAX, c(u64::MAX)),
        (BinaryOp::Xor, 0, r(1)),
        (BinaryOp::UMulHigh, 0, c(0)),
    ] {
        check_expression(b(op, r(1), c(constant)), expected.clone());
        check_expression(b(op, c(constant), r(1)), expected);
    }
    check_expression(b(BinaryOp::Sub, r(1), r(1)), c(0));
}

#[test]
fn all_thirteen_constant_only_ir_operations_match_the_independent_ir_evaluator() {
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
    for operation in operations {
        for a in [0, 1, 1 << 63, u64::MAX] {
            for z in [0, 1, 63, 64, u64::MAX] {
                let original = b(operation, c(a), c(z));
                let expected = ir_value(original.clone(), &[]);
                check_expression(original, c(expected));
            }
        }
    }
}

#[test]
fn identical_affine_comparisons_are_decidable_but_other_symbolic_control_is_rejected() {
    for (op, result) in [
        (BinaryOp::Eq, 1),
        (BinaryOp::Ne, 0),
        (BinaryOp::Ult, 0),
        (BinaryOp::Ule, 1),
    ] {
        let condition = b(
            op,
            b(BinaryOp::Add, r(1), c(3)),
            b(BinaryOp::Add, c(3), r(1)),
        );
        check_expression(condition.clone(), c(result));
        check_expression(
            Expr::select(condition, c(7), c(9)),
            c(if result == 0 { 9 } else { 7 }),
        );
    }
    for condition in [
        r(1),
        b(BinaryOp::Eq, r(1), c(0)),
        b(BinaryOp::Ult, r(1), c(9)),
    ] {
        let original = vec![branch(condition, vec![step(vec![set(1, c(7))])], vec![])];
        assert!(matches!(
            validate(&[], &original, &original, &[Reg(1)], &[Reg(1)], Reg(1)),
            Err(AffineError::Unsupported { .. })
        ));
    }
}

#[test]
fn nonlinear_multiply_symbolic_shr_and_unsupported_bit_operations_are_never_approximated() {
    for value in [
        b(BinaryOp::Mul, r(1), r(1)),
        b(BinaryOp::Shr, r(1), c(1)),
        b(BinaryOp::And, r(1), c(255)),
        b(BinaryOp::Xor, r(1), c(1)),
        b(BinaryOp::UMulHigh, r(1), c(1)),
        b(BinaryOp::Shl, c(1), r(1)),
    ] {
        let nodes = vec![step(vec![set(1, value)])];
        assert!(matches!(
            validate(&[], &nodes, &nodes, &[Reg(1)], &[Reg(1)], Reg(1)),
            Err(AffineError::Unsupported { .. })
        ));
    }
}

#[test]
fn offset_and_coefficient_mismatches_return_replayable_zero_or_one_witnesses() {
    for (left, right, expected_seed) in [
        (
            b(BinaryOp::Add, r(1), c(7)),
            b(BinaryOp::Add, r(1), c(8)),
            0,
        ),
        (
            b(BinaryOp::Add, b(BinaryOp::Mul, r(1), c(2)), c(7)),
            b(BinaryOp::Add, b(BinaryOp::Mul, r(1), c(3)), c(7)),
            1,
        ),
    ] {
        let original = vec![step(vec![set(1, left.clone())])];
        let candidate = vec![step(vec![set(1, right.clone())])];
        let error = validate(&[], &original, &candidate, &[Reg(1)], &[Reg(1)], Reg(1)).unwrap_err();
        let AffineError::Counterexample {
            inputs,
            register,
            original,
            candidate,
        } = error
        else {
            panic!("expected witness")
        };
        assert_eq!(register, Reg(1));
        assert_eq!(inputs, vec![(Reg(1), expected_seed)]);
        assert_ne!(original, candidate);
        assert_eq!(ir_value(left, &[0, expected_seed]), original);
        assert_eq!(ir_value(right, &[0, expected_seed]), candidate);
    }
    let prefix = vec![step(vec![set(0, b(BinaryOp::And, r(9), c(3)))])];
    let original = vec![step(vec![set(1, b(BinaryOp::Add, r(1), c(7)))])];
    let candidate = vec![branch(
        b(BinaryOp::Eq, r(0), c(3)),
        vec![step(vec![set(1, b(BinaryOp::Add, r(1), c(8)))])],
        original.clone(),
    )];
    let error = validate(
        &prefix,
        &original,
        &candidate,
        &[Reg(0), Reg(1)],
        &[Reg(1)],
        Reg(1),
    )
    .unwrap_err();
    let AffineError::Counterexample {
        inputs,
        original: left,
        candidate: right,
        ..
    } = error
    else {
        panic!("conditional witness")
    };
    assert_eq!(inputs, vec![(Reg(0), 3), (Reg(1), 0)]);
    let mut state: BTreeMap<_, _> = inputs.iter().map(|(r, v)| (r.0, *v)).collect();
    let mut other = state.clone();
    execute(&original, &mut state, &mut 100);
    execute(&candidate, &mut other, &mut 100);
    assert_eq!((state[&1], other[&1]), (left, right));
    assert_ne!(left, right);
}

#[test]
fn exactly_one_designated_unknown_is_required_and_sparse_labels_are_supported() {
    assert!(matches!(
        validate(&[], &[], &[], &INPUTS, &OBSERVED, Reg(1)),
        Err(AffineError::UnknownInput { .. })
    ));
    assert!(matches!(
        validate(
            &[step(vec![set(1, c(7))])],
            &[],
            &[],
            &[Reg(1)],
            &[Reg(1)],
            Reg(1)
        ),
        Err(AffineError::Malformed { .. })
    ));
    assert!(validate(&[], &[], &[], &[Reg(1)], &[Reg(1)], Reg(2)).is_err());
    let evidence = validate(
        &[],
        &[],
        &[],
        &[Reg(usize::MAX)],
        &[Reg(usize::MAX)],
        Reg(usize::MAX),
    )
    .unwrap();
    assert_eq!(evidence.symbolic_input, Reg(usize::MAX));
    assert_eq!(evidence.maxima, vec![(Reg(usize::MAX), u64::MAX)]);
    assert!(validate(&[], &[], &[], &[Reg(1), Reg(1)], &[Reg(1)], Reg(1)).is_err());
    assert!(validate(&[], &[], &[], &[Reg(1)], &[Reg(1), Reg(1)], Reg(1)).is_err());
}

#[test]
fn memory_escaping_control_and_out_of_domain_reads_or_writes_are_rejected_upfront() {
    let forbidden = vec![
        step(vec![set(1, Expr::load(c(0), Width::U64))]),
        step(vec![Assignment {
            destination: Place::Memory {
                address: c(0),
                width: Width::U64,
            },
            value: r(1),
        }]),
        Node::Return(r(1)),
        Node::Break,
        Node::Continue,
        Node::BreakOuter { levels: 1 },
        Node::ContinueOuter { levels: 1 },
        step(vec![set(
            1,
            Expr::select(c(1), r(1), Expr::load(c(0), Width::U8)),
        )]),
    ];
    for node in forbidden {
        assert!(validate(&[], &[node], &[], &[Reg(1)], &[Reg(1)], Reg(1)).is_err());
    }
    let read = vec![step(vec![set(1, b(BinaryOp::Add, r(1), r(2)))])];
    assert!(matches!(
        validate(&[], &read, &[], &[Reg(1)], &[Reg(1)], Reg(1)),
        Err(AffineError::Malformed { .. })
    ));
    let write = vec![step(vec![set(2, c(0))])];
    assert!(matches!(
        validate(&[], &write, &[], &[Reg(1)], &[Reg(1)], Reg(1)),
        Err(AffineError::Malformed { .. })
    ));
}

#[test]
fn nontermination_cartesian_and_expression_limits_never_return_evidence() {
    let endless = vec![Node::Loop(vec![Node::Continue])];
    assert!(
        validate(&[], &endless, &[], &[Reg(1)], &[Reg(1)], Reg(1))
            .unwrap_err()
            .is_resource_limit()
    );
    let prefix = vec![step(vec![
        set(0, b(BinaryOp::And, r(9), c(15))),
        set(2, b(BinaryOp::And, r(8), c(15))),
        set(3, b(BinaryOp::And, r(7), c(1))),
    ])];
    assert!(
        validate(
            &prefix,
            &[],
            &[],
            &[Reg(0), Reg(1), Reg(2), Reg(3)],
            &[],
            Reg(1)
        )
        .unwrap_err()
        .is_resource_limit()
    );
    assert!(
        validate(
            &[],
            &vec![Node::Evaluate(c(0)); MAX_NODES + 1],
            &[],
            &[Reg(1)],
            &[],
            Reg(1)
        )
        .unwrap_err()
        .is_resource_limit()
    );
    let mut value = r(1);
    for _ in 0..=MAX_EXPRESSION_DEPTH {
        value = b(BinaryOp::Add, value, c(1));
    }
    assert!(
        validate(
            &[],
            &[step(vec![set(1, value)])],
            &[],
            &[Reg(1)],
            &[Reg(1)],
            Reg(1)
        )
        .unwrap_err()
        .is_resource_limit()
    );
    assert!(
        validate(&[], &[], &[], &[Reg(1); 17], &[], Reg(1))
            .unwrap_err()
            .is_resource_limit()
    );
}

#[test]
fn maximum_bounds_include_transient_writes_and_affine_cancellation() {
    let original = vec![step(vec![
        set(2, c(900)),
        set(2, c(0)),
        set(1, b(BinaryOp::Sub, r(1), r(1))),
    ])];
    let candidate = vec![step(vec![set(1, c(0)), set(2, c(0))])];
    let evidence = validate(
        &[],
        &original,
        &candidate,
        &[Reg(1)],
        &[Reg(1), Reg(2)],
        Reg(1),
    )
    .unwrap();
    assert_eq!(evidence.maxima, vec![(Reg(1), u64::MAX), (Reg(2), 900)]);
    let prefix = vec![step(vec![
        set(0, b(BinaryOp::And, r(9), c(15))),
        set(2, b(BinaryOp::And, r(8), c(15))),
    ])];
    let evidence = validate(&prefix, &[], &[], &INPUTS, &INPUTS, Reg(1)).unwrap();
    assert_eq!(evidence.cases, 256);
}

#[test]
fn active_register_and_pending_ast_limits_are_checked_before_large_retention() {
    let prefix = vec![step(
        (0..=affine_region::MAX_REGISTERS)
            .map(|id| set(id, c(0)))
            .collect(),
    )];
    assert!(
        validate(&prefix, &[], &[], &[Reg(usize::MAX)], &[], Reg(usize::MAX))
            .unwrap_err()
            .is_resource_limit()
    );
    let wide = vec![Node::Loop(vec![Node::Evaluate(c(0)); MAX_NODES]); 2];
    assert!(
        validate(&[], &wide, &[], &[Reg(1)], &[], Reg(1))
            .unwrap_err()
            .is_resource_limit()
    );
}

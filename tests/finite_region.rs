use nirvana::finite_region::{
    FiniteError, FiniteEvidence, MAX_EXPRESSION_DEPTH, MAX_NODES, validate,
};
use nirvana::ir::{Assignment, BinaryOp, Control, Expr, IrInstruction, Place, Program, Reg, Width};
use nirvana::structure::Node;

fn r(index: usize) -> Expr {
    Expr::Register(Reg(index))
}
fn c(value: u64) -> Expr {
    Expr::Const(value)
}
fn binary(op: BinaryOp, left: Expr, right: Expr) -> Expr {
    Expr::binary(op, left, right)
}
fn add(left: Expr, right: Expr) -> Expr {
    binary(BinaryOp::Add, left, right)
}
fn set(index: usize, value: Expr) -> Assignment {
    Assignment {
        destination: Reg(index).into(),
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
fn mask(reg: usize, source: usize, value: u64) -> Assignment {
    set(reg, binary(BinaryOp::And, r(source), c(value)))
}
fn values(evidence: &FiniteEvidence, reg: usize) -> &[u64] {
    &evidence.inputs.iter().find(|(r, _)| r.0 == reg).unwrap().1
}
fn maximum(evidence: &FiniteEvidence, reg: usize) -> u64 {
    evidence.maxima.iter().find(|(r, _)| r.0 == reg).unwrap().1
}
fn prefix() -> Vec<Node> {
    vec![step(vec![set(0, c(0)), set(1, c(0)), mask(2, 9, 7)])]
}
fn increment() -> Node {
    step(vec![set(1, add(r(1), r(0))), set(0, add(r(0), c(1)))])
}
fn under_limit() -> Expr {
    binary(BinaryOp::Ult, r(0), r(2))
}
fn simple_sum() -> Vec<Node> {
    vec![Node::Loop(vec![
        branch(under_limit(), vec![], vec![Node::Break]),
        increment(),
        Node::Continue,
    ])]
}
fn unrolled_sum() -> Vec<Node> {
    (0..8)
        .map(|_| branch(under_limit(), vec![increment()], vec![]))
        .collect()
}
fn paired_sum() -> Vec<Node> {
    vec![
        branch(binary(BinaryOp::And, r(2), c(1)), vec![increment()], vec![]),
        branch(
            under_limit(),
            vec![Node::Loop(vec![
                increment(),
                increment(),
                branch(under_limit(), vec![Node::Continue], vec![Node::Break]),
            ])],
            vec![],
        ),
    ]
}
const INPUTS: [Reg; 3] = [Reg(0), Reg(1), Reg(2)];

#[test]
fn finite_domains_from_real_masked_prefix_certify_unrolled_and_parity_sums() {
    for original in [unrolled_sum(), paired_sum()] {
        let evidence = validate(&prefix(), &original, &simple_sum(), &INPUTS, &INPUTS).unwrap();
        assert_eq!(evidence.cases, 8);
        assert_eq!(values(&evidence, 0), [0]);
        assert_eq!(values(&evidence, 1), [0]);
        assert_eq!(values(&evidence, 2), (0..8).collect::<Vec<_>>());
        assert_eq!(
            (
                maximum(&evidence, 0),
                maximum(&evidence, 1),
                maximum(&evidence, 2)
            ),
            (7, 21, 7)
        );
        assert_eq!(evidence.observed, INPUTS);
    }
}

#[test]
fn concrete_bound_seventeen_and_wrong_sum_constants_are_not_certified() {
    let beyond_prefix = vec![step(vec![set(0, c(0)), set(1, c(0)), set(2, c(17))])];
    assert!(matches!(
        validate(
            &beyond_prefix,
            &unrolled_sum(),
            &simple_sum(),
            &INPUTS,
            &INPUTS
        ),
        Err(FiniteError::Counterexample { .. })
    ));
    let wrong = vec![Node::Loop(vec![
        branch(under_limit(), vec![], vec![Node::Break]),
        step(vec![set(1, add(r(1), c(7))), set(0, add(r(0), c(1)))]),
        Node::Continue,
    ])];
    assert!(matches!(
        validate(&prefix(), &unrolled_sum(), &wrong, &INPUTS, &INPUTS),
        Err(FiniteError::Counterexample {
            register: Reg(1),
            ..
        })
    ));
}

#[test]
fn noncontiguous_masks_enumerate_submasks_not_a_guessed_interval() {
    let prefix = vec![step(vec![mask(0, 9, 0b10101)])];
    let evidence = validate(&prefix, &[], &[], &[Reg(0)], &[Reg(0)]).unwrap();
    assert_eq!(values(&evidence, 0), [0, 1, 4, 5, 16, 17, 20, 21]);
    let prefix = vec![step(vec![
        set(3, c(0b1001)),
        set(0, binary(BinaryOp::And, r(9), r(3))),
    ])];
    assert_eq!(
        values(
            &validate(&prefix, &[], &[], &[Reg(0)], &[Reg(0)]).unwrap(),
            0
        ),
        [0, 1, 8, 9]
    );
    let large = vec![step(vec![mask(0, 9, 31)])];
    assert!(matches!(
        validate(&large, &[], &[], &[Reg(0)], &[Reg(0)]),
        Err(FiniteError::UnknownInput { register: Reg(0) })
    ));
}

#[test]
fn abstract_binary_cartesian_products_cover_correlated_values_without_truncation() {
    let prefix = vec![step(vec![mask(0, 9, 3), set(1, add(r(0), r(0)))])];
    let evidence = validate(&prefix, &[], &[], &[Reg(1)], &[Reg(1)]).unwrap();
    assert_eq!(values(&evidence, 1), (0..=6).collect::<Vec<_>>());
    let large = vec![step(vec![
        mask(0, 8, 15),
        mask(1, 9, 15),
        set(2, add(r(0), r(1))),
    ])];
    assert!(matches!(
        validate(&large, &[], &[], &[Reg(2)], &[Reg(2)]),
        Err(FiniteError::UnknownInput { register: Reg(2) })
    ));
    let select = vec![step(vec![set(0, Expr::select(r(9), c(7), c(11)))])];
    assert_eq!(
        values(
            &validate(&select, &[], &[], &[Reg(0)], &[Reg(0)]).unwrap(),
            0
        ),
        [7, 11]
    );
}

#[test]
fn unknown_branches_and_loops_kill_all_written_constants() {
    for control in [
        branch(
            r(9),
            vec![step(vec![set(0, c(1))])],
            vec![step(vec![set(0, c(1))])],
        ),
        Node::Loop(vec![step(vec![set(0, c(3))]), Node::Break]),
        branch(
            r(9),
            vec![Node::Loop(vec![step(vec![set(0, c(3))]), Node::Break])],
            vec![],
        ),
        branch(
            r(9),
            vec![step(vec![set(0, c(3))]), Node::Return(c(0))],
            vec![],
        ),
    ] {
        let prefix = vec![step(vec![set(0, c(1)), set(1, c(7))]), control];
        assert!(matches!(
            validate(&prefix, &[], &[], &[Reg(0)], &[Reg(0)]),
            Err(FiniteError::UnknownInput { register: Reg(0) })
        ));
        assert_eq!(
            values(
                &validate(&prefix, &[], &[], &[Reg(1)], &[Reg(1)]).unwrap(),
                1
            ),
            [7]
        );
    }
    let known = vec![
        step(vec![set(0, c(1))]),
        branch(
            c(0),
            vec![step(vec![set(0, c(9))])],
            vec![step(vec![set(0, c(3))])],
        ),
    ];
    assert_eq!(
        values(
            &validate(&known, &[], &[], &[Reg(0)], &[Reg(0)]).unwrap(),
            0
        ),
        [3]
    );
}

#[test]
fn prefix_loads_and_stores_are_allowed_only_outside_the_pure_region() {
    let prefix = vec![step(vec![
        Assignment {
            destination: Place::Memory {
                address: c(0),
                width: Width::U64,
            },
            value: r(9),
        },
        set(0, binary(BinaryOp::And, Expr::load(c(0), Width::U64), c(7))),
    ])];
    let evidence = validate(&prefix, &[], &[], &[Reg(0)], &[Reg(0)]).unwrap();
    assert_eq!(values(&evidence, 0), (0..8).collect::<Vec<_>>());
    let load = Node::Evaluate(Expr::select(c(1), c(7), Expr::load(c(0), Width::U8)));
    let store = step(vec![Assignment {
        destination: Place::Memory {
            address: c(0),
            width: Width::U8,
        },
        value: c(7),
    }]);
    for region in [vec![load], vec![branch(c(0), vec![store], vec![])]] {
        assert!(matches!(
            validate(&[], &region, &[], &[], &[]),
            Err(FiniteError::Unsupported { .. })
        ));
        assert!(matches!(
            validate(&[], &[], &region, &[], &[]),
            Err(FiniteError::Unsupported { .. })
        ));
    }
}

#[test]
fn prefix_abstract_values_cover_independent_concrete_ir_executions() {
    let assignments = vec![
        Assignment {
            destination: Place::Memory {
                address: c(0),
                width: Width::U64,
            },
            value: r(9),
        },
        set(
            0,
            binary(BinaryOp::And, Expr::load(c(0), Width::U64), c(0b10101)),
        ),
        set(1, add(r(0), c(3))),
    ];
    let evidence = validate(
        &[step(assignments.clone())],
        &[],
        &[],
        &[Reg(0), Reg(1)],
        &[Reg(0), Reg(1)],
    )
    .unwrap();
    assert_eq!(evidence.cases, 64);
    for poison in [0u64, 1, u64::MAX, 0xdead_beef_1234_5678] {
        for input in 0..256u64 {
            let mut registers = vec![poison; 10];
            registers[9] = input;
            let program = Program::new(
                0,
                10,
                vec![IrInstruction {
                    address: 0,
                    size: 1,
                    assignments: assignments.clone(),
                    control: Control::Return(r(1)),
                }],
            )
            .unwrap();
            let actual = program
                .execute_with_memory(&registers, 0, &[0x5a; 16], 1)
                .unwrap();
            assert!(values(&evidence, 0).contains(&actual.registers[0]));
            assert!(values(&evidence, 1).contains(&actual.registers[1]));
        }
    }
}

#[test]
fn all_unsigned_operations_match_the_independent_ir_for_prefix_and_region() {
    for op in [
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
    ] {
        for (left, right) in [
            (u64::MAX, 65),
            (u64::MAX, u64::MAX),
            (1 << 63, 2),
            (0, 0),
            (7, 3),
        ] {
            let expression = binary(op, r(0), r(1));
            let program = Program::new(
                0,
                2,
                vec![IrInstruction {
                    address: 0,
                    size: 1,
                    assignments: vec![],
                    control: Control::Return(expression.clone()),
                }],
            )
            .unwrap();
            let expected = program.execute(&[left, right], 1).unwrap().value;
            let prefix = vec![step(vec![set(0, c(left)), set(1, c(right))])];
            let region = validate(
                &prefix,
                &[step(vec![set(2, expression.clone())])],
                &[step(vec![set(2, c(expected))])],
                &[Reg(0), Reg(1)],
                &[Reg(2)],
            )
            .unwrap();
            assert_eq!(maximum(&region, 2), expected);
            let prefix = vec![step(vec![
                set(0, c(left)),
                set(1, c(right)),
                set(2, expression),
            ])];
            let derived = validate(&prefix, &[], &[], &[Reg(2)], &[Reg(2)]).unwrap();
            assert_eq!(values(&derived, 2), [expected]);
        }
    }
}

#[test]
fn maxima_include_unwritten_inputs_and_intermediate_writes_of_both_regions() {
    let prefix = vec![step(vec![set(0, c(0)), set(1, c(5000))])];
    let original = vec![step(vec![set(0, c(1000)), set(0, c(3))])];
    let candidate = vec![step(vec![set(0, c(2000)), set(0, c(3))])];
    let evidence = validate(&prefix, &original, &candidate, &[Reg(0), Reg(1)], &[Reg(0)]).unwrap();
    assert_eq!(maximum(&evidence, 0), 2000);
    assert_eq!(maximum(&evidence, 1), 5000);
}

#[test]
fn nested_local_break_and_continue_scope_is_executed_exactly() {
    let prefix = vec![step(vec![set(0, c(0)), set(1, c(0)), set(2, c(3))])];
    let original = vec![Node::Loop(vec![
        Node::Loop(vec![increment(), Node::Break]),
        branch(under_limit(), vec![Node::Continue], vec![Node::Break]),
    ])];
    let evidence = validate(&prefix, &original, &simple_sum(), &INPUTS, &INPUTS).unwrap();
    assert_eq!(evidence.cases, 1);
}

#[test]
fn unknown_inputs_wrong_termination_and_unbound_outputs_return_no_certificate() {
    assert!(matches!(
        validate(&[], &[], &[], &[Reg(0)], &[Reg(0)]),
        Err(FiniteError::UnknownInput { register: Reg(0) })
    ));
    let infinite = [Node::Loop(vec![])];
    assert!(
        validate(&prefix(), &simple_sum(), &infinite, &INPUTS, &INPUTS)
            .unwrap_err()
            .is_resource_limit()
    );
    assert!(
        validate(&prefix(), &infinite, &simple_sum(), &INPUTS, &INPUTS)
            .unwrap_err()
            .is_resource_limit()
    );
    assert!(matches!(
        validate(&[], &[], &[], &[], &[Reg(0)]),
        Err(FiniteError::Unsupported { .. })
    ));
}

#[test]
fn unsupported_transfers_and_raw_reads_writes_are_not_hidden_by_dead_branches() {
    for node in [
        Node::Return(c(7)),
        Node::Break,
        Node::Continue,
        Node::BreakOuter { levels: 1 },
        Node::ContinueOuter { levels: 1 },
    ] {
        assert!(matches!(
            validate(&[], &[branch(c(0), vec![node], vec![])], &[], &[], &[]),
            Err(FiniteError::Unsupported { .. })
        ));
    }
    assert!(matches!(
        validate(&[Node::Return(c(7))], &[], &[], &[], &[]),
        Err(FiniteError::Unsupported { .. })
    ));
    assert!(matches!(
        validate(&[], &[Node::Evaluate(r(9))], &[], &[], &[]),
        Err(FiniteError::Malformed { .. })
    ));
    assert!(matches!(
        validate(
            &[],
            &[branch(c(0), vec![step(vec![set(9, c(7))])], vec![])],
            &[],
            &[],
            &[]
        ),
        Err(FiniteError::Malformed { .. })
    ));
}

#[test]
fn sparse_labels_and_arbitrary_outside_values_do_not_allocate_dense_state() {
    let reg = Reg(usize::MAX - 1);
    let prefix = vec![step(vec![set(
        reg.0,
        binary(BinaryOp::And, r(usize::MAX), c(7)),
    )])];
    let region = vec![step(vec![set(reg.0, add(r(reg.0), c(0)))])];
    let evidence = validate(&prefix, &region, &[], &[reg], &[reg]).unwrap();
    assert_eq!(evidence.cases, 8);
    assert_eq!(maximum(&evidence, reg.0), 7);
    for (inputs, observed) in [(vec![reg, reg], vec![reg]), (vec![reg], vec![reg, reg])] {
        assert!(matches!(
            validate(&prefix, &[], &[], &inputs, &observed),
            Err(FiniteError::Malformed { .. })
        ));
    }
}

#[test]
fn cartesian_case_cap_and_whole_tree_depth_bounds_are_checked_before_execution() {
    let prefix = vec![step(vec![mask(0, 8, 15), mask(1, 9, 15), mask(2, 10, 1)])];
    assert_eq!(
        validate(&prefix, &[], &[], &[Reg(0), Reg(1)], &[Reg(0), Reg(1)])
            .unwrap()
            .cases,
        256
    );
    assert!(
        validate(&prefix, &[], &[], &INPUTS, &INPUTS)
            .unwrap_err()
            .is_resource_limit()
    );
    assert!(
        validate(
            &vec![Node::Evaluate(c(0)); MAX_NODES + 1],
            &[],
            &[],
            &[],
            &[]
        )
        .unwrap_err()
        .is_resource_limit()
    );
    let mut deep = c(0);
    for _ in 0..MAX_EXPRESSION_DEPTH {
        deep = add(deep, c(0));
    }
    assert!(
        validate(&[step(vec![set(0, deep)])], &[], &[], &[Reg(0)], &[Reg(0)])
            .unwrap_err()
            .is_resource_limit()
    );
}

fn raw_remainder(dividend: Expr, multiplier: u64, shift: u64, divisor: u64) -> Expr {
    let quotient = binary(
        BinaryOp::Shr,
        binary(BinaryOp::UMulHigh, c(multiplier), dividend.clone()),
        c(shift),
    );
    binary(
        BinaryOp::Sub,
        dividend,
        binary(BinaryOp::Mul, quotient, c(divisor)),
    )
}

fn remainder10(dividend: Expr) -> Expr {
    raw_remainder(dividend, 0xcccc_cccc_cccc_cccd, 3, 10)
}

#[test]
fn certified_raw_remainder_derives_numeric_interval_from_arbitrary_inputs() {
    use nirvana::finite_region::{PrefixDomain, derive_domains};

    let prefix = vec![step(vec![set(0, remainder10(r(9)))])];
    let unchanged = prefix.clone();
    let domain: Vec<_> = (0..10).collect();
    assert_eq!(
        derive_domains(&prefix, &[Reg(0)]).unwrap(),
        [(Reg(0), PrefixDomain::Finite(domain.clone()))]
    );
    let evidence = validate(&prefix, &[], &[], &[Reg(0)], &[Reg(0)]).unwrap();
    assert_eq!(evidence.cases, 10);
    assert_eq!(values(&evidence, 0), domain);
    assert_eq!(maximum(&evidence, 0), 9);
    assert_eq!(prefix, unchanged);

    // Independent executable IR replay checks interval membership and exact
    // remainder at wrap/sign/division boundaries. These samples supplement
    // the quotient certificate; they do not supply the abstract bound.
    let program = Program::new(
        0,
        10,
        vec![IrInstruction {
            address: 0,
            size: 1,
            assignments: vec![set(0, remainder10(r(9)))],
            control: Control::Return(r(0)),
        }],
    )
    .unwrap();
    let mut samples = vec![0, 1, 9, 10, 11, u64::MAX, u64::MAX - 1, 1 << 63];
    for quotient in [1, 2, 3, 0xffff, u64::MAX / 10] {
        let center = quotient * 10;
        samples.extend([center.wrapping_sub(1), center, center.wrapping_add(1)]);
    }
    for input in samples {
        let mut registers = vec![0; 10];
        registers[9] = input;
        let result = program.execute(&registers, 4).unwrap();
        assert_eq!(result.value, input % 10);
        assert!(domain.contains(&result.value));
    }
}

#[test]
fn remainder_domains_require_raw_certificates_and_fit_the_existing_set_cap() {
    use nirvana::finite_region::{PrefixDomain, derive_domains};

    let product = binary(
        BinaryOp::Mul,
        binary(
            BinaryOp::Shr,
            binary(BinaryOp::UMulHigh, c(0xcccc_cccc_cccc_cccd), r(9)),
            c(3),
        ),
        c(10),
    );
    let bad_product_mask = binary(BinaryOp::Sub, r(9), binary(BinaryOp::And, product, c(9)));
    let beyond_cap = raw_remainder(r(9), 0xf0f0_f0f0_f0f0_f0f1, 4, 17);
    assert_eq!(
        nirvana::remainder_expr::recognize(&beyond_cap)
            .unwrap()
            .maximum_remainder,
        16,
    );
    let load = Expr::load(c(0x1000), Width::U64);
    let lazy_load = Expr::select(c(1), r(9), load.clone());
    let negatives = [
        // A valid quotient for a different divisor cannot justify this %10.
        raw_remainder(r(9), 0xcccc_cccc_cccc_cccd, 4, 10),
        raw_remainder(r(9), 0xcccc_cccc_cccc_cccd, 67, 10),
        // Noncontiguous numeric bound9 is not a sufficient product mask.
        bad_product_mask,
        // A correct %17 has 17 possible values, exceeding the existing cap16.
        beyond_cap,
        remainder10(load),
        remainder10(lazy_load),
        // Separate register quotient: no substitution of dataflow facts.
        binary(BinaryOp::Sub, r(9), binary(BinaryOp::Mul, r(8), c(10))),
        // Distinct dividend syntax cannot borrow the other input's certificate.
        binary(
            BinaryOp::Sub,
            r(8),
            binary(
                BinaryOp::Mul,
                binary(
                    BinaryOp::Shr,
                    binary(BinaryOp::UMulHigh, c(0xcccc_cccc_cccc_cccd), r(9)),
                    c(3),
                ),
                c(10),
            ),
        ),
    ];
    for expression in negatives {
        let prefix = vec![step(vec![set(0, expression.clone())])];
        assert_eq!(
            derive_domains(&prefix, &[Reg(0)]).unwrap(),
            [(Reg(0), PrefixDomain::Unknown)],
            "{expression:?}"
        );
        assert!(matches!(
            validate(&prefix, &[], &[], &[Reg(0)], &[Reg(0)]),
            Err(FiniteError::UnknownInput { register: Reg(0) })
        ));
    }
}

#[test]
fn remainder_prefix_certifies_ten_case_sum_with_arbitrary_loaded_seed() {
    let prefix = vec![step(vec![
        set(9, Expr::load(c(0x1000), Width::U64)),
        set(0, c(0)),
        set(1, Expr::load(c(0x1008), Width::U64)),
        set(2, remainder10(r(9))),
    ])];
    let unchanged = prefix.clone();
    let evidence = nirvana::affine_region::validate(
        &prefix,
        &paired_sum(),
        &simple_sum(),
        &INPUTS,
        &[Reg(0), Reg(1)],
        Reg(1),
    )
    .unwrap();
    assert_eq!(evidence.cases, 10);
    assert_eq!(
        evidence.inputs,
        [(Reg(0), vec![0]), (Reg(2), (0..10).collect())]
    );
    assert_eq!(evidence.symbolic_input, Reg(1));
    assert!(evidence.maxima.contains(&(Reg(1), u64::MAX)));
    assert_eq!(prefix, unchanged);

    let wrong = vec![step(vec![set(1, add(r(1), c(1)))])];
    assert!(matches!(
        nirvana::affine_region::validate(
            &prefix,
            &paired_sum(),
            &wrong,
            &INPUTS,
            &[Reg(0), Reg(1)],
            Reg(1),
        ),
        Err(nirvana::affine_region::AffineError::Counterexample { .. })
    ));
}

#[test]
fn repeated_remainder_probes_consume_the_existing_whole_work_budget() {
    use nirvana::finite_region::derive_domains;

    let prefix: Vec<_> = (0..8)
        .map(|index| step(vec![set(index, remainder10(r(100)))]))
        .collect();
    assert!(matches!(
        derive_domains(&prefix, &[Reg(0)]),
        Err(FiniteError::Unavailable {
            resource: "whole work"
        })
    ));
}

#[test]
fn ordinary_unknown_products_do_not_spend_the_remainder_certificate_budget() {
    use nirvana::finite_region::{PrefixDomain, derive_domains};

    let mut assignments: Vec<_> = (0..4)
        .map(|index| {
            set(
                index,
                binary(
                    BinaryOp::Sub,
                    r(100 + index),
                    binary(BinaryOp::Mul, r(200 + index), c(2)),
                ),
            )
        })
        .collect();
    assignments.push(set(9, c(7)));
    let prefix = vec![step(assignments)];
    let unchanged = prefix.clone();
    assert_eq!(
        derive_domains(&prefix, &[Reg(9)]).unwrap(),
        [(Reg(9), PrefixDomain::Finite(vec![7]))]
    );
    let evidence = validate(&prefix, &[], &[], &[Reg(9)], &[Reg(9)]).unwrap();
    assert_eq!(evidence.cases, 1);
    assert_eq!(values(&evidence, 9), [7]);
    assert_eq!(prefix, unchanged);
}

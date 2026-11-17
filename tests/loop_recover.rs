// Local path wiring keeps the deliverable limited to this test and the module.
use nirvana::{ir, structure, value_role};
#[allow(dead_code)]
#[path = "../src/finite_region.rs"]
mod finite_region;
#[path = "../src/loop_recover.rs"]
mod loop_recover;

use ir::{Assignment, BinaryOp, Expr, Place, Reg, Width};
use loop_recover::recover;
use structure::Node;
use value_role::ValueRole;

fn r(id: usize) -> Expr {
    Expr::Register(Reg(id))
}
fn c(value: u64) -> Expr {
    Expr::Const(value)
}
fn b(op: BinaryOp, a: Expr, z: Expr) -> Expr {
    Expr::binary(op, a, z)
}
fn set(id: usize, value: Expr) -> Assignment {
    Assignment {
        destination: Reg(id).into(),
        value,
    }
}
fn step(address: u64, assignments: Vec<Assignment>) -> Node {
    Node::Step {
        address,
        assignments,
    }
}
fn roles() -> Vec<(Reg, ValueRole)> {
    vec![
        (Reg(0), ValueRole::Counter),
        (Reg(1), ValueRole::Accumulator),
        (Reg(2), ValueRole::Limit),
    ]
}
fn widths(width: Width) -> Vec<(Reg, Width)> {
    (0..3).map(|id| (Reg(id), width)).collect()
}
fn prefix(mask: u64, accumulator: u64) -> Vec<Node> {
    vec![step(
        100,
        vec![
            set(0, c(0)),
            set(1, c(accumulator)),
            set(2, b(BinaryOp::And, r(3), c(mask))),
        ],
    )]
}
fn guard() -> Node {
    Node::If {
        condition: b(BinaryOp::Ult, r(0), r(2)),
        taken: vec![],
        not_taken: vec![Node::Break],
    }
}
fn paired(address: u64, operator: BinaryOp) -> Node {
    Node::Loop(vec![
        guard(),
        step(
            address,
            vec![
                set(
                    1,
                    b(
                        operator,
                        r(1),
                        b(BinaryOp::Add, b(BinaryOp::Mul, r(0), c(2)), c(1)),
                    ),
                ),
                set(0, b(BinaryOp::Add, r(0), c(2))),
            ],
        ),
        Node::Continue,
    ])
}
fn unrolled(operator: BinaryOp) -> Node {
    Node::If {
        condition: b(BinaryOp::Ne, b(BinaryOp::And, r(2), c(1)), c(0)),
        taken: vec![
            step(
                10,
                vec![
                    set(1, b(BinaryOp::Add, r(1), r(0))),
                    set(0, b(BinaryOp::Add, r(0), c(1))),
                ],
            ),
            paired(20, operator),
        ],
        not_taken: vec![paired(30, operator)],
    }
}
fn input(mask: u64, accumulator: u64, operator: BinaryOp) -> Vec<Node> {
    let mut nodes = prefix(mask, accumulator);
    nodes.push(unrolled(operator));
    nodes.push(Node::Return(r(1)));
    nodes
}
fn ordinary(address: u64) -> Node {
    Node::Loop(vec![
        guard(),
        step(
            address,
            vec![
                set(1, b(BinaryOp::Add, r(1), r(0))),
                set(0, b(BinaryOp::Add, r(0), c(1))),
            ],
        ),
    ])
}

// Independent test interpreter for this pure structured subset. It uses its
// own control signals and a finite execution budget, not verifier internals.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Flow {
    Next,
    Break,
    Continue,
}
fn expression(value: &Expr, registers: &[u64]) -> u64 {
    match value {
        Expr::Const(value) => *value,
        Expr::Register(reg) => registers[reg.0],
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
        Expr::Load { .. } => panic!("test interpreter excludes memory"),
        Expr::Binary(op, a, z) => {
            let a = expression(a, registers);
            let z = expression(z, registers);
            match op {
                BinaryOp::Add => a.wrapping_add(z),
                BinaryOp::Sub => a.wrapping_sub(z),
                BinaryOp::Mul => a.wrapping_mul(z),
                BinaryOp::And => a & z,
                BinaryOp::Or => a | z,
                BinaryOp::Xor => a ^ z,
                BinaryOp::Shl => a.wrapping_shl((z & 63) as u32),
                BinaryOp::Shr => a.wrapping_shr((z & 63) as u32),
                BinaryOp::Eq => u64::from(a == z),
                BinaryOp::Ne => u64::from(a != z),
                BinaryOp::Ult => u64::from(a < z),
                BinaryOp::Ule => u64::from(a <= z),
                BinaryOp::UMulHigh => ((u128::from(a) * u128::from(z)) >> 64) as u64,
            }
        }
    }
}
fn execute(nodes: &[Node], registers: &mut [u64], budget: &mut usize) -> Flow {
    for node in nodes {
        *budget = budget.checked_sub(1).expect("test execution budget");
        match node {
            Node::Step { assignments, .. } => {
                for assignment in assignments {
                    let Place::Register(reg) = assignment.destination else {
                        panic!("pure test subset")
                    };
                    registers[reg.0] = expression(&assignment.value, registers);
                }
            }
            Node::If {
                condition,
                taken,
                not_taken,
            } => {
                let branch = if expression(condition, registers) != 0 {
                    taken
                } else {
                    not_taken
                };
                let flow = execute(branch, registers, budget);
                if flow != Flow::Next {
                    return flow;
                }
            }
            Node::Loop(body) => loop {
                if execute(body, registers, budget) == Flow::Break {
                    break;
                }
            },
            Node::Break => return Flow::Break,
            Node::Continue => return Flow::Continue,
            Node::Evaluate(value) => {
                expression(value, registers);
            }
            Node::Return(_) => break,
            _ => panic!("test interpreter excludes nonlocal control"),
        }
    }
    Flow::Next
}

#[test]
fn parity_unroll_recovers_one_ordinary_loop_and_preserves_prefix_suffix_and_input() {
    let original = input(7, 0, BinaryOp::Add);
    let before = original.clone();
    let result = recover(&original, &roles(), &widths(Width::U64)).expect("finite even/odd sum");
    assert_eq!(
        result.nodes(),
        &[original[0].clone(), ordinary(10), original[2].clone()]
    );
    assert_eq!(original, before);
    assert_eq!(result.region(), 1..2);
    assert_eq!(result.replacement(), &[ordinary(10)]);
    assert_eq!(result.evidence().cases, 8);
    for initial in [0, 1, 2, 3, 4, 5, 6, 7, 8, 15, 255, 1 << 63, u64::MAX] {
        let mut expected = vec![0xdead_beef; 4];
        expected[3] = initial;
        let mut actual = expected.clone();
        execute(&original, &mut expected, &mut 10000);
        execute(result.nodes(), &mut actual, &mut 10000);
        assert_eq!(actual, expected);
        let limit = initial & 7;
        assert_eq!(actual[0], limit);
        assert_eq!(actual[1], limit * limit.saturating_sub(1) / 2);
    }
}

#[test]
fn root_sibling_window_can_join_two_loops_without_searching_inside_them() {
    let mut original = prefix(7, 0);
    // First loop consumes pairs while a second loop handles the possible odd
    // remainder. The entire two-loop window must be checked together.
    original.extend([
        Node::Loop(vec![
            Node::If {
                condition: b(BinaryOp::Ult, b(BinaryOp::Add, r(0), c(1)), r(2)),
                taken: vec![],
                not_taken: vec![Node::Break],
            },
            step(
                88,
                vec![
                    set(
                        1,
                        b(
                            BinaryOp::Add,
                            r(1),
                            b(BinaryOp::Add, b(BinaryOp::Mul, r(0), c(2)), c(1)),
                        ),
                    ),
                    set(0, b(BinaryOp::Add, r(0), c(2))),
                ],
            ),
            Node::Continue,
        ]),
        ordinary(99),
        Node::Return(r(1)),
    ]);
    let result = recover(&original, &roles(), &widths(Width::U64)).unwrap();
    assert_eq!(
        result.nodes(),
        &[original[0].clone(), ordinary(88), original[3].clone()]
    );
    assert_eq!(result.region(), 1..3);
    assert_eq!(result.replacement(), &[ordinary(88)]);
    let nested = vec![Node::Loop(original)];
    assert!(recover(&nested, &roles(), &widths(Width::U64)).is_none());
}

#[test]
fn wrong_operation_unknown_limit_and_nontermination_never_authorize_recovery() {
    assert!(recover(&input(7, 0, BinaryOp::Xor), &roles(), &widths(Width::U64)).is_none());
    let mut unknown = input(7, 0, BinaryOp::Add);
    unknown[0] = step(100, vec![set(0, c(0)), set(1, c(0)), set(2, r(3))]);
    assert!(recover(&unknown, &roles(), &widths(Width::U64)).is_none());
    let mut nonterminating = prefix(7, 0);
    nonterminating.push(Node::If {
        condition: c(1),
        taken: vec![Node::Loop(vec![Node::Continue])],
        not_taken: vec![paired(30, BinaryOp::Add)],
    });
    assert!(recover(&nonterminating, &roles(), &widths(Width::U64)).is_none());
}

#[test]
fn memory_other_writes_returns_and_nonlocal_control_are_not_candidate_regions() {
    let forbidden = vec![
        step(9, vec![set(1, Expr::load(c(0), Width::U8))]),
        step(
            9,
            vec![Assignment {
                destination: Place::Memory {
                    address: c(0),
                    width: Width::U8,
                },
                value: r(1),
            }],
        ),
        step(9, vec![set(4, c(1))]),
        step(9, vec![set(2, c(7))]),
        Node::Return(r(1)),
        Node::BreakOuter { levels: 1 },
        Node::ContinueOuter { levels: 1 },
        Node::Loop(vec![Node::Loop(vec![Node::BreakOuter { levels: 1 }])]),
        step(
            9,
            vec![set(
                1,
                Expr::select(c(1), r(1), Expr::load(c(0), Width::U8)),
            )],
        ),
    ];
    for node in forbidden {
        let mut original = prefix(7, 0);
        original.push(Node::If {
            condition: c(1),
            taken: vec![node, paired(20, BinaryOp::Add)],
            not_taken: vec![paired(30, BinaryOp::Add)],
        });
        assert!(recover(&original, &roles(), &widths(Width::U64)).is_none());
    }
}

#[test]
fn complete_role_and_width_metadata_is_required_without_aliases_or_ambiguity() {
    let original = input(7, 0, BinaryOp::Add);
    for malformed in [
        vec![],
        vec![
            (Reg(0), ValueRole::Counter),
            (Reg(1), ValueRole::Accumulator),
        ],
        vec![
            (Reg(0), ValueRole::Counter),
            (Reg(0), ValueRole::Accumulator),
            (Reg(2), ValueRole::Limit),
        ],
        vec![
            (Reg(0), ValueRole::Counter),
            (Reg(4), ValueRole::Counter),
            (Reg(1), ValueRole::Accumulator),
            (Reg(2), ValueRole::Limit),
        ],
    ] {
        assert!(recover(&original, &malformed, &widths(Width::U64)).is_none());
    }
    let mut duplicate = widths(Width::U64);
    duplicate.push((Reg(0), Width::U64));
    assert!(recover(&original, &roles(), &duplicate).is_none());
    assert!(
        recover(
            &original,
            &roles(),
            &[(Reg(0), Width::U64), (Reg(1), Width::U64)]
        )
        .is_none()
    );
}

#[test]
fn every_original_and_candidate_maximum_must_fit_the_storage_width() {
    let original = input(7, 255, BinaryOp::Add);
    assert!(recover(&original, &roles(), &widths(Width::U8)).is_none());
    let result = recover(&original, &roles(), &widths(Width::U16)).expect("wider storage fits");
    assert!(
        result
            .evidence()
            .maxima
            .iter()
            .any(|&(reg, max)| reg == Reg(1) && max > 255)
    );
    let mut original = prefix(7, 0);
    original[0] = step(100, vec![set(0, c(256)), set(1, c(0)), set(2, c(256))]);
    original.push(unrolled(BinaryOp::Add));
    assert!(recover(&original, &roles(), &widths(Width::U8)).is_none());
}

#[test]
fn oversize_metadata_syntax_and_depth_fall_back_before_cloning() {
    let original = input(7, 0, BinaryOp::Add);
    assert!(
        recover(
            &original,
            &vec![(Reg(9), ValueRole::Address); 4097],
            &widths(Width::U64)
        )
        .is_none()
    );
    assert!(recover(&original, &roles(), &vec![(Reg(9), Width::U64); 4097]).is_none());
    let mut large = vec![Node::Evaluate(c(0)); 8193];
    large.extend(original.clone());
    assert!(recover(&large, &roles(), &widths(Width::U64)).is_none());
    let mut deep = Node::Evaluate(c(0));
    for _ in 0..66 {
        deep = Node::Loop(vec![deep]);
    }
    assert!(recover(&[deep], &roles(), &widths(Width::U64)).is_none());
}

#[test]
fn one_loop_or_a_larger_proposal_is_not_an_unroll_recovery() {
    let mut original = prefix(7, 0);
    original.push(ordinary(10));
    assert!(recover(&original, &roles(), &widths(Width::U64)).is_none());
    let mut original = prefix(0, 0);
    original.extend([Node::Loop(vec![Node::Break]), Node::Loop(vec![Node::Break])]);
    assert!(recover(&original, &roles(), &widths(Width::U64)).is_none());
}

#[test]
fn masked_load_prefix_and_faulting_memory_suffix_are_preserved_exactly() {
    let prefix = step(
        412,
        vec![
            set(0, c(0)),
            set(1, c(0)),
            set(2, b(BinaryOp::And, Expr::load(r(3), Width::U64), c(7))),
        ],
    );
    let suffix = step(
        812,
        vec![Assignment {
            destination: Place::Memory {
                address: c(u64::MAX),
                width: Width::U64,
            },
            value: r(1),
        }],
    );
    let original = vec![
        prefix.clone(),
        unrolled(BinaryOp::Add),
        suffix.clone(),
        Node::Return(r(1)),
    ];
    let before = original.clone();
    let result = recover(&original, &roles(), &widths(Width::U64)).unwrap();
    assert_eq!(
        result.nodes(),
        &[prefix, ordinary(10), suffix, Node::Return(r(1))]
    );
    assert_eq!(result.evidence().cases, 8);
    assert_eq!(original, before);
}

#[test]
fn failed_candidates_do_not_authorize_later_unchecked_regions_or_exceed_attempt_budget() {
    fn unused_loops() -> Node {
        Node::If {
            condition: c(0),
            taken: vec![paired(45, BinaryOp::Xor), paired(46, BinaryOp::Xor)],
            not_taken: vec![],
        }
    }
    let mut short = prefix(7, 0);
    short.extend([unused_loops(), unrolled(BinaryOp::Add)]);
    assert!(recover(&short, &roles(), &widths(Width::U64)).is_some());
    let mut exhausted = prefix(7, 0);
    exhausted.extend((0..17).map(|_| unused_loops()));
    exhausted.push(unrolled(BinaryOp::Add));
    assert!(recover(&exhausted, &roles(), &widths(Width::U64)).is_none());
}

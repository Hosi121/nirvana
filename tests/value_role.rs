use nirvana::ir::{Assignment, BinaryOp, Expr, Place, Reg, Width};
use nirvana::structure::Node;
use nirvana::value_role::{ValueRole, infer};
use std::collections::BTreeMap;

fn r(n: usize) -> Expr {
    Expr::Register(Reg(n))
}
fn c(n: u64) -> Expr {
    Expr::Const(n)
}
fn b(op: BinaryOp, a: Expr, z: Expr) -> Expr {
    Expr::binary(op, a, z)
}
fn set(n: usize, value: Expr) -> Assignment {
    Assignment {
        destination: Reg(n).into(),
        value,
    }
}
fn step(assignments: Vec<Assignment>) -> Node {
    Node::Step {
        address: 0,
        assignments,
    }
}
fn guard(condition: Expr) -> Node {
    Node::If {
        condition,
        taken: vec![],
        not_taken: vec![Node::Break],
    }
}
fn slots(reg: Reg) -> Option<usize> {
    (reg.0 < 4).then_some(reg.0)
}
fn counted(counter: usize, limit: usize) -> Node {
    Node::Loop(vec![
        guard(b(BinaryOp::Ult, r(counter), r(limit))),
        step(vec![set(counter, b(BinaryOp::Add, r(counter), c(1)))]),
        Node::Continue,
    ])
}

#[test]
fn sum_like_loop_uses_comparison_flags_and_keeps_invariant_limit() {
    let nodes = vec![
        step(vec![set(0, c(0)), set(1, c(0)), set(2, c(10))]),
        Node::Loop(vec![
            step(vec![set(3, b(BinaryOp::Ult, r(0), r(2)))]),
            guard(r(3)),
            step(vec![
                set(1, b(BinaryOp::Add, r(1), Expr::load(r(4), Width::U8))),
                set(0, b(BinaryOp::Add, r(0), c(1))),
            ]),
            Node::Continue,
        ]),
    ];
    assert_eq!(
        infer(&nodes, slots),
        BTreeMap::from([
            (0, ValueRole::Counter),
            (1, ValueRole::Accumulator),
            (2, ValueRole::Limit),
        ])
    );
}

#[test]
fn aliases_and_identity_copies_are_resolved_by_final_slot() {
    let nodes = vec![Node::Loop(vec![
        guard(b(BinaryOp::Ult, r(10), r(12))),
        step(vec![
            set(10, r(0)),
            set(11, b(BinaryOp::Xor, r(1), r(4))),
            set(10, b(BinaryOp::Sub, r(0), c(2))),
            set(12, r(2)),
        ]),
        Node::Continue,
    ])];
    let mapping = |reg: Reg| match reg.0 {
        0 | 10 => Some(0),
        1 | 11 => Some(1),
        2 | 12 => Some(2),
        _ => None,
    };
    assert_eq!(
        infer(&nodes, mapping),
        BTreeMap::from([
            (0, ValueRole::Counter),
            (1, ValueRole::Accumulator),
            (2, ValueRole::Limit),
        ])
    );
}

#[test]
fn post_test_and_truth_inverted_guards_find_counters_without_monotonicity_claims() {
    for condition in [
        b(BinaryOp::Ult, r(0), r(2)),
        b(BinaryOp::Eq, b(BinaryOp::Ult, r(0), r(2)), c(0)),
    ] {
        let nodes = vec![Node::Loop(vec![
            step(vec![set(0, b(BinaryOp::Add, r(0), c(u64::MAX)))]),
            Node::If {
                condition,
                taken: vec![Node::Continue],
                not_taken: vec![Node::Break],
            },
        ])];
        assert_eq!(infer(&nodes, slots).get(&0), Some(&ValueRole::Counter));
        assert_eq!(infer(&nodes, slots).get(&2), Some(&ValueRole::Limit));
    }
    let countdown = vec![Node::Loop(vec![
        step(vec![set(0, b(BinaryOp::Sub, r(0), c(1)))]),
        guard(r(0)),
    ])];
    assert_eq!(infer(&countdown, slots).get(&0), Some(&ValueRole::Counter));
}

#[test]
fn conflicting_roles_across_loops_or_address_uses_are_permanently_suppressed() {
    let mut nodes = vec![
        counted(0, 2),
        Node::Loop(vec![
            step(vec![set(0, b(BinaryOp::Add, r(0), r(4)))]),
            Node::Continue,
        ]),
        counted(0, 2),
    ];
    let roles = infer(&nodes, slots);
    assert!(!roles.contains_key(&0));
    assert_eq!(roles.get(&2), Some(&ValueRole::Limit));
    nodes = vec![counted(0, 2), Node::Evaluate(Expr::load(r(0), Width::U64))];
    assert!(!infer(&nodes, slots).contains_key(&0));
}

#[test]
fn unrelated_writes_zero_updates_and_noncontrolling_tests_do_not_create_counters() {
    for update in [c(7), b(BinaryOp::Add, r(0), c(0))] {
        let nodes = vec![Node::Loop(vec![
            guard(b(BinaryOp::Ult, r(0), r(2))),
            step(vec![set(0, update)]),
        ])];
        assert!(!infer(&nodes, slots).contains_key(&0));
        assert!(!infer(&nodes, slots).contains_key(&2));
    }
    let nodes = vec![Node::Loop(vec![
        Node::If {
            condition: b(BinaryOp::Ult, r(0), r(2)),
            taken: vec![Node::Continue],
            not_taken: vec![],
        },
        step(vec![set(0, b(BinaryOp::Add, r(0), c(1)))]),
    ])];
    assert_eq!(infer(&nodes, slots).get(&0), Some(&ValueRole::Accumulator));
    let nodes = vec![Node::Loop(vec![
        guard(b(BinaryOp::Ult, r(0), r(2))),
        step(vec![set(0, b(BinaryOp::Add, r(0), c(1))), set(0, c(99))]),
    ])];
    assert!(!infer(&nodes, slots).contains_key(&0));
}

#[test]
fn limits_must_be_invariant_including_nested_loop_writes() {
    let nodes = vec![Node::Loop(vec![
        guard(b(BinaryOp::Ult, r(0), r(2))),
        step(vec![
            set(0, b(BinaryOp::Add, r(0), c(1))),
            set(2, Expr::load(r(4), Width::U64)),
        ]),
    ])];
    assert_eq!(infer(&nodes, slots).get(&0), Some(&ValueRole::Counter));
    assert!(!infer(&nodes, slots).contains_key(&2));
    let nested = vec![Node::Loop(vec![
        guard(b(BinaryOp::Ult, r(0), r(2))),
        step(vec![set(0, b(BinaryOp::Add, r(0), c(1)))]),
        Node::Loop(vec![
            step(vec![set(2, b(BinaryOp::Add, r(2), c(1)))]),
            Node::Break,
        ]),
    ])];
    assert_ne!(infer(&nested, slots).get(&2), Some(&ValueRole::Limit));
}

#[test]
fn faulty_and_lazy_memory_only_provides_syntax_evidence_without_changing_the_tree() {
    let nodes = vec![
        Node::Evaluate(Expr::select(
            c(0),
            Expr::load(r(0), Width::U64),
            Expr::load(r(1), Width::U8),
        )),
        step(vec![Assignment {
            destination: Place::Memory {
                address: r(2),
                width: Width::U32,
            },
            value: Expr::load(c(u64::MAX), Width::U64),
        }]),
        Node::Evaluate(Expr::load(b(BinaryOp::Add, r(3), c(1)), Width::U16)),
    ];
    let before = nodes.clone();
    assert_eq!(
        infer(&nodes, slots),
        BTreeMap::from([
            (0, ValueRole::Address),
            (1, ValueRole::Address),
            (2, ValueRole::Address)
        ])
    );
    assert_eq!(nodes, before);
    assert!(infer(&nodes, |_| None).is_empty());
}

#[test]
fn bounded_failures_discard_even_prior_address_evidence() {
    let mut deep = vec![Node::Evaluate(Expr::load(r(0), Width::U8))];
    for _ in 0..130 {
        deep = vec![Node::Loop(deep)];
    }
    assert!(infer(&deep, |_| panic!("depth checked before slot callback")).is_empty());
    let mut wide = vec![Node::Evaluate(Expr::load(r(0), Width::U8))];
    wide.extend((0..33_000).map(|_| Node::Evaluate(c(0))));
    assert!(infer(&wide, |_| panic!("size checked before slot callback")).is_empty());
    let slots: Vec<_> = (0..4100)
        .map(|n| Node::Evaluate(Expr::load(r(n), Width::U8)))
        .collect();
    assert!(infer(&slots, |reg| Some(reg.0)).is_empty());
}

#[test]
fn stems_are_deterministic_role_words() {
    for (role, name) in [
        (ValueRole::Counter, "counter"),
        (ValueRole::Accumulator, "accumulator"),
        (ValueRole::Limit, "limit"),
        (ValueRole::Address, "address"),
    ] {
        assert_eq!(role.stem(), name);
    }
}

#[test]
fn long_guard_definition_chains_also_have_a_whole_result_depth_limit() {
    let mut assignments = vec![set(3, b(BinaryOp::Ult, r(0), r(2)))];
    for index in 4..145 {
        assignments.push(set(index, r(index - 1)));
    }
    let nodes = vec![
        Node::Evaluate(Expr::load(r(150), Width::U8)),
        Node::Loop(vec![
            step(assignments),
            guard(r(144)),
            step(vec![set(0, b(BinaryOp::Add, r(0), c(1)))]),
        ]),
    ];
    assert!(infer(&nodes, |reg| Some(reg.0)).is_empty());
}

#[test]
fn pointer_slot_reused_for_loop_data_conditions_or_return_gets_no_address_name() {
    let mapping = |reg: Reg| match reg.0 {
        0 | 10 => Some(0),
        2 => Some(2),
        3 => Some(3),
        _ => None,
    };
    let nodes = vec![
        Node::Evaluate(Expr::load(r(10), Width::U64)),
        Node::Loop(vec![
            step(vec![set(0, Expr::load(r(5), Width::U64))]),
            guard(b(BinaryOp::Ult, r(0), r(2))),
            step(vec![
                set(3, b(BinaryOp::Add, r(0), c(1))),
                Assignment {
                    destination: Place::Memory {
                        address: r(5),
                        width: Width::U64,
                    },
                    value: r(3),
                },
            ]),
        ]),
        Node::Evaluate(Expr::load(r(10), Width::U64)),
        Node::Return(r(0)),
    ];
    assert!(!infer(&nodes, mapping).contains_key(&0));
    for use_as_data in [
        Node::Return(r(0)),
        Node::If {
            condition: r(0),
            taken: vec![],
            not_taken: vec![],
        },
        Node::Evaluate(b(BinaryOp::Xor, r(0), c(7))),
        Node::Evaluate(Expr::select(r(0), Expr::load(r(10), Width::U8), c(0))),
        step(vec![Assignment {
            destination: Place::Memory {
                address: r(5),
                width: Width::U64,
            },
            value: r(0),
        }]),
    ] {
        assert!(
            !infer(
                &[Node::Evaluate(Expr::load(r(10), Width::U8)), use_as_data],
                mapping
            )
            .contains_key(&0)
        );
    }
}

#[test]
fn address_only_alias_copies_and_constant_updates_retain_address_evidence() {
    let nodes = vec![
        step(vec![set(0, r(4))]),
        Node::Evaluate(Expr::load(r(0), Width::U64)),
        step(vec![set(10, r(0)), set(10, b(BinaryOp::Add, r(0), c(8)))]),
        Node::Evaluate(Expr::load(b(BinaryOp::Add, r(10), c(1)), Width::U8)),
        step(vec![
            set(0, b(BinaryOp::Sub, r(10), c(4))),
            Assignment {
                destination: Place::Memory {
                    address: r(0),
                    width: Width::U16,
                },
                value: Expr::load(r(5), Width::U16),
            },
        ]),
        Node::Return(Expr::load(r(10), Width::U32)),
    ];
    let mapping = |reg: Reg| matches!(reg.0, 0 | 10).then_some(0);
    let before = nodes.clone();
    assert_eq!(
        infer(&nodes, mapping),
        BTreeMap::from([(0, ValueRole::Address)])
    );
    assert_eq!(nodes, before);
}

fn exit_tail() -> Vec<Node> {
    vec![
        step(vec![
            Assignment {
                destination: Place::Memory {
                    address: r(4),
                    width: Width::U8,
                },
                value: c(7),
            },
            set(3, r(1)),
        ]),
        Node::Evaluate(Expr::load(c(u64::MAX), Width::U8)),
        Node::Break,
    ]
}

#[test]
fn continue_guard_controls_the_loop_when_effectful_fallthrough_suffix_exits() {
    for inverted in [false, true] {
        let (taken, not_taken) = if inverted {
            (vec![], vec![Node::Continue])
        } else {
            (vec![Node::Continue], vec![])
        };
        let mut body = vec![
            step(vec![set(0, b(BinaryOp::Add, r(0), c(1)))]),
            Node::If {
                condition: b(BinaryOp::Ult, r(0), r(2)),
                taken,
                not_taken,
            },
        ];
        body.extend(exit_tail());
        let nodes = vec![Node::Loop(body)];
        let original = nodes.clone();
        let roles = infer(&nodes, slots);
        assert_eq!(roles.get(&0), Some(&ValueRole::Counter));
        assert_eq!(roles.get(&2), Some(&ValueRole::Limit));
        assert_eq!(nodes, original, "faulting suffix must remain untouched");
    }
}

#[test]
fn nested_conditionals_can_definitely_continue_or_exit_via_the_same_suffix() {
    let both_continue = Node::If {
        condition: r(5),
        taken: vec![Node::Continue],
        not_taken: vec![Node::Continue],
    };
    let mut body = vec![
        step(vec![set(0, b(BinaryOp::Sub, r(0), c(1)))]),
        Node::If {
            condition: b(BinaryOp::Eq, b(BinaryOp::Ult, r(0), r(2)), c(0)),
            taken: vec![both_continue],
            not_taken: vec![],
        },
    ];
    body.push(Node::If {
        condition: r(5),
        taken: vec![Node::Break],
        not_taken: vec![Node::Return(c(9))],
    });
    let roles = infer(&[Node::Loop(body)], slots);
    assert_eq!(roles.get(&0), Some(&ValueRole::Counter));
    assert_eq!(roles.get(&2), Some(&ValueRole::Limit));
}

#[test]
fn conditional_or_unreachable_exit_suffixes_do_not_establish_a_counter() {
    let update = step(vec![set(0, b(BinaryOp::Add, r(0), c(1)))]);
    let continue_guard = Node::If {
        condition: b(BinaryOp::Ult, r(0), r(2)),
        taken: vec![Node::Continue],
        not_taken: vec![],
    };
    for suffix in [
        vec![update.clone()],
        vec![Node::If {
            condition: r(5),
            taken: vec![Node::Break],
            not_taken: vec![Node::Continue],
        }],
        vec![Node::Continue, Node::Break],
        vec![Node::Loop(vec![Node::Break]), Node::Break],
        vec![Node::ContinueOuter { levels: 1 }, Node::Break],
    ] {
        let mut body = vec![update.clone(), continue_guard.clone()];
        body.extend(suffix);
        let roles = infer(&[Node::Loop(body)], slots);
        assert_ne!(roles.get(&0), Some(&ValueRole::Counter));
        assert!(!roles.contains_key(&2));
    }
    let body = vec![update, Node::Continue, guard(b(BinaryOp::Ult, r(0), r(2)))];
    assert_eq!(
        infer(&[Node::Loop(body)], slots).get(&0),
        Some(&ValueRole::Accumulator)
    );
}

#[test]
fn both_continuing_arms_and_inner_or_outer_transfers_are_not_current_loop_exits() {
    for taken in [
        vec![Node::Continue],
        vec![Node::Loop(vec![Node::Continue])],
        vec![Node::Loop(vec![Node::Break]), Node::Continue],
        vec![Node::BreakOuter { levels: 1 }],
        vec![Node::ContinueOuter { levels: 1 }],
    ] {
        let both_continue = matches!(taken.as_slice(), [Node::Continue]);
        let body = vec![
            step(vec![set(0, b(BinaryOp::Add, r(0), c(1)))]),
            Node::If {
                condition: b(BinaryOp::Ult, r(0), r(2)),
                taken,
                not_taken: if both_continue {
                    vec![Node::Continue]
                } else {
                    vec![]
                },
            },
            Node::Break,
        ];
        let roles = infer(&[Node::Loop(body)], slots);
        assert_ne!(roles.get(&0), Some(&ValueRole::Counter));
        assert!(!roles.contains_key(&2));
    }
    let nodes = vec![Node::Loop(vec![
        step(vec![set(0, b(BinaryOp::Add, r(0), c(1)))]),
        Node::Loop(vec![guard(b(BinaryOp::Ult, r(0), r(2))), Node::Continue]),
    ])];
    assert_ne!(infer(&nodes, slots).get(&0), Some(&ValueRole::Counter));
}

#[test]
fn common_break_suffix_factoring_keeps_inner_continuation_guard_evidence() {
    let mut taken = vec![
        Node::If {
            condition: b(BinaryOp::Ult, r(0), r(2)),
            taken: vec![Node::Continue],
            not_taken: vec![],
        },
        step(vec![Assignment {
            destination: Place::Memory {
                address: r(4),
                width: Width::U8,
            },
            value: c(7),
        }]),
    ];
    let mut not_taken = vec![Node::Evaluate(Expr::load(c(u64::MAX), Width::U8))];
    let update = step(vec![set(0, b(BinaryOp::Add, r(0), c(1)))]);
    let factored = vec![Node::Loop(vec![
        update.clone(),
        Node::If {
            condition: r(5),
            taken: taken.clone(),
            not_taken: not_taken.clone(),
        },
        Node::Break,
    ])];
    taken.push(Node::Break);
    not_taken.push(Node::Break);
    let original = vec![Node::Loop(vec![
        update,
        Node::If {
            condition: r(5),
            taken,
            not_taken,
        },
    ])];
    let expected = BTreeMap::from([(0, ValueRole::Counter), (2, ValueRole::Limit)]);
    assert_eq!(infer(&original, slots), expected);
    assert_eq!(infer(&factored, slots), expected);
}

#[test]
fn explicit_exit_guard_still_controls_multi_exit_loop_header_and_its_inverse() {
    for inverted in [false, true] {
        let compare = b(BinaryOp::Ult, r(0), r(2));
        let (condition, taken, not_taken) = if inverted {
            (b(BinaryOp::Eq, compare, c(0)), vec![], vec![Node::Break])
        } else {
            (compare, vec![Node::Break], vec![])
        };
        let nodes = vec![Node::Loop(vec![
            Node::If {
                condition,
                taken,
                not_taken,
            },
            Node::If {
                condition: r(3),
                taken: vec![Node::Break],
                not_taken: vec![],
            },
            step(vec![set(0, b(BinaryOp::Add, r(0), c(1)))]),
            Node::Continue,
        ])];
        let roles = infer(&nodes, slots);
        assert_eq!(roles.get(&0), Some(&ValueRole::Counter));
        assert_eq!(roles.get(&2), Some(&ValueRole::Limit));
    }
}

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
            (2, ValueRole::Address),
            (3, ValueRole::Address)
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

#[test]
fn constant_byte_offsets_and_wrapping_chains_name_only_the_single_address_base() {
    for width in [Width::U8, Width::U16, Width::U32, Width::U64] {
        for offset in [0, 1, 8, 1 << 63, u64::MAX] {
            let nodes = vec![
                Node::Evaluate(Expr::load(b(BinaryOp::Add, r(0), c(offset)), width)),
                Node::Return(Expr::load(
                    b(BinaryOp::Sub, b(BinaryOp::Add, c(3), r(10)), c(offset)),
                    width,
                )),
                step(vec![Assignment {
                    destination: Place::Memory {
                        address: b(BinaryOp::Sub, r(1), c(offset)),
                        width,
                    },
                    value: Expr::load(b(BinaryOp::Add, c(offset), r(0)), width),
                }]),
            ];
            let before = nodes.clone();
            let mapping = |reg: Reg| match reg.0 {
                0 | 10 => Some(0),
                1 => Some(1),
                _ => None,
            };
            assert_eq!(
                infer(&nodes, mapping),
                BTreeMap::from([(0, ValueRole::Address), (1, ValueRole::Address),])
            );
            assert_eq!(nodes, before);
        }
    }
}

#[test]
fn variable_indices_scales_reversed_subtractions_and_selected_bases_do_not_name_operands() {
    for address in [
        b(BinaryOp::Add, r(0), r(1)),
        b(BinaryOp::Add, r(0), b(BinaryOp::Mul, r(1), c(8))),
        b(BinaryOp::Shl, r(0), c(3)),
        b(BinaryOp::Sub, c(8), r(0)),
        b(BinaryOp::Xor, r(0), c(7)),
        Expr::select(c(1), b(BinaryOp::Add, r(0), c(8)), r(1)),
    ] {
        assert!(infer(&[Node::Evaluate(Expr::load(address, Width::U64))], slots).is_empty());
    }
    let aliases = [Node::Evaluate(Expr::load(
        b(BinaryOp::Add, r(0), r(10)),
        Width::U8,
    ))];
    assert!(
        infer(&aliases, |_| Some(0)).is_empty(),
        "two register operands stay ambiguous even when aliased"
    );
}

#[test]
fn offset_address_candidates_keep_existing_data_use_and_role_conflict_suppression() {
    let mapping = |reg: Reg| matches!(reg.0, 0 | 10).then_some(0);
    let load = Node::Evaluate(Expr::load(b(BinaryOp::Sub, r(10), c(8)), Width::U64));
    for data_use in [
        Node::Return(r(0)),
        Node::If {
            condition: r(0),
            taken: vec![],
            not_taken: vec![],
        },
        Node::Evaluate(b(BinaryOp::Xor, r(0), c(3))),
        step(vec![set(2, b(BinaryOp::Add, r(0), c(4)))]),
        step(vec![Assignment {
            destination: Place::Memory {
                address: r(4),
                width: Width::U64,
            },
            value: r(0),
        }]),
    ] {
        assert!(infer(&[load.clone(), data_use], mapping).is_empty());
    }
    assert_eq!(
        infer(
            &[load, step(vec![set(10, b(BinaryOp::Add, r(0), c(8)))]),],
            mapping
        ),
        BTreeMap::from([(0, ValueRole::Address)])
    );
    let conflict = [
        counted(0, 2),
        Node::Evaluate(Expr::load(b(BinaryOp::Add, r(0), c(8)), Width::U64)),
    ];
    assert!(!infer(&conflict, slots).contains_key(&0));
}

#[allow(dead_code)]
#[path = "support/native.rs"]
mod native;

#[test]
fn compiled_sum_o0_names_the_constant_offset_output_base_without_changing_ir() {
    let scratch = native::Scratch::new();
    let object = scratch.0.join("sum-O0.o");
    native::object(
        &native::fixture_root().join("cases/sum.c"),
        &object,
        "-O0",
        "fixture",
    );
    let lifted = nirvana::frontend::lift_elf(&std::fs::read(object).unwrap(), "fixture").unwrap();
    let before = lifted.program.instructions().to_vec();
    let output = nirvana::readable::emit_readable_c_with_options(
        &lifted.program,
        nirvana::readable::ReadableOptions {
            stack_register: Some(Reg(nirvana::x86::RSP)),
            recover_objects: true,
            coalesce_locals: true,
            compact_memory: true,
        },
    )
    .unwrap();
    assert!(
        output
            .locals
            .iter()
            .any(|local| local.role == Some(ValueRole::Address)
                && output
                    .code
                    .contains(&format!("write64({} + 16,", local.name))
                && output
                    .code
                    .contains(&format!("write64({} + 24,", local.name))),
        "{}",
        output.code
    );
    for role in [ValueRole::Counter, ValueRole::Accumulator, ValueRole::Limit] {
        assert!(output.locals.iter().any(|local| local.role == Some(role)));
    }
    assert_eq!(lifted.program.instructions(), before);
}

fn copyback_loop(intervening: Vec<Node>, after: Vec<Node>, condition: Expr) -> Vec<Node> {
    let mut body = vec![step(vec![set(4, b(BinaryOp::Add, r(0), c(1)))])];
    body.extend(intervening);
    body.push(step(vec![set(0, r(4))]));
    body.extend(after);
    body.push(Node::If {
        condition,
        taken: vec![Node::Continue],
        not_taken: vec![Node::Break],
    });
    vec![Node::Loop(body)]
}

#[test]
fn affine_producer_copyback_names_the_current_counter_and_invariant_limit() {
    let nodes = copyback_loop(
        vec![step(vec![set(
            1,
            b(BinaryOp::Xor, b(BinaryOp::Mul, r(1), c(33)), r(0)),
        )])],
        vec![],
        b(BinaryOp::Ne, r(2), r(4)),
    );
    let before = nodes.clone();
    let inferred = infer(&nodes, |reg| Some(reg.0));
    assert_eq!(inferred.get(&0), Some(&ValueRole::Counter));
    assert_eq!(inferred.get(&1), Some(&ValueRole::Accumulator));
    assert_eq!(inferred.get(&2), Some(&ValueRole::Limit));
    assert!(
        !inferred.contains_key(&4),
        "next-value temporary is not a self-updated counter"
    );
    assert_eq!(nodes, before);
    let aliased = |reg: Reg| match reg.0 {
        0 | 10 => Some(0),
        4 | 14 => Some(4),
        2 => Some(2),
        _ => None,
    };
    let nodes = vec![Node::Loop(vec![
        step(vec![
            set(14, b(BinaryOp::Sub, r(10), c(u64::MAX))),
            set(0, r(4)),
        ]),
        Node::If {
            condition: b(BinaryOp::Ne, r(2), r(14)),
            taken: vec![Node::Continue],
            not_taken: vec![Node::Break],
        },
    ])];
    assert_eq!(
        infer(&nodes, aliased),
        BTreeMap::from([(0, ValueRole::Counter), (2, ValueRole::Limit)])
    );
}

#[test]
fn copyback_evidence_does_not_cross_overwrites_branches_inner_loops_or_other_writes() {
    let condition = b(BinaryOp::Ne, r(2), r(4));
    for barrier in [
        step(vec![set(0, b(BinaryOp::Add, r(0), c(2)))]),
        step(vec![set(4, c(9))]),
        Node::If {
            condition: r(7),
            taken: vec![],
            not_taken: vec![],
        },
        Node::Loop(vec![Node::Break]),
    ] {
        assert_ne!(
            infer(
                &copyback_loop(vec![barrier], vec![], condition.clone()),
                |reg| Some(reg.0)
            )
            .get(&0),
            Some(&ValueRole::Counter)
        );
    }
    for later in [
        step(vec![set(0, c(7))]),
        step(vec![set(4, c(7))]),
        Node::If {
            condition: r(7),
            taken: vec![step(vec![set(0, b(BinaryOp::Add, r(0), c(1)))])],
            not_taken: vec![],
        },
        Node::Loop(vec![
            step(vec![set(0, b(BinaryOp::Add, r(0), c(1)))]),
            Node::Break,
        ]),
    ] {
        assert_ne!(
            infer(
                &copyback_loop(vec![], vec![later], condition.clone()),
                |reg| Some(reg.0)
            )
            .get(&0),
            Some(&ValueRole::Counter)
        );
    }
    let nodes = vec![Node::Loop(vec![
        Node::If {
            condition: r(7),
            taken: vec![step(vec![set(4, b(BinaryOp::Add, r(0), c(1)))])],
            not_taken: vec![],
        },
        step(vec![set(0, r(4))]),
        Node::If {
            condition,
            taken: vec![Node::Continue],
            not_taken: vec![Node::Break],
        },
    ])];
    assert_ne!(
        infer(&nodes, |reg| Some(reg.0)).get(&0),
        Some(&ValueRole::Counter)
    );
}

#[test]
fn stale_or_noncontrolling_copyback_guards_and_identity_comparisons_do_not_name_counters() {
    for (after, condition) in [
        (
            vec![step(vec![set(4, b(BinaryOp::Add, r(4), c(1)))])],
            b(BinaryOp::Ne, r(2), r(4)),
        ),
        (
            vec![step(vec![set(0, b(BinaryOp::Add, r(0), c(1)))])],
            b(BinaryOp::Ne, r(2), r(4)),
        ),
        (vec![], b(BinaryOp::Ne, r(0), r(4))),
    ] {
        assert_ne!(
            infer(&copyback_loop(vec![], after, condition), |reg| Some(reg.0)).get(&0),
            Some(&ValueRole::Counter)
        );
    }
    let nodes = vec![Node::Loop(vec![
        step(vec![set(4, b(BinaryOp::Add, r(0), c(1))), set(0, r(4))]),
        Node::If {
            condition: b(BinaryOp::Ne, r(2), r(4)),
            taken: vec![Node::Continue],
            not_taken: vec![],
        },
        Node::Continue,
    ])];
    assert_ne!(
        infer(&nodes, |reg| Some(reg.0)).get(&0),
        Some(&ValueRole::Counter)
    );
    let unreachable = vec![Node::Loop(vec![
        Node::Continue,
        step(vec![set(4, b(BinaryOp::Add, r(0), c(1))), set(0, r(4))]),
        Node::If {
            condition: b(BinaryOp::Ne, r(2), r(4)),
            taken: vec![Node::Continue],
            not_taken: vec![Node::Break],
        },
    ])];
    assert_ne!(
        infer(&unreachable, |reg| Some(reg.0)).get(&0),
        Some(&ValueRole::Counter)
    );
    let arbitrary = vec![Node::Loop(vec![
        step(vec![set(4, b(BinaryOp::Mul, r(0), c(3))), set(0, r(4))]),
        Node::If {
            condition: b(BinaryOp::Ne, r(2), r(4)),
            taken: vec![Node::Continue],
            not_taken: vec![Node::Break],
        },
    ])];
    assert_ne!(
        infer(&arbitrary, |reg| Some(reg.0)).get(&0),
        Some(&ValueRole::Counter)
    );
}

#[test]
fn compiled_branch_lifetimes_o2_names_copyback_counter_and_bound_without_changing_ir() {
    let scratch = native::Scratch::new();
    let object = scratch.0.join("branch-lifetimes-O2.o");
    native::object(
        &native::fixture_root().join("recovery/branch-lifetimes.c"),
        &object,
        "-O2",
        "fixture",
    );
    let lifted = nirvana::frontend::lift_elf(&std::fs::read(object).unwrap(), "fixture").unwrap();
    let before = lifted.program.instructions().to_vec();
    let output = nirvana::readable::emit_readable_c_with_options(
        &lifted.program,
        nirvana::readable::ReadableOptions {
            stack_register: Some(Reg(nirvana::x86::RSP)),
            recover_objects: true,
            coalesce_locals: true,
            compact_memory: true,
        },
    )
    .unwrap();
    for role in [ValueRole::Counter, ValueRole::Limit, ValueRole::Accumulator] {
        assert!(
            output.locals.iter().any(|local| local.role == Some(role)),
            "missing {role:?}: {}",
            output.code
        );
    }
    assert_eq!(lifted.program.instructions(), before);
}

fn captured_flag_loop(assignments: Vec<Assignment>, condition: Expr) -> Vec<Node> {
    vec![Node::Loop(vec![
        step(assignments),
        Node::If {
            condition,
            taken: vec![Node::Continue],
            not_taken: vec![Node::Break],
        },
    ])]
}

#[test]
fn captured_identity_flags_stay_noncontrolling_after_source_or_alias_overwrites() {
    use nirvana::ir::{Control, IrInstruction, Program, RunStatus};
    let mapping = |reg: Reg| {
        Some(match reg.0 {
            10 => 0,
            14 => 4,
            other => other,
        })
    };
    for overwritten in [
        set(4, c(9)),
        set(14, c(9)),
        set(0, b(BinaryOp::Add, r(0), c(1))),
        set(10, b(BinaryOp::Add, r(0), c(1))),
    ] {
        for chain in 0..=2 {
            let mut assignments = vec![
                set(4, b(BinaryOp::Add, r(0), c(1))),
                set(0, r(4)),
                set(5, b(BinaryOp::Ne, r(4), r(0))),
            ];
            for index in 0..chain {
                assignments.push(set(6 + index, r(5 + index)));
            }
            assignments.push(overwritten.clone());
            let condition = r(5 + chain);
            let nodes = captured_flag_loop(assignments.clone(), condition.clone());
            let before = nodes.clone();
            let roles = infer(&nodes, mapping);
            assert_ne!(roles.get(&0), Some(&ValueRole::Counter));
            assert_ne!(roles.get(&2), Some(&ValueRole::Limit));
            assert_eq!(nodes, before);
            // Independent executable evidence: the captured comparison is
            // false before any clobber, so the apparent backedge is never used.
            let program = Program::new(
                0,
                15,
                vec![
                    IrInstruction {
                        address: 0,
                        size: 1,
                        assignments,
                        control: Control::Branch {
                            condition: condition.clone(),
                            target: 0,
                        },
                    },
                    IrInstruction {
                        address: 1,
                        size: 1,
                        assignments: vec![],
                        control: Control::Return(condition),
                    },
                ],
            )
            .unwrap();
            for value in [0, 1, 9, u64::MAX] {
                let mut input = vec![0xdead_beef; 15];
                input[0] = value;
                let report = program.run_with_memory(&input, 0, &[], 3).unwrap();
                assert_eq!(report.status, RunStatus::Returned(0));
                assert_eq!(report.state.trace, [0, 1]);
            }
        }
    }
}

#[test]
fn captured_counter_flags_do_not_create_counter_or_limit_after_copyback() {
    for chain in [false, true] {
        let mut assignments = vec![set(5, b(BinaryOp::Ult, r(0), r(2)))];
        if chain {
            assignments.push(set(6, r(5)));
        }
        assignments.extend([set(4, b(BinaryOp::Add, r(0), c(1))), set(0, r(4))]);
        let roles = infer(
            &captured_flag_loop(assignments, r(if chain { 6 } else { 5 })),
            |reg| Some(reg.0),
        );
        assert_ne!(roles.get(&0), Some(&ValueRole::Counter));
        assert_ne!(roles.get(&2), Some(&ValueRole::Limit));
    }
}

#[test]
fn invalidation_visits_binary_select_and_load_address_dependencies() {
    for dependent in [
        r(4),
        b(BinaryOp::Add, c(7), r(4)),
        Expr::select(r(4), r(0), c(0)),
        Expr::select(c(1), r(0), r(4)), // conservative even in a lazy arm
        Expr::load(b(BinaryOp::Add, r(4), c(0x1000)), Width::U8),
        Expr::load(Expr::load(r(4), Width::U64), Width::U8),
    ] {
        let nodes = captured_flag_loop(
            vec![
                set(4, b(BinaryOp::Add, r(0), c(1))),
                set(0, r(4)),
                set(5, b(BinaryOp::Ne, dependent, r(0))),
                set(14, c(9)),
            ],
            r(5),
        );
        let roles = infer(&nodes, |reg| Some(if reg.0 == 14 { 4 } else { reg.0 }));
        assert_ne!(roles.get(&0), Some(&ValueRole::Counter));
        assert_ne!(roles.get(&2), Some(&ValueRole::Limit));
    }
}

#[test]
fn dependency_invalidation_work_failure_discards_previously_inferred_roles() {
    fn input(definitions: usize) -> Vec<Node> {
        vec![
            counted(0, 2),
            Node::Evaluate(Expr::load(r(7), Width::U8)),
            Node::Loop(vec![
                step(
                    (0..definitions)
                        .map(|index| set(100 + index, b(BinaryOp::Xor, r(50), c(index as u64))))
                        .collect(),
                ),
                Node::Break,
            ]),
        ]
    }
    let small = infer(&input(8), |reg| Some(reg.0));
    assert_eq!(small.get(&0), Some(&ValueRole::Counter));
    assert_eq!(small.get(&7), Some(&ValueRole::Address));
    // This syntax is well below depth/node/slot limits. Rechecking all retained
    // compound dependencies exhausts the independently charged work budget.
    assert!(infer(&input(800), |reg| Some(reg.0)).is_empty());
}

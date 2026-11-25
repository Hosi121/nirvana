use super::*;
use crate::dataflow::value_width::ValueWidths;
use crate::model::ir::{Assignment, IrInstruction, Reg, UnaryOp, Width};

fn c(value: u64) -> Expr {
    Expr::Const(value)
}
fn r(reg: usize) -> Expr {
    Expr::Register(Reg(reg))
}
fn b(op: BinaryOp, left: Expr, right: Expr) -> Expr {
    Expr::binary(op, left, right)
}
fn set(reg: usize, value: Expr) -> Assignment {
    Assignment {
        destination: Reg(reg).into(),
        value,
    }
}
fn ins(address: u64, assignments: Vec<Assignment>, control: Control) -> IrInstruction {
    IrInstruction {
        address,
        size: 1,
        assignments,
        control,
    }
}
fn branch(assignments: Vec<Assignment>, condition: Expr) -> Program {
    Program::new(
        0,
        8,
        vec![
            ins(
                0,
                assignments,
                Control::Branch {
                    condition,
                    target: 2,
                },
            ),
            ins(1, vec![], Control::Return(c(0))),
            ins(2, vec![], Control::Return(c(0))),
        ],
    )
    .unwrap()
}
fn plans(source: &Program) -> Plans {
    Plans::build(source, 100).unwrap()
}
fn apply(plans: &Plans, kind: EdgeKind, before: &[u8]) -> Vec<u8> {
    plans
        .refine(0, kind, before, &mut Budget(100_000))
        .unwrap()
        .unwrap_or_else(|| before.to_vec())
}
fn incoming(source: &Program, address: u64) -> Vec<u8> {
    ValueWidths::analyze_bounded(source).unwrap().1[source.cfg().block_at(address).unwrap().index()]
        .clone()
        .unwrap()
}

#[test]
fn unsigned_polarities_use_only_the_corresponding_other_operand_cap() {
    for (op, kind, constrained, expected) in [
        (BinaryOp::Ult, EdgeKind::Taken, 0, 3),
        (BinaryOp::Ult, EdgeKind::NotTaken, 1, 4),
        (BinaryOp::Ule, EdgeKind::Taken, 0, 3),
        (BinaryOp::Ule, EdgeKind::NotTaken, 1, 4),
    ] {
        let source = branch(vec![], b(op, r(0), r(1)));
        let before = if kind == EdgeKind::Taken {
            vec![64, 3, 64, 64, 64, 64, 64, 64]
        } else {
            vec![4, 64, 64, 64, 64, 64, 64, 64]
        };
        let result = apply(&plans(&source), kind, &before);
        assert_eq!(result[constrained], expected);
        assert_eq!(result[1 - constrained], before[1 - constrained]);
    }
    // Literal bounds retain their exact value until conversion to bits.
    let ult = branch(vec![], b(BinaryOp::Ult, r(0), c(256)));
    let ule = branch(vec![], b(BinaryOp::Ule, r(0), c(256)));
    assert_eq!(apply(&plans(&ult), EdgeKind::Taken, &[64; 8])[0], 8);
    assert_eq!(apply(&plans(&ule), EdgeKind::Taken, &[64; 8])[0], 9);
    let ult = branch(vec![], b(BinaryOp::Ult, c(256), r(0)));
    let ule = branch(vec![], b(BinaryOp::Ule, c(256), r(0)));
    assert_eq!(apply(&plans(&ult), EdgeKind::NotTaken, &[64; 8])[0], 9);
    assert_eq!(apply(&plans(&ule), EdgeKind::NotTaken, &[64; 8])[0], 8);
}

#[test]
fn predicate_and_operand_copies_preserve_captured_values_after_overwrites() {
    let source = branch(
        vec![
            set(2, r(0)),
            set(3, r(1)),
            set(4, b(BinaryOp::Ult, r(0), r(1))),
            set(5, r(4)),
            set(4, c(0)),
            set(0, c(u64::MAX)),
            set(1, c(u64::MAX)),
        ],
        r(5),
    );
    let mut before = vec![64; 8];
    before[3] = 8;
    let result = apply(&plans(&source), EdgeKind::Taken, &before);
    assert_eq!(result[0], 64); // The current r0 is a different value.
    assert_eq!(result[1], 64);
    assert_eq!(result[2], 8); // The captured left value still has an alias.
    assert_eq!(result[3], 8);

    let lost_rhs = branch(
        vec![set(4, b(BinaryOp::Ult, r(0), r(1))), set(1, c(7))],
        r(4),
    );
    before[1] = 3;
    assert_eq!(apply(&plans(&lost_rhs), EdgeKind::Taken, &before), before);

    let alias_cap = branch(vec![set(2, r(1))], b(BinaryOp::Ult, r(0), r(1)));
    let mut before = vec![64; 8];
    before[2] = 3;
    assert_eq!(apply(&plans(&alias_cap), EdgeKind::Taken, &before)[0], 3);
}

#[test]
fn proved_boolean_normalizations_preserve_relation_polarity() {
    for (op, value, inverted) in [
        (BinaryOp::Eq, 0, true),
        (BinaryOp::Eq, 1, false),
        (BinaryOp::Ne, 0, false),
        (BinaryOp::Ne, 1, true),
        (BinaryOp::Xor, 1, true),
    ] {
        for reversed in [false, true] {
            let condition = if reversed {
                b(op, c(value), r(3))
            } else {
                b(op, r(3), c(value))
            };
            let source = branch(
                vec![set(2, b(BinaryOp::Ult, r(0), c(256))), set(3, r(2))],
                condition,
            );
            let kind = if inverted {
                EdgeKind::NotTaken
            } else {
                EdgeKind::Taken
            };
            assert_eq!(apply(&plans(&source), kind, &[64; 8])[0], 8);
            let opposite = if inverted {
                EdgeKind::Taken
            } else {
                EdgeKind::NotTaken
            };
            assert_eq!(apply(&plans(&source), opposite, &[64; 8])[0], 64);
        }
    }
}

#[test]
fn arbitrary_words_overwritten_flags_and_non_direct_comparisons_do_not_refine() {
    let cases = [
        branch(vec![], b(BinaryOp::Xor, r(0), c(1))),
        branch(
            vec![set(2, b(BinaryOp::Ult, r(0), c(256))), set(2, r(7))],
            r(2),
        ),
        branch(
            vec![],
            b(
                BinaryOp::Ult,
                Expr::unary(
                    UnaryOp::Extract {
                        start: 0,
                        width: Width::U32,
                    },
                    r(0),
                ),
                c(256),
            ),
        ),
        branch(
            vec![],
            b(BinaryOp::Ult, b(BinaryOp::Sub, r(0), r(1)), c(256)),
        ),
        branch(
            vec![],
            b(
                BinaryOp::Ult,
                Expr::unary(UnaryOp::SignExtend(Width::U32), r(0)),
                c(256),
            ),
        ),
    ];
    for source in cases {
        for kind in [EdgeKind::Taken, EdgeKind::NotTaken] {
            assert_eq!(apply(&plans(&source), kind, &[64; 8]), vec![64; 8]);
        }
    }

    // A separately stored low32 comparison can bound that extracted value,
    // while the original word keeps its unknown high bits.
    let low32 = branch(
        vec![set(
            2,
            Expr::unary(
                UnaryOp::Extract {
                    start: 0,
                    width: Width::U32,
                },
                r(0),
            ),
        )],
        b(BinaryOp::Ult, r(2), c(256)),
    );
    let result = apply(&plans(&low32), EdgeKind::Taken, &[64; 8]);
    assert_eq!(result[0], 64);
    assert_eq!(result[2], 8);
}

#[test]
fn zero_strict_caps_and_non_branch_edges_keep_unconditional_state() {
    for (condition, kind) in [
        (b(BinaryOp::Ult, r(0), c(0)), EdgeKind::Taken),
        (b(BinaryOp::Ule, c(0), r(0)), EdgeKind::NotTaken),
    ] {
        assert_eq!(
            apply(&plans(&branch(vec![], condition)), kind, &[64; 8]),
            vec![64; 8]
        );
    }
    let source = branch(vec![], b(BinaryOp::Ult, r(0), c(256)));
    for kind in [EdgeKind::Fallthrough, EdgeKind::Jump, EdgeKind::Indirect] {
        assert_eq!(apply(&plans(&source), kind, &[64; 8]), vec![64; 8]);
    }
}

#[test]
fn counted_loop_two_backedges_narrows_but_keeps_pre_edge_observations() {
    let source = Program::new(
        0,
        8,
        vec![
            ins(
                0,
                vec![set(0, c(0)), set(1, b(BinaryOp::And, r(7), c(7)))],
                Control::Jump(1),
            ),
            ins(
                1,
                vec![],
                Control::Branch {
                    condition: b(BinaryOp::Ult, r(0), r(1)),
                    target: 3,
                },
            ),
            ins(2, vec![], Control::Return(r(0))),
            ins(
                3,
                vec![],
                Control::Branch {
                    condition: r(6),
                    target: 5,
                },
            ),
            ins(
                4,
                vec![set(0, b(BinaryOp::Add, r(0), c(1)))],
                Control::Jump(1),
            ),
            ins(
                5,
                vec![set(0, b(BinaryOp::Add, r(0), c(2)))],
                Control::Jump(1),
            ),
        ],
    )
    .unwrap();
    let (widths, rows) = ValueWidths::analyze_bounded(&source).unwrap();
    assert_eq!(widths[0], Width::U8);
    assert_eq!(incoming(&source, 1)[0], 4);
    assert_eq!(incoming(&source, 3)[0], 3);
    assert_eq!(rows[source.cfg().entry().index()], Some(vec![64; 8]));

    // Reading the original full word at the branch still requires U64
    // storage, even though only its narrower values reach the taken block.
    let observed = Program::new(
        0,
        8,
        vec![
            ins(
                0,
                vec![],
                Control::Branch {
                    condition: b(BinaryOp::Ult, r(0), c(256)),
                    target: 2,
                },
            ),
            ins(1, vec![], Control::Return(c(0))),
            ins(2, vec![set(1, r(0))], Control::Return(r(1))),
        ],
    )
    .unwrap();
    let (widths, _) = ValueWidths::analyze_bounded(&observed).unwrap();
    assert_eq!(widths[0], Width::U64);
    assert_eq!(widths[1], Width::U8);
}

#[test]
fn initialized_counter_with_two_guarded_backedges_stays_byte_sized() {
    for limit in [c(7), b(BinaryOp::And, r(7), c(7))] {
        // Match the selected-source shape: header work increments the
        // counter, and either tail compares the new value before looping.
        let source = Program::new(
            0,
            8,
            vec![
                ins(0, vec![set(0, c(0)), set(1, limit)], Control::Jump(1)),
                ins(
                    1,
                    vec![set(2, b(BinaryOp::Add, r(0), c(1))), set(0, r(2))],
                    Control::Branch {
                        condition: r(6),
                        target: 4,
                    },
                ),
                ins(
                    2,
                    vec![],
                    Control::Branch {
                        condition: b(BinaryOp::Ult, r(0), r(1)),
                        target: 1,
                    },
                ),
                ins(3, vec![], Control::Return(r(0))),
                ins(
                    4,
                    vec![],
                    Control::Branch {
                        condition: b(BinaryOp::Ult, r(0), r(1)),
                        target: 1,
                    },
                ),
                ins(5, vec![], Control::Return(r(0))),
            ],
        )
        .unwrap();
        let (widths, _) = ValueWidths::analyze_bounded(&source).unwrap();
        assert_eq!(widths[0], Width::U8);
        assert_eq!(widths[2], Width::U8);
        assert_eq!(incoming(&source, 1)[0], 3);
    }
}

#[test]
fn unguarded_predecessor_and_same_target_arms_join_all_states() {
    let source = Program::new(
        0,
        8,
        vec![
            ins(
                0,
                vec![],
                Control::Branch {
                    condition: r(7),
                    target: 2,
                },
            ),
            ins(
                1,
                vec![],
                Control::Branch {
                    condition: b(BinaryOp::Ult, r(0), c(256)),
                    target: 3,
                },
            ),
            ins(2, vec![], Control::Jump(3)),
            ins(3, vec![], Control::Return(r(0))),
        ],
    )
    .unwrap();
    assert_eq!(incoming(&source, 3)[0], 64);
    let source = Program::new(
        0,
        8,
        vec![
            ins(
                0,
                vec![],
                Control::Branch {
                    condition: b(BinaryOp::Ult, r(0), c(256)),
                    target: 1,
                },
            ),
            ins(1, vec![], Control::Return(r(0))),
        ],
    )
    .unwrap();
    assert_eq!(source.cfg().blocks()[0].successors.len(), 2);
    assert_eq!(incoming(&source, 1)[0], 64);
}

#[test]
fn no_predicate_is_carried_through_another_block_or_an_entry_backedge() {
    let source = Program::new(
        0,
        8,
        vec![
            ins(
                0,
                vec![set(2, b(BinaryOp::Ult, r(0), c(256)))],
                Control::Jump(1),
            ),
            ins(
                1,
                vec![],
                Control::Branch {
                    condition: r(2),
                    target: 3,
                },
            ),
            ins(2, vec![], Control::Return(c(0))),
            ins(3, vec![], Control::Return(r(0))),
        ],
    )
    .unwrap();
    assert_eq!(incoming(&source, 3)[0], 64);
    let source = Program::new(
        0,
        8,
        vec![
            ins(
                0,
                vec![],
                Control::Branch {
                    condition: b(BinaryOp::Ult, r(0), c(256)),
                    target: 2,
                },
            ),
            ins(1, vec![], Control::Return(r(0))),
            ins(2, vec![], Control::Jump(0)),
        ],
    )
    .unwrap();
    assert_eq!(incoming(&source, 0), vec![64; 8]);
}

#[test]
fn unresolved_targets_preserve_existing_failure_and_planning_is_optional() {
    let unresolved = Program::new(
        0,
        8,
        vec![ins(
            0,
            vec![],
            Control::Branch {
                condition: b(BinaryOp::Ult, r(0), c(256)),
                target: 42,
            },
        )],
    );
    assert!(matches!(
        unresolved,
        Err(crate::model::ir::ProgramError::Unresolved(_))
    ));
    let large = Program::new(
        0,
        MAX_REGISTERS + 1,
        vec![ins(0, vec![set(0, c(7))], Control::Return(r(0)))],
    )
    .unwrap();
    assert!(Plans::build(&large, 2).is_none());
    assert_eq!(
        ValueWidths::analyze_bounded(&large).unwrap().0[0],
        Width::U8
    );
    assert!(Plans::build(&branch(vec![], r(0)), MAX_POINTS + 1).is_none());

    // Within all size limits, optional planning still has its own work cap.
    let mut instructions: Vec<_> = (0..89)
        .map(|address| {
            ins(
                address,
                vec![],
                Control::Branch {
                    condition: b(BinaryOp::Ult, r(0), c(256)),
                    target: address + 1,
                },
            )
        })
        .collect();
    instructions.push(ins(89, vec![], Control::Return(r(0))));
    let source = Program::new(0, MAX_REGISTERS, instructions).unwrap();
    assert!(Plans::build(&source, 90).is_none());
    assert_eq!(
        ValueWidths::analyze_bounded(&source).unwrap().0[0],
        Width::U64
    );
}

#[test]
fn guard_applications_are_charged_to_the_existing_work_budget() {
    let source = branch(vec![], b(BinaryOp::Ult, r(0), c(256)));
    let plan = plans(&source);
    assert!(
        plan.refine(0, EdgeKind::Taken, &[64; 8], &mut Budget(0))
            .is_none()
    );
    assert!(
        plan.refine(0, EdgeKind::Taken, &[64; 8], &mut Budget(2))
            .is_none()
    );
}

use super::*;
use crate::dataflow::value_width::verify::{Invalid, ValidationEvidence, validate};
use crate::model::ir::{Assignment, BinaryOp as B, Program, UnaryOp, Width};

fn c(value: u64) -> Expr {
    Expr::Const(value)
}
fn r(register: usize) -> Expr {
    Expr::Register(Reg(register))
}
fn b(operation: B, left: Expr, right: Expr) -> Expr {
    Expr::binary(operation, left, right)
}
fn set(register: usize, value: Expr) -> Assignment {
    Assignment {
        destination: Reg(register).into(),
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
fn source(instructions: Vec<IrInstruction>) -> Program {
    Program::new(0, 8, instructions).unwrap()
}
fn branch(assignments: Vec<Assignment>, condition: Expr) -> Program {
    source(vec![
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
    ])
}
fn rows(source: &Program) -> Vec<Option<Vec<u8>>> {
    let mut rows = vec![None; source.cfg().blocks().len()];
    for block in source.cfg().reachable_blocks() {
        rows[block.index()] = Some(vec![64; source.register_count()]);
    }
    rows
}
fn derive_guard(source: &Program) -> Guard {
    let block = &source.cfg().blocks()[source.cfg().entry().index()];
    derive(
        &source.instructions()[block.instructions.clone()],
        source.register_count(),
        &mut Budget::new(source.register_count()),
    )
    .expect("supported checker guard")
}
fn covered(guard: Option<&Guard>, kind: EdgeKind, post: &[u128], next: &[u8]) -> bool {
    covers(
        guard,
        kind,
        post,
        next,
        &mut Work {
            remaining: 1_000_000,
            evidence: ValidationEvidence::default(),
        },
    )
    .unwrap()
}

#[test]
fn the_four_unsigned_rules_keep_exact_numeric_caps_until_row_comparison() {
    for (operation, kind, constrained, bounding_value) in [
        (B::Ult, EdgeKind::Taken, 0, 8),
        (B::Ult, EdgeKind::NotTaken, 1, 7),
        (B::Ule, EdgeKind::Taken, 0, 7),
        (B::Ule, EdgeKind::NotTaken, 1, 8),
    ] {
        let source = branch(vec![], b(operation, r(0), r(1)));
        let guard = derive_guard(&source);
        let mut post = vec![1000; 8];
        post[1 - constrained] = bounding_value;
        let mut next = vec![64; 8];
        next[constrained] = 3;
        assert!(covered(Some(&guard), kind, &post, &next));
        assert!(!covered(None, kind, &post, &next));
        next[constrained] = 2;
        assert!(!covered(Some(&guard), kind, &post, &next));
        next[constrained] = 3;
        assert!(!covered(Some(&guard), EdgeKind::Jump, &post, &next));
        assert!(!covered(Some(&guard), EdgeKind::Fallthrough, &post, &next));
    }
}

#[test]
fn zero_strict_caps_do_not_underflow_or_prove_reachability() {
    for (operation, kind, constrained) in [
        (B::Ult, EdgeKind::Taken, 0),
        (B::Ule, EdgeKind::NotTaken, 1),
    ] {
        let source = branch(vec![], b(operation, r(0), r(1)));
        let guard = derive_guard(&source);
        let mut post = vec![0; 8];
        post[constrained] = 255;
        let mut next = vec![64; 8];
        next[constrained] = 0;
        assert!(!covered(Some(&guard), kind, &post, &next));
    }
}

#[test]
fn boolean_copies_and_proved_inversions_preserve_relation_polarity() {
    let relation = b(B::Ult, r(0), r(1));
    for (condition, inverted) in [
        (r(3), false),
        (b(B::Xor, r(3), c(1)), true),
        (b(B::Eq, c(0), r(3)), true),
        (b(B::Eq, r(3), c(1)), false),
        (b(B::Ne, r(3), c(0)), false),
        (b(B::Ne, c(1), r(3)), true),
        (b(B::Eq, b(B::Xor, r(3), c(1)), c(0)), false),
    ] {
        let source = branch(vec![set(2, relation.clone()), set(3, r(2))], condition);
        let guard = derive_guard(&source);
        let mut post = vec![1000; 8];
        post[1] = 8;
        let mut next = vec![64; 8];
        next[0] = 3;
        let kind = if inverted {
            EdgeKind::NotTaken
        } else {
            EdgeKind::Taken
        };
        assert!(covered(Some(&guard), kind, &post, &next));
    }
}

#[test]
fn comparison_snapshots_use_current_aliases_and_literals_after_overwrites() {
    let source = branch(
        vec![
            set(3, r(0)),
            set(4, r(1)),
            set(2, b(B::Ult, r(0), r(1))),
            set(0, Expr::load(c(0), Width::U64)),
            set(1, Expr::load(c(8), Width::U64)),
        ],
        r(2),
    );
    let guard = derive_guard(&source);
    let mut post = vec![1000; 8];
    post[4] = 8;
    let mut next = vec![64; 8];
    next[3] = 3;
    assert!(covered(Some(&guard), EdgeKind::Taken, &post, &next));
    next[0] = 3;
    assert!(!covered(Some(&guard), EdgeKind::Taken, &post, &next));
    next[0] = 64;
    // The overwritten RHS's current bound is unavailable as a bound for the
    // snapshot, even if its new value happens to be smaller.
    post[1] = 0;
    post[4] = 1000;
    assert!(!covered(Some(&guard), EdgeKind::Taken, &post, &next));

    let literal = branch(
        vec![set(1, c(8)), set(2, b(B::Ult, r(0), r(1))), set(1, c(0))],
        r(2),
    );
    let literal_guard = derive_guard(&literal);
    next[3] = 64;
    next[0] = 3;
    assert!(covered(Some(&literal_guard), EdgeKind::Taken, &post, &next));
}

#[test]
fn arbitrary_word_xor_low_word_and_nonrelational_flags_cannot_narrow_rows() {
    let low = Expr::unary(
        UnaryOp::Extract {
            start: 0,
            width: Width::U32,
        },
        r(0),
    );
    for (assignments, condition) in [
        (vec![], b(B::Xor, r(0), c(1))),
        (vec![], b(B::Eq, r(0), c(0))),
        (vec![], b(B::Ult, low, c(8))),
        (vec![], b(B::Eq, b(B::Shr, r(0), c(63)), c(0))),
        (vec![], b(B::Ne, b(B::Sub, r(0), r(1)), c(0))),
        (vec![set(2, b(B::Ult, r(0), c(8))), set(2, r(7))], r(2)),
        (
            vec![
                set(2, b(B::Ult, r(0), c(8))),
                set(0, Expr::load(c(0), Width::U64)),
            ],
            r(2),
        ),
    ] {
        let source = branch(assignments, condition);
        let mut incoming = rows(&source);
        incoming[source.cfg().block_at(2).unwrap().index()]
            .as_mut()
            .unwrap()[0] = 3;
        assert_eq!(
            validate(&source, &[Width::U64; 8], &incoming),
            Err(Invalid("successor entry bound"))
        );
    }
}

#[test]
fn edge_refinement_does_not_narrow_prior_source_storage_observations() {
    let source = branch(vec![], b(B::Ult, r(0), c(8)));
    let mut incoming = rows(&source);
    incoming[source.cfg().block_at(2).unwrap().index()]
        .as_mut()
        .unwrap()[0] = 3;
    assert!(validate(&source, &[Width::U64; 8], &incoming).is_ok());
    let mut widths = vec![Width::U64; 8];
    widths[0] = Width::U8;
    assert_eq!(
        validate(&source, &widths, &incoming),
        Err(Invalid("storage read bound"))
    );
    let written = branch(vec![set(0, c(u64::MAX))], b(B::Ult, r(0), c(8)));
    assert_eq!(
        validate(&written, &widths, &incoming),
        Err(Invalid("storage write bound"))
    );
}

#[test]
fn two_guarded_backedges_admit_a_counter_and_reject_a_mutated_certificate() {
    let compare = || b(B::Ult, r(0), r(1));
    let increment = || set(0, b(B::Add, r(0), c(1)));
    let source = source(vec![
        ins(
            0,
            vec![set(0, c(0)), set(1, b(B::And, r(7), c(7)))],
            Control::Jump(1),
        ),
        ins(
            1,
            vec![],
            Control::Branch {
                condition: compare(),
                target: 3,
            },
        ),
        ins(2, vec![], Control::Return(r(0))),
        ins(
            3,
            vec![],
            Control::Branch {
                condition: r(6),
                target: 6,
            },
        ),
        ins(
            4,
            vec![increment()],
            Control::Branch {
                condition: compare(),
                target: 1,
            },
        ),
        ins(5, vec![], Control::Return(r(0))),
        ins(
            6,
            vec![increment()],
            Control::Branch {
                condition: compare(),
                target: 1,
            },
        ),
        ins(7, vec![], Control::Return(r(0))),
    ]);
    let mut incoming = rows(&source);
    for address in [1, 2, 3, 4, 5, 6, 7] {
        let row = incoming[source.cfg().block_at(address).unwrap().index()]
            .as_mut()
            .unwrap();
        row[0] = if matches!(address, 5 | 7) { 4 } else { 3 };
        row[1] = 3;
    }
    let mut widths = vec![Width::U64; 8];
    widths[0] = Width::U8;
    widths[1] = Width::U8;
    assert_eq!(validate(&source, &widths, &incoming).unwrap().edges, 9);
    let mut too_small = incoming.clone();
    too_small[source.cfg().block_at(1).unwrap().index()]
        .as_mut()
        .unwrap()[0] = 2;
    assert_eq!(
        validate(&source, &widths, &too_small),
        Err(Invalid("successor entry bound"))
    );
    let mut initial = incoming.clone();
    initial[source.cfg().entry().index()].as_mut().unwrap()[0] = 3;
    assert_eq!(
        validate(&source, &widths, &initial),
        Err(Invalid("arbitrary initial boundary"))
    );
    let mut missing = incoming;
    missing[source.cfg().block_at(6).unwrap().index()] = None;
    assert_eq!(
        validate(&source, &widths, &missing),
        Err(Invalid("reachable block coverage"))
    );
}

#[test]
fn same_target_edges_unguarded_predecessors_and_cross_block_flags_remain_covered() {
    for source in [
        source(vec![
            ins(
                0,
                vec![],
                Control::Branch {
                    condition: b(B::Ult, r(0), c(8)),
                    target: 1,
                },
            ),
            ins(1, vec![], Control::Return(c(0))),
        ]),
        source(vec![
            ins(
                0,
                vec![],
                Control::Branch {
                    condition: r(7),
                    target: 2,
                },
            ),
            ins(1, vec![], Control::Jump(3)),
            ins(
                2,
                vec![],
                Control::Branch {
                    condition: b(B::Ult, r(0), c(8)),
                    target: 3,
                },
            ),
            ins(3, vec![], Control::Return(c(0))),
        ]),
        source(vec![
            ins(0, vec![set(2, b(B::Ult, r(0), c(8)))], Control::Jump(1)),
            ins(
                1,
                vec![],
                Control::Branch {
                    condition: r(2),
                    target: 3,
                },
            ),
            ins(2, vec![], Control::Return(c(0))),
            ins(3, vec![], Control::Return(c(0))),
        ]),
    ] {
        let mut incoming = rows(&source);
        incoming.last_mut().unwrap().as_mut().unwrap()[0] = 3;
        assert_eq!(
            validate(&source, &[Width::U64; 8], &incoming),
            Err(Invalid("successor entry bound"))
        );
    }
}

#[test]
fn long_source_chains_are_iterative_and_optional_budget_exhaustion_is_unconditional() {
    let mut assignments = vec![set(2, b(B::Ult, r(0), c(8)))];
    assignments.extend((0..10_000).map(|_| set(2, r(2))));
    let source = branch(assignments, r(2));
    let guard = derive_guard(&source);
    let post = vec![1000; 8];
    let mut next = vec![64; 8];
    next[0] = 3;
    assert!(covered(Some(&guard), EdgeKind::Taken, &post, &next));

    let mut budget = Budget { remaining: 100 };
    assert!(derive(&source.instructions()[..1], 8, &mut budget).is_none());
    assert!(!covered(None, EdgeKind::Taken, &post, &next));
    let mut assignments = vec![set(2, b(B::Ult, r(0), c(8)))];
    assignments.extend((0..5_000).map(|_| set(2, b(B::Xor, r(2), c(1)))));
    let source = branch(assignments, r(2));
    let guard = derive_guard(&source);
    assert!(covered(Some(&guard), EdgeKind::Taken, &post, &next));

    let large = branch(vec![], b(B::Ult, r(0), c(8)));
    assert!(derive(&large.instructions()[..1], 4097, &mut Budget::new(4097)).is_none());
}

#[test]
fn distinct_register_copy_chains_reuse_backward_resolutions_within_budget() {
    let registers = 1001;
    let source = Program::new(
        0,
        registers,
        vec![
            ins(
                0,
                (1..registers).map(|reg| set(reg, r(reg - 1))).collect(),
                Control::Branch {
                    condition: b(B::Ult, r(registers - 1), c(256)),
                    target: 2,
                },
            ),
            ins(1, vec![], Control::Return(c(0))),
            ins(2, vec![], Control::Return(c(0))),
        ],
    )
    .unwrap();
    let mut budget = Budget::new(registers);
    let guard = derive(&source.instructions()[..1], registers, &mut budget)
        .expect("copy chain must fit the structural budget");
    assert!(budget.remaining > MAX_GUARD_WORK - 50_000);
    assert_eq!(guard.left, (0..registers).collect::<Vec<_>>());
    let post = vec![unsigned_caps::WORD_MAX; registers];
    let mut next = vec![8; registers];
    assert!(covered(Some(&guard), EdgeKind::Taken, &post, &next));
    next[registers - 1] = 7;
    assert!(!covered(Some(&guard), EdgeKind::Taken, &post, &next));
}

#[test]
fn memoized_writer_references_keep_old_snapshots_distinct_from_later_writes() {
    let instructions = [ins(
        0,
        vec![
            set(1, r(0)),
            set(2, r(1)),
            set(0, Expr::load(c(0), Width::U64)),
            set(1, r(0)),
            set(3, r(2)),
            set(2, c(7)),
            set(4, r(2)),
        ],
        Control::Return(c(0)),
    )];
    let mut budget = Budget::new(8);
    let history = History::new(&instructions, 8, &mut budget).unwrap();
    let mut resolved = vec![None; history.values.len()];
    assert_eq!(
        history.value(&r(2), 2, &mut resolved, &mut budget),
        Ok(Some(Value::Entry(0)))
    );
    for (register, expected) in [
        (0, Value::Definition(2)),
        (1, Value::Definition(2)),
        (2, Value::Literal(7)),
        (3, Value::Entry(0)),
        (4, Value::Literal(7)),
    ] {
        assert_eq!(
            history.value(
                &r(register),
                history.values.len(),
                &mut resolved,
                &mut budget,
            ),
            Ok(Some(expected))
        );
    }
    assert_eq!(resolved[1], Some(Value::Entry(0)));
    assert_eq!(resolved[5], Some(Value::Literal(7)));
}

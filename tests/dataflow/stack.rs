use nirvana::ir::{
    AccessKind, Assignment, BinaryOp, Control, Expr, IrInstruction, Place, Program, Reg, UnaryOp,
    Width,
};
use nirvana::reduce::reduce;
use nirvana::stack::{StackAccess, StackAnalysis};

use crate::support::ir::r;

use crate::support::ir::c;

fn add(left: Expr, right: Expr) -> Expr {
    Expr::binary(BinaryOp::Add, left, right)
}

fn sub(left: Expr, right: Expr) -> Expr {
    Expr::binary(BinaryOp::Sub, left, right)
}

fn set(index: usize, value: Expr) -> Assignment {
    Assignment {
        destination: Reg(index).into(),
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

fn program(registers: usize, instructions: Vec<IrInstruction>) -> Program {
    Program::new(0, registers, instructions).unwrap()
}

fn access(
    instruction: u64,
    assignment: usize,
    offset: i64,
    width: Width,
    kind: AccessKind,
) -> StackAccess {
    StackAccess {
        instruction,
        assignment,
        offset,
        width,
        kind,
    }
}

#[test]
fn input_registers_are_unknown_and_queries_use_exact_points() {
    let p = program(3, vec![instruction(0, vec![], Control::Return(r(0)))]);
    let a = StackAnalysis::analyze(&p, Reg(0));
    assert_eq!(a.offset_before(0, 0, &r(0)), Some(0));
    assert_eq!(a.offset_before(0, 0, &add(r(0), r(1))), None);
    assert_eq!(a.offset_before(0, 0, &r(1)), None);
    assert_eq!(a.offset_before(0, 0, &c(0)), None);
    assert_eq!(a.offset_before(0, 0, &r(999)), None);
    assert_eq!(a.offset_before(0, 1, &r(0)), None);
    assert_eq!(a.offset_before(1, 0, &r(0)), None);
    assert!(a.accesses().is_empty());
    let invalid = StackAnalysis::analyze(&p, Reg(3));
    assert_eq!(invalid.offset_before(0, 0, &r(0)), None);
    assert!(invalid.accesses().is_empty());
}

#[test]
fn ordered_writes_frame_copies_and_reused_temporaries_are_not_ssa() {
    let p = program(
        3,
        vec![instruction(
            0,
            vec![
                set(1, r(0)),
                set(2, r(0)),
                set(0, sub(r(0), c(8))),
                set(2, sub(r(2), c(16))),
                store(add(r(2), c(4)), Width::U32, c(7)),
                set(2, r(0)),
                set(2, Expr::load(r(2), Width::U64)),
            ],
            Control::Return(Expr::load(add(r(1), c(8)), Width::U8)),
        )],
    );
    let a = StackAnalysis::analyze(&p, Reg(0));
    assert_eq!(a.offset_before(0, 0, &r(1)), None);
    assert_eq!(a.offset_before(0, 1, &r(1)), Some(0));
    assert_eq!(a.offset_before(0, 2, &r(0)), Some(0));
    assert_eq!(a.offset_before(0, 3, &r(0)), Some(-8));
    assert_eq!(a.offset_before(0, 3, &r(2)), Some(0));
    assert_eq!(a.offset_before(0, 4, &r(2)), Some(-16));
    assert_eq!(a.offset_before(0, 6, &r(2)), Some(-8));
    assert_eq!(a.offset_before(0, 7, &r(2)), None);
    assert_eq!(a.offset_before(0, 7, &r(1)), Some(0));
    assert_eq!(
        a.accesses(),
        &[
            access(0, 4, -12, Width::U32, AccessKind::Write),
            access(0, 6, -8, Width::U64, AccessKind::Read),
            access(0, 7, 8, Width::U8, AccessKind::Read),
        ]
    );
}

fn diamond(left: Expr, right: Expr) -> Program {
    program(
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
            instruction(1, vec![set(1, left)], Control::Jump(3)),
            instruction(2, vec![set(1, right)], Control::Jump(3)),
            instruction(3, vec![], Control::Return(Expr::load(r(1), Width::U64))),
            // This unknown predecessor must not poison the reachable join.
            instruction(4, vec![set(1, r(2))], Control::Jump(3)),
        ],
    )
}

#[test]
fn diamond_meets_keep_only_agreeing_affine_or_constant_values() {
    let same = diamond(sub(r(0), c(16)), add(c(u64::MAX - 15), r(0)));
    let a = StackAnalysis::analyze(&same, Reg(0));
    assert_eq!(a.offset_before(3, 0, &r(1)), Some(-16));
    assert_eq!(a.offset_before(4, 0, &r(0)), None);
    assert_eq!(
        a.accesses(),
        &[access(3, 0, -16, Width::U64, AccessKind::Read)]
    );
    for p in [
        diamond(sub(r(0), c(16)), sub(r(0), c(8))),
        diamond(sub(r(0), c(16)), r(2)),
    ] {
        let a = StackAnalysis::analyze(&p, Reg(0));
        assert_eq!(a.offset_before(3, 0, &r(1)), None);
        assert!(a.accesses().is_empty());
    }
    let constants = diamond(c(24), sub(c(32), c(8)));
    let a = StackAnalysis::analyze(&constants, Reg(0));
    assert_eq!(a.offset_before(3, 0, &add(r(0), r(1))), Some(24));
}

#[test]
fn loops_converge_before_exposing_facts_and_preserve_saved_frame_values() {
    let p = program(
        3,
        vec![
            instruction(0, vec![set(1, r(0))], Control::Jump(1)),
            instruction(
                1,
                vec![store(r(0), Width::U8, c(0)), set(0, sub(r(0), c(8)))],
                Control::Branch {
                    condition: r(2),
                    target: 1,
                },
            ),
            instruction(2, vec![], Control::Return(Expr::load(r(1), Width::U64))),
        ],
    );
    let a = StackAnalysis::analyze(&p, Reg(0));
    assert_eq!(a.offset_before(0, 0, &r(0)), Some(0));
    assert_eq!(a.offset_before(1, 0, &r(0)), None);
    assert_eq!(a.offset_before(1, 2, &r(0)), None);
    assert_eq!(a.offset_before(1, 0, &r(1)), Some(0));
    assert_eq!(
        a.accesses(),
        &[access(2, 0, 0, Width::U64, AccessKind::Read)]
    );
}

#[test]
fn entry_backedges_meet_the_original_boundary_including_unknown_inputs() {
    for step in [0, 8] {
        let p = program(
            3,
            vec![
                instruction(
                    0,
                    vec![
                        store(r(0), Width::U8, c(0)),
                        set(1, r(0)),
                        set(0, sub(r(0), c(step))),
                    ],
                    Control::Branch {
                        condition: r(2),
                        target: 0,
                    },
                ),
                instruction(1, vec![], Control::Return(c(0))),
            ],
        );
        let a = StackAnalysis::analyze(&p, Reg(0));
        assert_eq!(a.offset_before(0, 0, &r(1)), None);
        assert_eq!(a.offset_before(0, 0, &r(0)), (step == 0).then_some(0));
        assert_eq!(a.accesses().len(), usize::from(step == 0));
    }
}

#[test]
fn dynamic_stack_updates_are_unknown_but_saved_copies_remain_known() {
    let p = program(
        3,
        vec![instruction(
            0,
            vec![set(1, r(0)), set(0, sub(r(0), r(2)))],
            Control::Return(c(0)),
        )],
    );
    let a = StackAnalysis::analyze(&p, Reg(0));
    assert_eq!(a.offset_before(0, 2, &r(0)), None);
    assert_eq!(a.offset_before(0, 2, &add(r(0), c(8))), None);
    assert_eq!(a.offset_before(0, 2, &sub(r(1), c(24))), Some(-24));
}

#[test]
fn offsets_wrap_as_u64_and_other_arithmetic_is_not_guessed() {
    let p = program(
        2,
        vec![instruction(
            0,
            vec![set(1, c(u64::MAX)), set(0, add(r(0), c(u64::MAX)))],
            Control::Return(c(0)),
        )],
    );
    let a = StackAnalysis::analyze(&p, Reg(0));
    assert_eq!(a.offset_before(0, 2, &r(0)), Some(-1));
    assert_eq!(a.offset_before(0, 2, &sub(r(0), r(1))), Some(0));
    assert_eq!(
        a.offset_before(0, 0, &add(c(1 << 63), r(0))),
        Some(i64::MIN)
    );
    assert_eq!(a.offset_before(0, 2, &add(r(0), c(2))), Some(1));
    for op in [
        BinaryOp::Mul,
        BinaryOp::And,
        BinaryOp::Or,
        BinaryOp::Xor,
        BinaryOp::Shl,
        BinaryOp::Shr,
        BinaryOp::UMulHigh,
    ] {
        assert_eq!(a.offset_before(0, 0, &Expr::binary(op, r(0), c(0))), None);
    }
    assert_eq!(a.offset_before(0, 0, &add(r(0), r(0))), None);
    assert_eq!(a.offset_before(0, 0, &sub(c(0), r(0))), None);
}

#[test]
fn unary_widths_preserve_only_full_word_stack_identities() {
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
        UnaryOp::Extract {
            start: 255,
            width: Width::U8,
        },
    ] {
        let expression = Expr::Unary(op, Box::new(r(0)));
        let p = program(
            2,
            vec![instruction(
                0,
                vec![set(1, expression.clone())],
                Control::Return(r(1)),
            )],
        );
        let a = StackAnalysis::try_analyze(&p, Reg(0)).unwrap();
        assert_eq!(a.offset_before(0, 0, &expression), None, "{op:?}");
        assert_eq!(a.offset_before(0, 1, &r(1)), None, "{op:?}");
    }
    for op in [
        UnaryOp::SignExtend(Width::U64),
        UnaryOp::Extract {
            start: 0,
            width: Width::U64,
        },
    ] {
        let p = program(
            2,
            vec![instruction(
                0,
                vec![set(1, Expr::Unary(op, Box::new(sub(r(0), c(8)))))],
                Control::Return(r(1)),
            )],
        );
        let a = StackAnalysis::try_analyze(&p, Reg(0)).unwrap();
        assert_eq!(a.offset_before(0, 1, &r(1)), Some(-8));
    }
}

#[test]
fn constant_unary_boundaries_retain_wrapped_offsets() {
    for (op, value, offset) in [
        (UnaryOp::SignExtend(Width::U8), 0x80, -128),
        (UnaryOp::SignExtend(Width::U16), 0x8000, -32768),
        (UnaryOp::SignExtend(Width::U32), 0x8000_0000, -2147483648),
        (
            UnaryOp::Extract {
                start: 63,
                width: Width::U8,
            },
            u64::MAX,
            1,
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
        let p = program(
            2,
            vec![instruction(
                0,
                vec![
                    set(1, Expr::Unary(op, Box::new(c(value)))),
                    set(1, add(r(0), r(1))),
                ],
                Control::Return(r(1)),
            )],
        );
        let a = StackAnalysis::try_analyze(&p, Reg(0)).unwrap();
        assert_eq!(a.offset_before(0, 2, &r(1)), Some(offset), "{op:?}");
        let checked = nirvana::stack::validate(&p, Reg(0), &a).unwrap();
        assert_eq!(checked.offset_before(0, 2, &r(1)).unwrap(), Some(offset));
    }
}

#[test]
fn pure_equal_select_arms_survive_but_no_query_can_erase_a_load() {
    let p = program(
        3,
        vec![instruction(
            0,
            vec![
                set(1, Expr::select(r(2), r(0), add(r(0), c(0)))),
                set(
                    2,
                    Expr::select(Expr::load(c(u64::MAX), Width::U8), r(0), r(0)),
                ),
            ],
            Control::Return(c(0)),
        )],
    );
    let a = StackAnalysis::analyze(&p, Reg(0));
    assert_eq!(a.offset_before(0, 2, &r(1)), Some(0));
    assert_eq!(a.offset_before(0, 2, &r(2)), None);
    assert_eq!(
        a.offset_before(0, 0, &Expr::select(r(2), r(0), add(r(0), c(1)))),
        None
    );
    for expression in [
        Expr::load(r(0), Width::U64),
        Expr::select(Expr::load(c(u64::MAX), Width::U8), r(0), r(0)),
        Expr::select(c(1), r(0), Expr::load(r(0), Width::U64)),
        Expr::select(
            Expr::binary(BinaryOp::Mul, Expr::load(r(0), Width::U8), c(0)),
            r(0),
            r(0),
        ),
    ] {
        assert_eq!(a.offset_before(0, 0, &expression), None);
    }
}

#[test]
fn nested_loads_control_expressions_and_overlapping_stores_are_all_visited() {
    let p = program(
        3,
        vec![
            instruction(
                0,
                vec![
                    store(r(0), Width::U64, c(0)),
                    store(add(r(0), c(1)), Width::U16, c(7)),
                    store(
                        Expr::load(add(r(0), c(8)), Width::U64),
                        Width::U32,
                        Expr::load(sub(r(0), c(4)), Width::U8),
                    ),
                    set(
                        1,
                        Expr::load(Expr::load(add(r(0), c(16)), Width::U64), Width::U64),
                    ),
                    set(2, Expr::load(r(0), Width::U64)),
                    store(r(2), Width::U64, c(0)),
                ],
                Control::Branch {
                    condition: Expr::load(add(r(0), c(2)), Width::U16),
                    target: 1,
                },
            ),
            instruction(
                1,
                vec![],
                Control::Return(Expr::select(
                    r(1),
                    Expr::load(add(r(0), c(3)), Width::U32),
                    Expr::load(add(r(0), c(4)), Width::U64),
                )),
            ),
        ],
    );
    let a = StackAnalysis::analyze(&p, Reg(0));
    assert_eq!(
        a.accesses(),
        &[
            access(0, 0, 0, Width::U64, AccessKind::Write),
            access(0, 1, 1, Width::U16, AccessKind::Write),
            access(0, 2, 8, Width::U64, AccessKind::Read),
            access(0, 2, -4, Width::U8, AccessKind::Read),
            access(0, 3, 16, Width::U64, AccessKind::Read),
            access(0, 4, 0, Width::U64, AccessKind::Read),
            access(0, 6, 2, Width::U16, AccessKind::Read),
            access(1, 0, 3, Width::U32, AccessKind::Read),
            access(1, 0, 4, Width::U64, AccessKind::Read),
        ]
    );
    // Even a pointer just stored to the same stack location is not reloaded as
    // an affine value. This avoids claims about aliasing and memory contents.
    assert_eq!(a.offset_before(0, 5, &r(2)), None);
}

#[test]
fn original_and_reduced_programs_discover_the_same_concrete_stack_accesses() {
    let p = program(
        3,
        vec![
            instruction(
                0,
                vec![set(1, r(0)), set(0, sub(r(0), c(32)))],
                Control::Next,
            ),
            instruction(
                1,
                vec![
                    set(2, sub(r(1), c(16))),
                    store(r(2), Width::U32, c(9)),
                    set(2, Expr::load(add(r(0), c(16)), Width::U32)),
                ],
                Control::Return(r(2)),
            ),
        ],
    );
    let reduced = reduce(&p).unwrap();
    let original = StackAnalysis::analyze(&p, Reg(0));
    let reduced = StackAnalysis::analyze(reduced.program(), Reg(0));
    let signature = |a: &StackAnalysis| {
        a.accesses()
            .iter()
            .map(|access| (access.instruction, access.offset, access.width, access.kind))
            .collect::<Vec<_>>()
    };
    assert_eq!(signature(&original), signature(&reduced));
    assert_eq!(original.accesses().len(), 2);
}

#[test]
fn resource_fallback_discards_all_facts_including_already_collected_accesses() {
    let huge = program(500_001, vec![instruction(0, vec![], Control::Return(r(0)))]);
    let a = StackAnalysis::analyze(&huge, Reg(0));
    assert_eq!(a.offset_before(0, 0, &r(0)), None);
    assert!(a.accesses().is_empty());

    let mut deep = r(0);
    for _ in 0..260 {
        deep = add(deep, c(0));
    }
    let p = program(
        1,
        vec![
            instruction(0, vec![store(r(0), Width::U8, c(0))], Control::Next),
            instruction(1, vec![], Control::Return(deep.clone())),
        ],
    );
    let a = StackAnalysis::analyze(&p, Reg(0));
    assert_eq!(a.offset_before(0, 0, &r(0)), None);
    assert!(a.accesses().is_empty());

    let small = program(1, vec![instruction(0, vec![], Control::Return(c(0)))]);
    let a = StackAnalysis::analyze(&small, Reg(0));
    assert_eq!(a.offset_before(0, 0, &deep), None);
    assert_eq!(a.offset_before(0, 0, &r(0)), Some(0));
}

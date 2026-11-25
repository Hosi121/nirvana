use super::*;
use crate::model::ir::{BinaryOp, IrInstruction, Reg, Width};

fn reg(index: usize) -> Expr {
    Expr::Register(Reg(index))
}

fn binary(op: BinaryOp, left: Expr, right: Expr) -> Expr {
    Expr::binary(op, left, right)
}

fn set(index: usize, value: Expr) -> Assignment {
    Assignment {
        destination: Reg(index).into(),
        value,
    }
}

fn add(index: usize, value: u64) -> Assignment {
    set(index, binary(BinaryOp::Add, reg(index), Expr::Const(value)))
}

fn store(offset: u64, index: usize) -> Assignment {
    Assignment {
        destination: Place::Memory {
            address: Expr::Const(0x1000 + offset),
            width: Width::U64,
        },
        value: reg(index),
    }
}

fn branch(condition: Expr, target: u64) -> Control {
    Control::Branch { condition, target }
}

fn mode(bit: u64) -> Expr {
    binary(BinaryOp::And, reg(0), Expr::Const(bit))
}

fn result() -> Assignment {
    set(5, binary(BinaryOp::Xor, reg(3), reg(4)))
}

// A peeled inner iteration and the inner loop share the mark-update exit.
// Both ordinary exits contain observable work before an outer transfer.
// With shared_final, their final calculation is another shared tail and the
// public two-copy strategy fails before it can finish the whole function.
fn nested(shared_final: bool) -> Program {
    use Control::{Jump, Return};
    let blocks = vec![
        (
            vec![
                set(1, Expr::Const(0)),
                set(3, Expr::Const(0)),
                set(4, Expr::Const(0)),
            ],
            Jump(1),
        ),
        (
            vec![set(2, Expr::Const(0)), add(3, 1), store(0, 3), result()],
            branch(mode(1), 15),
        ),
        (vec![], branch(mode(8), 12)),
        (vec![set(2, Expr::Const(1))], Jump(4)),
        (
            vec![set(4, binary(BinaryOp::Add, reg(4), reg(3)))],
            branch(binary(BinaryOp::Ult, reg(2), Expr::Const(3)), 7),
        ),
        (
            vec![
                set(4, binary(BinaryOp::Add, reg(4), reg(1))),
                store(8, 4),
                add(1, 1),
            ],
            branch(binary(BinaryOp::Ult, reg(1), Expr::Const(3)), 1),
        ),
        (vec![result()], Jump(15)),
        (
            vec![add(2, 1), add(3, 2), store(0, 3), result()],
            branch(mode(4), 15),
        ),
        (vec![], branch(mode(2), 12)),
        (vec![], Jump(4)),
        (vec![], Return(Expr::Const(10))),
        (vec![], Return(Expr::Const(11))),
        (
            vec![
                set(4, binary(BinaryOp::Xor, reg(4), reg(2))),
                set(4, binary(BinaryOp::Add, reg(4), reg(1))),
                store(8, 4),
                add(1, 1),
            ],
            branch(binary(BinaryOp::Ult, reg(1), Expr::Const(3)), 1),
        ),
        if shared_final {
            (vec![], Jump(6))
        } else {
            (vec![result()], Jump(15))
        },
        (vec![], Return(Expr::Const(14))),
        (vec![store(0, 3), store(8, 4)], Return(reg(5))),
    ];
    Program::new(
        0,
        6,
        blocks
            .into_iter()
            .enumerate()
            .map(|(address, (assignments, control))| IrInstruction {
                address: address as u64,
                size: 1,
                assignments,
                control,
            })
            .collect(),
    )
    .unwrap()
}

fn compare_prefixes(program: &Program, function: &StructuredFunction) {
    assert_eq!(
        structure_verify::validate(program, function.body()).unwrap(),
        function.evidence()
    );
    let steps = bounded_steps(program, &program.cfg().reachable_blocks()).unwrap();
    assert!(function.evidence.compared_copies <= steps * 2);
    for mode in 0..16 {
        let input = [mode, 99, 98, 97, 96, 95];
        for size in [0, 8, 16] {
            let memory = vec![0xa5; size];
            for limit in 0..96 {
                assert_eq!(
                    program.run_with_memory(&input, 0x1000, &memory, limit),
                    function.run_with_memory(&input, 0x1000, &memory, limit),
                    "mode={mode}, memory={size}, limit={limit}"
                );
            }
        }
    }
}

#[test]
fn alternative_follow_recovers_copy_failure_without_changing_public_policy() {
    let program = nested(true);
    let baseline = StructuredFunction::recover(&program).unwrap_err();
    assert!(matches!(
        baseline,
        StructureError::CopyLimit { limit: 2, .. }
    ));
    let function = StructuredFunction::recover_for_readable(&program).unwrap();
    assert_eq!(StructuredFunction::recover(&program).unwrap_err(), baseline);
    compare_prefixes(&program, &function);
}

#[test]
fn successful_primary_is_replaced_only_with_fewer_steps_and_copies() {
    let program = nested(false);
    let baseline = StructuredFunction::recover(&program).unwrap();
    let function = StructuredFunction::recover_for_readable(&program).unwrap();
    assert!(function.stats.emitted_block_copies < baseline.stats.emitted_block_copies);
    assert!(function.evidence.compared_copies < baseline.evidence.compared_copies);
    let public = StructuredFunction::recover(&program).unwrap();
    assert_eq!(public.body(), baseline.body());
    assert_eq!(public.stats(), baseline.stats());
    compare_prefixes(&program, &function);
}

fn chain() -> Program {
    Program::new(
        0,
        1,
        (0..20)
            .map(|address| IrInstruction {
                address,
                size: 1,
                assignments: vec![],
                control: if address == 19 {
                    Control::Return(reg(0))
                } else {
                    Control::Jump(address + 1)
                },
            })
            .collect(),
    )
    .unwrap()
}

#[test]
fn discovery_excludes_ancestor_boundaries_and_caps_single_overrides() {
    let program = chain();
    let id = |address| program.cfg().block_at(address).unwrap();
    let contexts = [LoopContext {
        header: id(0),
        body: (0..19).map(id).collect(),
        exits: BTreeSet::from([id(19)]),
        follow: Some(id(19)),
    }];
    let exits = (0..20).filter(|&address| address != 1).map(id).collect();
    let mut plan = FollowPlan::default();
    assert_eq!(
        plan.select(id(1), &exits, &contexts, Ok(Some(id(19)))),
        Ok(Some(id(19)))
    );
    assert_eq!(
        plan.candidates,
        (2..10).map(|exit| (id(1), id(exit))).collect::<Vec<_>>()
    );
    // Repeated copies of the same natural loop do not consume more attempts.
    plan.select(id(1), &exits, &contexts, Ok(Some(id(19))))
        .unwrap();
    assert_eq!(plan.candidates.len(), MAX_CANDIDATES);
    for boundary in [id(0), id(19)] {
        let mut chosen = FollowPlan {
            chosen: Some((id(1), boundary)),
            candidates: Vec::new(),
        };
        assert_eq!(
            chosen.select(id(1), &exits, &contexts, Ok(Some(id(19)))),
            Ok(Some(id(19)))
        );
    }
}

#[test]
fn optional_syntax_budget_counts_reachable_assignments_and_expression_depth() {
    let program = nested(false);
    let mut instructions = program.instructions().to_vec();
    instructions.push(IrInstruction {
        address: 100,
        size: 1,
        assignments: vec![set(0, Expr::Const(0)); MAX_SYNTAX],
        control: Control::Return(reg(0)),
    });
    let unreachable = Program::new(0, 6, instructions).unwrap();
    assert_eq!(
        bounded_steps(&program, &program.cfg().reachable_blocks()),
        bounded_steps(&unreachable, &unreachable.cfg().reachable_blocks())
    );
    let oversized = Program::new(100, 6, unreachable.instructions().to_vec()).unwrap();
    assert!(bounded_steps(&oversized, &oversized.cfg().reachable_blocks()).is_none());
    let mut expression = Expr::Const(0);
    for _ in 0..=MAX_DEPTH {
        expression = Expr::Load {
            address: Box::new(expression),
            width: Width::U64,
        };
    }
    let mut remaining = MAX_SYNTAX;
    assert!(bounded_expression(&expression, &mut remaining).is_none());
}

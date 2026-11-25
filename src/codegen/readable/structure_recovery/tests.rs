use super::*;
use crate::control_flow::structure::Node;
use crate::control_flow::structure_verify;
use crate::model::ir::{
    AccessKind, Assignment, BinaryOp, IrInstruction, Reg, RunStatus, UnaryOp, Width,
};
use std::collections::BTreeMap;

fn r(index: usize) -> Expr {
    Expr::Register(Reg(index))
}

fn c(value: u64) -> Expr {
    Expr::Const(value)
}

fn b(op: BinaryOp, left: Expr, right: Expr) -> Expr {
    Expr::binary(op, left, right)
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

/// Several distinct exits of a bounded loop share a tail before the common
/// follow. Direct latch-to-follow exits prevent hoisting that tail wholesale.
fn shared_exit(arms: usize, tail_len: usize, memory: bool) -> Program {
    assert!(arms > 0 && arms < 64 && tail_len > 0);
    let follow = arms as u64 + 2;
    let tail = follow + 1;
    let mut source = vec![ins(
        0,
        vec![set(1, b(BinaryOp::And, r(3), c(3)))],
        Control::Jump(1),
    )];
    for index in 0..arms {
        let assignments = if index == 0 {
            vec![set(1, b(BinaryOp::Add, r(1), c(1)))]
        } else {
            Vec::new()
        };
        source.push(ins(
            index as u64 + 1,
            assignments,
            Control::Branch {
                condition: b(BinaryOp::And, r(0), c(1 << index)),
                target: tail,
            },
        ));
    }
    source.push(ins(
        arms as u64 + 1,
        vec![],
        Control::Branch {
            condition: b(BinaryOp::Ult, r(1), c(8)),
            target: 1,
        },
    ));
    source.push(ins(follow, vec![], Control::Return(r(2))));
    for index in 0..tail_len {
        let assignments = if index == 0 && memory {
            vec![
                Assignment {
                    destination: Place::Memory {
                        address: r(4),
                        width: Width::U64,
                    },
                    value: r(1),
                },
                set(2, Expr::load(b(BinaryOp::Add, r(4), c(8)), Width::U16)),
            ]
        } else {
            vec![set(
                2,
                if index == 0 {
                    r(1)
                } else {
                    b(BinaryOp::Add, r(2), c(1))
                },
            )]
        };
        source.push(ins(
            tail + index as u64,
            assignments,
            if index + 1 == tail_len {
                Control::Jump(follow)
            } else {
                Control::Next
            },
        ));
    }
    Program::new(0, 5, source).unwrap()
}

fn copies(nodes: &[Node]) -> BTreeMap<u64, usize> {
    let mut result = BTreeMap::new();
    let mut pending: Vec<_> = nodes.iter().collect();
    while let Some(node) = pending.pop() {
        match node {
            Node::Step { address, .. } => *result.entry(*address).or_insert(0) += 1,
            Node::If {
                taken, not_taken, ..
            } => pending.extend(taken.iter().chain(not_taken)),
            Node::Loop(body) => pending.extend(body),
            _ => {}
        }
    }
    result
}

fn deep(depth: usize) -> Expr {
    let mut expression = r(1);
    for _ in 0..depth {
        expression = Expr::unary(UnaryOp::SignExtend(Width::U64), expression);
    }
    expression
}

fn balanced(depth: usize) -> Expr {
    if depth == 0 {
        c(1)
    } else {
        b(BinaryOp::Add, balanced(depth - 1), balanced(depth - 1))
    }
}

#[test]
fn short_shared_exit_uses_more_local_copies_within_the_original_total_bound() {
    let source = shared_exit(3, 1, false);
    let before = source.instructions().to_vec();
    assert!(matches!(
        StructuredFunction::recover(&source),
        Err(StructureError::CopyLimit { limit: 2, .. })
    ));
    let recovered = recover(&source).unwrap();
    let counts = copies(recovered.body());
    assert_eq!(counts[&6], 3);
    assert!(counts.values().all(|&n| n <= MAX_LOCAL_COPIES));
    assert!(counts.values().sum::<usize>() <= source.instructions().len() * 2);
    assert_eq!(
        structure_verify::validate(&source, recovered.body()).unwrap(),
        recovered.evidence()
    );
    assert_eq!(source.instructions(), before);
    // The public/core policy remains at two copies even after readable recovery.
    assert!(matches!(
        StructuredFunction::recover(&source),
        Err(StructureError::CopyLimit { limit: 2, .. })
    ));
}

#[test]
fn recovered_copies_keep_complete_prefix_register_memory_trace_and_first_fault_state() {
    let source = shared_exit(3, 1, true);
    let recovered = recover(&source).unwrap();
    let memory: Vec<_> = (0..16).map(|n| (n * 7 + 3) as u8).collect();
    let mut returns = 0;
    let mut read_faults = 0;
    let mut write_faults = 0;
    let mut suspended = 0;
    for flags in 0..8 {
        for seed in [0, 1, 3, u64::MAX] {
            for address in [0x1000, 0x1008, 0x100f, u64::MAX] {
                let registers = [flags, 99, 7, seed, address];
                for budget in 0..40 {
                    let original = source
                        .run_with_memory(&registers, 0x1000, &memory, budget)
                        .unwrap();
                    let actual = recovered
                        .run_with_memory(&registers, 0x1000, &memory, budget)
                        .unwrap();
                    assert_eq!(
                        actual, original,
                        "flags={flags} seed={seed} address={address:#x} budget={budget}"
                    );
                    match original.status {
                        RunStatus::Returned(_) => returns += 1,
                        RunStatus::Suspended => suspended += 1,
                        RunStatus::Fault(fault) => match fault.access {
                            AccessKind::Read => read_faults += 1,
                            AccessKind::Write => write_faults += 1,
                        },
                    }
                }
            }
        }
    }
    assert!(returns > 0 && suspended > 0 && read_faults > 0 && write_faults > 0);
}

#[test]
fn long_shared_tail_cannot_exceed_twice_the_reachable_original_steps() {
    let source = shared_exit(3, 16, false);
    let baseline = StructuredFunction::recover(&source).unwrap_err();
    assert!(matches!(
        baseline,
        StructureError::CopyLimit { limit: 2, .. }
    ));
    let unbounded =
        StructuredFunction::recover_with_step_limit(&source, MAX_LOCAL_COPIES, usize::MAX).unwrap();
    assert!(unbounded.evidence().compared_copies > source.instructions().len() * 2);
    assert_eq!(recover(&source).unwrap_err(), baseline);
}

#[test]
fn the_local_cap_is_independent_of_available_total_steps() {
    let source = shared_exit(9, 1, false);
    let baseline = StructuredFunction::recover(&source).unwrap_err();
    assert!(matches!(
        baseline,
        StructureError::CopyLimit { limit: 2, .. }
    ));
    assert!(matches!(
        StructuredFunction::recover_with_step_limit(&source, MAX_LOCAL_COPIES, usize::MAX),
        Err(StructureError::CopyLimit {
            limit: MAX_LOCAL_COPIES,
            ..
        })
    ));
    assert_eq!(recover(&source).unwrap_err(), baseline);
}

#[test]
fn existing_success_is_not_subject_to_the_optional_expression_depth_guard() {
    let source = Program::new(
        0,
        2,
        vec![ins(0, vec![], Control::Return(deep(MAX_EXPRESSION_DEPTH)))],
    )
    .unwrap();
    assert_eq!(retry_step_limit(&source), None);
    let baseline = StructuredFunction::recover(&source).unwrap();
    let recovered = recover(&source).unwrap();
    assert_eq!(baseline.body(), recovered.body());
    assert_eq!(baseline.evidence(), recovered.evidence());
    assert_eq!(baseline.stats(), recovered.stats());
}

#[test]
fn depth_guard_applies_only_after_copy_failure_and_covers_nested_loads_and_lazy_arms() {
    assert!(
        Syntax(MAX_SYNTAX_ITEMS)
            .expression(&deep(MAX_EXPRESSION_DEPTH - 1))
            .is_some()
    );
    for expression in [
        deep(MAX_EXPRESSION_DEPTH),
        Expr::load(deep(MAX_EXPRESSION_DEPTH), Width::U8),
        Expr::select(c(1), r(1), deep(MAX_EXPRESSION_DEPTH)),
    ] {
        let original = shared_exit(3, 1, false);
        let mut instructions = original.instructions().to_vec();
        instructions.last_mut().unwrap().assignments[0].value = expression;
        let source = Program::new(0, 5, instructions).unwrap();
        let baseline = StructuredFunction::recover(&source).unwrap_err();
        assert!(matches!(
            baseline,
            StructureError::CopyLimit { limit: 2, .. }
        ));
        assert_eq!(retry_step_limit(&source), None);
        assert_eq!(recover(&source).unwrap_err(), baseline);
    }
}

#[test]
fn syntax_weight_counts_instructions_assignments_and_all_expression_occurrences() {
    // A depth-15 binary tree has 65,535 Expr nodes: one instruction fits the
    // complete 65,536 item bound exactly; an assignment and return no longer do.
    let source = Program::new(0, 0, vec![ins(0, vec![], Control::Return(balanced(15)))]).unwrap();
    assert_eq!(retry_step_limit(&source), Some(2));
    for destination in [
        Place::Register(Reg(0)),
        Place::Memory {
            address: balanced(15),
            width: Width::U8,
        },
    ] {
        let value = if matches!(destination, Place::Register(_)) {
            balanced(15)
        } else {
            c(0)
        };
        let source = Program::new(
            0,
            1,
            vec![ins(
                0,
                vec![Assignment { destination, value }],
                Control::Return(c(0)),
            )],
        )
        .unwrap();
        assert_eq!(retry_step_limit(&source), None);
    }
}

#[test]
fn unreachable_expression_weight_and_steps_do_not_spend_the_retry_allowance() {
    let original = shared_exit(3, 1, false);
    let mut instructions = original.instructions().to_vec();
    instructions.push(ins(
        100,
        vec![],
        Control::Return(deep(MAX_EXPRESSION_DEPTH)),
    ));
    let source = Program::new(0, 5, instructions).unwrap();
    assert_eq!(
        retry_step_limit(&source),
        Some(original.instructions().len() * 2)
    );
    let recovered = recover(&source).unwrap();
    assert_eq!(
        recovered.evidence().original_steps,
        original.instructions().len()
    );
    assert!(!copies(recovered.body()).contains_key(&100));
}

#[test]
fn irreducible_failures_keep_the_original_recovery_policy() {
    // Both entries to the irreducible cycle need more than the splitter's
    // eight-step entry-copy bound, so the baseline error is not CopyLimit.
    let mut instructions = vec![ins(
        0,
        vec![],
        Control::Branch {
            condition: r(0),
            target: 11,
        },
    )];
    instructions.extend((1..20).map(|pc| ins(pc, vec![], Control::Next)));
    instructions.push(ins(
        20,
        vec![],
        Control::Branch {
            condition: r(1),
            target: 1,
        },
    ));
    instructions.push(ins(21, vec![], Control::Return(c(0))));
    let source = Program::new(0, 2, instructions).unwrap();
    let baseline = StructuredFunction::recover(&source).unwrap_err();
    assert_eq!(baseline, StructureError::Irreducible);
    assert_eq!(recover(&source).unwrap_err(), baseline);
}

#[test]
fn readable_source_and_display_evidence_remain_bound_to_their_own_programs() {
    let source = shared_exit(3, 1, true);
    let kept = super::super::webs::keep_original(&source, super::super::WebRecovery::Unchanged);
    let kept_structure = kept.structure.as_ref().unwrap();
    assert_eq!(kept.source_evidence, Some(kept_structure.evidence()));
    assert_eq!(kept.source_stats, Some(kept_structure.stats()));
    let selected = super::super::webs::select(&source);
    assert_eq!(selected.source_evidence, kept.source_evidence);
    assert_eq!(selected.source_stats, kept.source_stats);
    let displayed = selected.program.as_ref().unwrap_or(&source);
    let structure = selected.structure.as_ref().unwrap();
    assert_eq!(
        structure_verify::validate(displayed, structure.body()).unwrap(),
        structure.evidence()
    );

    let readable = super::super::emit_readable_c(&source).unwrap();
    assert!(readable.fallback_reason.is_none(), "{}", readable.code);
    assert!(readable.structure_evidence.is_some());
    assert!(readable.structure_stats.is_some());
    assert!(readable.display_structure_evidence.is_some());
    let core = crate::codegen::emit::emit_c(&source).unwrap();
    assert!(matches!(
        core.fallback_reason,
        Some(StructureError::CopyLimit { limit: 2, .. })
    ));
}

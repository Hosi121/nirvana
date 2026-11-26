use nirvana::analysis::ControlFlowAnalysis;
use nirvana::ir::{
    Assignment, BinaryOp as B, Control, Expr, IrInstruction, Place, Program, Reg, Width,
};
use nirvana::structure::{Node, StructureError, StructuredFunction};
use nirvana::structure_verify::{validate, validate_reentries};

use crate::support::ir::c;
use crate::support::ir::r;
fn b(op: B, a: Expr, d: Expr) -> Expr {
    Expr::binary(op, a, d)
}
fn set(n: usize, value: Expr) -> Assignment {
    Assignment {
        destination: Reg(n).into(),
        value,
    }
}
fn increment(n: usize) -> Assignment {
    set(n, b(B::Add, r(n), c(1)))
}
fn ins(address: u64, assignments: Vec<Assignment>, control: Control) -> IrInstruction {
    IrInstruction {
        address,
        size: 1,
        assignments,
        control,
    }
}

fn cycle(base: u64, memory: bool) -> Program {
    let mut body = vec![increment(1)];
    if memory {
        body.extend([
            Assignment {
                destination: Place::Memory {
                    address: r(2),
                    width: Width::U8,
                },
                value: r(1),
            },
            set(3, Expr::load(b(B::Add, r(2), c(1)), Width::U64)),
        ]);
    }
    Program::new(
        base,
        4,
        vec![
            ins(
                base,
                vec![],
                Control::Branch {
                    condition: r(0),
                    target: base + 2,
                },
            ),
            ins(base + 1, body, Control::Jump(base + 2)),
            ins(
                base + 2,
                vec![set(0, b(B::Sub, r(0), c(1)))],
                Control::Branch {
                    condition: b(B::Ult, r(1), c(4)),
                    target: base + 1,
                },
            ),
            ins(base + 3, vec![], Control::Return(r(1))),
        ],
    )
    .unwrap()
}

fn check(program: &Program, function: &StructuredFunction, inputs: &[[u64; 4]]) -> usize {
    assert!(
        !ControlFlowAnalysis::compute(program.cfg())
            .unwrap()
            .is_reducible()
    );
    assert!(function.split_evidence().is_some());
    assert_eq!(
        validate(program, function.body()).unwrap(),
        function.evidence()
    );
    validate_reentries(program, function.body()).unwrap();
    assert!(function.stats().emitted_block_copies <= function.stats().unique_blocks * 2);
    let memory: Vec<u8> = (0..32).collect();
    for input in inputs {
        for budget in 0..48 {
            assert_eq!(
                program
                    .run_with_memory(input, 4096, &memory, budget)
                    .unwrap(),
                function
                    .run_with_memory(input, 4096, &memory, budget)
                    .unwrap(),
                "input={input:?}, budget={budget}"
            );
        }
    }
    inputs.len() * 48
}

#[test]
fn splitting_restores_original_pcs_full_state_traces_and_reentry_correspondence() {
    for base in [0, 1000, u64::MAX - 8] {
        let source = cycle(base, false);
        let before = source.instructions().to_vec();
        let recovered = StructuredFunction::recover(&source).unwrap();
        let inputs = [
            [0, 0, 0, 0],
            [1, 0, 0, 0],
            [2, 3, 0, 0],
            [u64::MAX, u64::MAX, 0, 0],
        ];
        assert_eq!(check(&source, &recovered, &inputs), 192);
        assert_eq!(source.instructions(), before);
        assert_eq!(
            recovered.body(),
            StructuredFunction::recover(&source).unwrap().body()
        );
        assert_eq!(
            recovered.split_evidence(),
            StructuredFunction::recover(&source)
                .unwrap()
                .split_evidence()
        );
    }
}

#[test]
fn copied_loads_stores_and_faulting_conditions_keep_order_and_all_prior_writes() {
    let mut cases = Vec::new();
    for condition_load in [false, true] {
        let source = cycle(0, true);
        let mut instructions = source.instructions().to_vec();
        if condition_load {
            instructions[2].control = Control::Branch {
                condition: b(B::Ult, r(1), Expr::load(r(2), Width::U8)),
                target: 1,
            };
        }
        cases.push(Program::new(0, 4, instructions).unwrap());
    }
    let mut inputs = Vec::new();
    for start in [0, 1, 2, u64::MAX] {
        for address in [4096, 4120, 4127, 4095, u64::MAX] {
            inputs.push([start, 0, address, 0]);
        }
    }
    for source in cases {
        let recovered = StructuredFunction::recover(&source).unwrap();
        assert_eq!(check(&source, &recovered, &inputs), 960);
    }
}

#[test]
fn irreducible_cycle_inside_an_outer_loop_preserves_the_outer_loop() {
    let source = Program::new(
        0,
        4,
        vec![
            ins(0, vec![set(3, c(0))], Control::Jump(1)),
            ins(
                1,
                vec![set(2, c(0))],
                Control::Branch {
                    condition: r(0),
                    target: 3,
                },
            ),
            ins(2, vec![increment(1)], Control::Jump(3)),
            ins(
                3,
                vec![increment(2)],
                Control::Branch {
                    condition: b(B::Ult, r(2), c(3)),
                    target: 2,
                },
            ),
            ins(
                4,
                vec![increment(3)],
                Control::Branch {
                    condition: b(B::Ult, r(3), c(2)),
                    target: 1,
                },
            ),
            ins(5, vec![], Control::Return(r(1))),
        ],
    )
    .unwrap();
    let recovered = StructuredFunction::recover(&source).unwrap();
    check(
        &source,
        &recovered,
        &[[0, 0, 0, 0], [1, 0, 0, 0], [u64::MAX, u64::MAX, 0, 0]],
    );
    fn loops(nodes: &[Node]) -> usize {
        nodes
            .iter()
            .map(|n| match n {
                Node::Loop(body) => 1 + loops(body),
                Node::If {
                    taken, not_taken, ..
                } => loops(taken) + loops(not_taken),
                _ => 0,
            })
            .sum()
    }
    assert!(loops(recovered.body()) >= 2);
}

#[test]
fn original_copy_and_step_limits_remain_acceptance_conditions() {
    let source = cycle(0, false);
    for copies in [0, 1] {
        assert_eq!(
            StructuredFunction::recover_with_copy_limit(&source, copies).unwrap_err(),
            StructureError::Irreducible
        );
    }
    let recovered = StructuredFunction::recover(&source).unwrap();
    let exact = recovered.evidence().compared_copies;
    assert!(StructuredFunction::recover_with_step_limit(&source, 2, exact - 1).is_err());
    let bounded = StructuredFunction::recover_with_step_limit(&source, 2, exact).unwrap();
    assert_eq!(bounded.evidence().compared_copies, exact);
}

#[test]
fn copied_multistep_block_keeps_internal_fallthroughs_and_partial_fault_state() {
    let source = Program::new(
        0,
        4,
        vec![
            ins(
                0,
                vec![],
                Control::Branch {
                    condition: r(0),
                    target: 4,
                },
            ),
            ins(1, vec![increment(1)], Control::Next),
            ins(2, vec![set(3, Expr::load(r(2), Width::U8))], Control::Next),
            ins(
                3,
                vec![Assignment {
                    destination: Place::Memory {
                        address: b(B::Add, r(2), c(1)),
                        width: Width::U8,
                    },
                    value: r(1),
                }],
                Control::Jump(4),
            ),
            ins(4, vec![set(0, b(B::Sub, r(0), c(1)))], Control::Next),
            ins(5, vec![set(3, b(B::Xor, r(3), r(0)))], Control::Next),
            ins(6, vec![set(3, b(B::Add, r(3), r(1)))], Control::Next),
            ins(
                7,
                vec![],
                Control::Branch {
                    condition: b(B::Ult, r(1), c(4)),
                    target: 1,
                },
            ),
            ins(8, vec![], Control::Return(r(3))),
        ],
    )
    .unwrap();
    let recovered = StructuredFunction::recover(&source).unwrap();
    assert_eq!(recovered.split_evidence().unwrap().copied_steps, 3);
    check(
        &source,
        &recovered,
        &[
            [0, 0, 4096, 0],
            [1, 0, 4096, 0],
            [0, 0, 4127, 0],
            [1, 0, 4095, 0],
        ],
    );
}

fn consecutive_cycles(count: usize) -> Program {
    let mut instructions = Vec::new();
    for index in 0..count {
        let mut part = cycle((index * 4) as u64, false).instructions().to_vec();
        if index + 1 < count {
            part[3].control = Control::Jump(((index + 1) * 4) as u64);
        }
        instructions.extend(part);
    }
    Program::new(0, 4, instructions).unwrap()
}

#[test]
fn independent_cycles_keep_source_history_full_state_and_exact_budgets() {
    for count in [2, 3] {
        let source = consecutive_cycles(count);
        let before = source.instructions().to_vec();
        let recovered = StructuredFunction::recover(&source).unwrap();
        assert_eq!(source.instructions(), before);
        assert_eq!(recovered.split_sites().len(), count);
        let summary = recovered.split_evidence().unwrap();
        assert_eq!(
            summary.copied_steps,
            recovered
                .split_sites()
                .iter()
                .map(|site| site.copied_steps)
                .sum()
        );
        assert!(summary.copied_steps <= 8 && summary.attempted_candidates <= 16);
        check(
            &source,
            &recovered,
            &[[0, 0, 4096, 0], [1, 0, 4096, 0], [u64::MAX, 0, 4127, 0]],
        );
        assert!(
            nirvana::emit::emit_c(&source)
                .unwrap()
                .fallback_reason
                .is_none()
        );
    }
}

#[test]
fn too_many_independent_cycles_retain_the_checked_fallback() {
    let source = consecutive_cycles(9);
    assert_eq!(
        StructuredFunction::recover(&source).unwrap_err(),
        StructureError::Irreducible
    );
    assert!(
        nirvana::emit::emit_c(&source)
            .unwrap()
            .fallback_reason
            .is_some()
    );
}

#[test]
fn long_entry_blocks_and_oversized_whole_input_decline_atomically() {
    let mut instructions = vec![ins(
        0,
        vec![],
        Control::Branch {
            condition: r(0),
            target: 20,
        },
    )];
    for (start, end, target) in [(1, 10, 20), (20, 29, 1)] {
        for pc in start..end {
            instructions.push(ins(pc, vec![increment(1)], Control::Next));
        }
        instructions.push(ins(
            end,
            vec![increment(1)],
            if start == 1 {
                Control::Jump(target)
            } else {
                Control::Branch {
                    condition: r(0),
                    target,
                }
            },
        ));
    }
    instructions.push(ins(30, vec![], Control::Return(r(1))));
    let source = Program::new(0, 4, instructions).unwrap();
    let before = source.instructions().to_vec();
    assert!(StructuredFunction::recover(&source).is_err());
    assert_eq!(source.instructions(), before);
    let small = cycle(0, false);
    let large = Program::new(0, 4097, small.instructions().to_vec()).unwrap();
    assert_eq!(
        StructuredFunction::recover(&large).unwrap_err(),
        StructureError::Irreducible
    );
}

#[test]
fn restored_copies_are_rechecked_against_the_source_not_only_the_proposal() {
    let source = cycle(0, false);
    let recovered = StructuredFunction::recover(&source).unwrap();
    let mut changed = recovered.body().to_vec();
    fn alter(nodes: &mut [Node]) -> bool {
        for n in nodes {
            match n {
                Node::Step { assignments, .. } if !assignments.is_empty() => {
                    assignments[0].value = c(123);
                    return true;
                }
                Node::If {
                    taken, not_taken, ..
                } => {
                    if alter(taken) || alter(not_taken) {
                        return true;
                    }
                }
                Node::Loop(body) => {
                    if alter(body) {
                        return true;
                    }
                }
                _ => {}
            }
        }
        false
    }
    assert!(alter(&mut changed));
    assert!(validate(&source, &changed).is_err());
}

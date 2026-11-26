//! Bounded implementation audit: real recovery/checker/executors, no model VM.
use super::*;
use crate::model::ir::{BinaryOp, IrInstruction, Place, Reg, Width};
use std::collections::BTreeMap;
use std::fmt::Write as _;

fn r(index: usize) -> Expr {
    Expr::Register(Reg(index))
}
fn k(value: u64) -> Expr {
    Expr::Const(value)
}
fn binary(op: BinaryOp, left: Expr, right: Expr) -> Expr {
    Expr::binary(op, left, right)
}
fn assign(index: usize, value: Expr) -> Assignment {
    Assignment {
        destination: Reg(index).into(),
        value,
    }
}
fn store(address: Expr, value: Expr) -> Assignment {
    Assignment {
        destination: Place::Memory {
            address,
            width: Width::U8,
        },
        value,
    }
}
fn program(mut graph: usize, profile: usize) -> Program {
    let mut instructions = Vec::new();
    for pc in 0..4u64 {
        let mut assignments = Vec::new();
        match (profile, pc) {
            (1, 1) => {
                assignments.push(assign(2, binary(BinaryOp::Add, r(2), r(0))));
                assignments.push(assign(0, binary(BinaryOp::Sub, r(0), k(1))));
            }
            (1, 2) => {
                assignments.push(store(r(1), r(2)));
                assignments.push(assign(1, binary(BinaryOp::Add, r(1), k(1))));
            }
            (2, 0) => {
                assignments.push(store(r(1), k(0x7f)));
                assignments.push(store(
                    binary(BinaryOp::Add, r(1), k(1)),
                    Expr::load(binary(BinaryOp::Add, r(1), k(2)), Width::U8),
                ));
            }
            (2, 1) => assignments.push(assign(0, binary(BinaryOp::Sub, r(0), k(1)))),
            (2, 2) => assignments.push(assign(
                2,
                Expr::select(
                    k(0),
                    Expr::load(k(u64::MAX), Width::U64),
                    binary(BinaryOp::Add, r(2), k(1)),
                ),
            )),
            _ => {}
        }
        let choice = if pc == 3 {
            9
        } else {
            let x = graph % 10;
            graph /= 10;
            x
        };
        let control = match choice {
            0 => Control::Next,
            1..=4 => Control::Jump(choice as u64 - 1),
            5..=8 => Control::Branch {
                condition: if profile == 2 {
                    Expr::select(r(0), Expr::load(r(1), Width::U8), k(0))
                } else {
                    r(0)
                },
                target: choice as u64 - 5,
            },
            _ => Control::Return(r(2)),
        };
        instructions.push(IrInstruction {
            address: pc,
            size: 1,
            assignments,
            control,
        });
    }
    Program::new(0, 3, instructions).unwrap()
}

fn run_ast(nodes: &[Node], input: &[u64], memory: &[u8], budget: usize) -> RunReport {
    let mut machine = Machine::with_memory(3, input, 0, memory, budget).unwrap();
    let result = match execute_nodes(nodes, &mut machine) {
        Ok(Signal::Return(value)) => Ok(value),
        Err(stop) => Err(stop),
        _ => panic!("accepted AST leaked a loop transfer or fell through"),
    };
    machine.finish(result)
}

fn mutate(nodes: &mut Vec<Node>, kind: usize) -> bool {
    let mut index = 0;
    while index < nodes.len() {
        let node = &mut nodes[index];
        match (kind, &mut *node) {
            (
                0,
                Node::If {
                    taken, not_taken, ..
                },
            ) if taken != not_taken => {
                std::mem::swap(taken, not_taken);
                return true;
            }
            (1, Node::Step { .. }) => {
                nodes.remove(index);
                return true;
            }
            (2, Node::Step { assignments, .. }) if assignments.len() > 1 => {
                assignments.reverse();
                return true;
            }
            (3, Node::Return(value)) => {
                *value = k(u64::MAX);
                return true;
            }
            (4, Node::Evaluate(_)) => {
                nodes.remove(index);
                return true;
            }
            (5, Node::Break) => {
                *node = Node::Continue;
                return true;
            }
            (5, Node::Continue) => {
                *node = Node::Break;
                return true;
            }
            (5, Node::BreakOuter { levels } | Node::ContinueOuter { levels }) => {
                *levels += 1;
                return true;
            }
            _ => {}
        }
        let changed = match node {
            Node::If {
                taken, not_taken, ..
            } => mutate(taken, kind) || mutate(not_taken, kind),
            Node::Loop(body) => mutate(body, kind),
            _ => false,
        };
        if changed {
            return true;
        }
        index += 1;
    }
    false
}

fn divergent_arm() -> (Program, Vec<Node>) {
    // if (r0) return r2; else for (;;) original_step_1();
    let source = Program::new(
        0,
        3,
        vec![
            IrInstruction {
                address: 0,
                size: 1,
                assignments: vec![],
                control: Control::Branch {
                    condition: r(0),
                    target: 2,
                },
            },
            IrInstruction {
                address: 1,
                size: 1,
                assignments: vec![],
                control: Control::Jump(1),
            },
            IrInstruction {
                address: 2,
                size: 1,
                assignments: vec![],
                control: Control::Return(r(2)),
            },
        ],
    )
    .unwrap();
    let step = |address| Node::Step {
        address,
        assignments: vec![],
    };
    let body = vec![
        step(0),
        Node::If {
            condition: r(0),
            taken: vec![step(2), Node::Return(r(2))],
            not_taken: vec![Node::Loop(vec![step(1)])],
        },
    ];
    (source, body)
}

#[test]
fn divergent_arm_has_a_valid_structured_witness_with_exact_rust_reports() {
    let (source, body) = divergent_arm();
    assert!(
        ControlFlowAnalysis::compute(source.cfg())
            .unwrap()
            .is_reducible()
    );
    let evidence = structure_verify::validate(&source, &body).unwrap();
    assert_eq!(evidence.original_steps, 3);
    for counter in [0, 1, 2, u64::MAX] {
        for budget in 0..=8 {
            let input = [counter, 0, 0x55];
            assert_eq!(
                source.run_with_memory(&input, 0, &[], budget).unwrap(),
                run_ast(&body, &input, &[], budget)
            );
        }
    }
    println!(
        "constructive structured witness: {evidence:?}; recovery={:?}",
        StructuredFunction::recover(&source).map(|f| f.stats())
    );
}

#[test]
fn mixed_return_and_divergent_loop_exits_have_a_structured_witness() {
    let source = program(358, 0);
    let step = |address| Node::Step {
        address,
        assignments: vec![],
    };
    let body = vec![Node::Loop(vec![
        step(0),
        Node::If {
            condition: r(0),
            taken: vec![step(3), Node::Return(r(2))],
            not_taken: vec![],
        },
        step(1),
        Node::If {
            condition: r(0),
            taken: vec![Node::Continue],
            not_taken: vec![Node::Loop(vec![step(2)])],
        },
    ])];
    assert!(
        ControlFlowAnalysis::compute(source.cfg())
            .unwrap()
            .is_reducible()
    );
    let evidence = structure_verify::validate(&source, &body).unwrap();
    assert_eq!(evidence.original_steps, 4);
    for counter in [0, 1, 2, u64::MAX] {
        for budget in 0..=8 {
            let input = [counter, 0, 0x55];
            assert_eq!(
                source.run_with_memory(&input, 0, &[], budget).unwrap(),
                run_ast(&body, &input, &[], budget)
            );
        }
    }
    println!(
        "mixed-exit witness: {evidence:?}; recovery={:?}",
        StructuredFunction::recover(&source).map(|f| f.stats())
    );
    let function =
        StructuredFunction::recover(&source).expect("mixed loop exits have a structured witness");
    for counter in [0, 1, 2, u64::MAX] {
        for budget in 0..=8 {
            let input = [counter, 0, 0x55];
            assert_eq!(
                source.run_with_memory(&input, 0, &[], budget).unwrap(),
                function.run_with_memory(&input, 0, &[], budget).unwrap()
            );
        }
    }
}

#[test]
fn recovery_should_accept_a_return_or_divergent_arm() {
    let (source, body) = divergent_arm();
    structure_verify::validate(&source, &body).unwrap();
    let function =
        StructuredFunction::recover(&source).expect("a validated structured witness exists");
    for counter in [0, 1, 2, u64::MAX] {
        for budget in 0..=8 {
            let input = [counter, 0, 0x55];
            assert_eq!(
                source.run_with_memory(&input, 0, &[], budget).unwrap(),
                function.run_with_memory(&input, 0, &[], budget).unwrap()
            );
        }
    }
}

#[test]
#[ignore = "bounded 3000-CFG implementation audit; run explicitly with --ignored --exact"]
fn generated_cfgs_and_accepted_mutants_preserve_complete_rust_reports() {
    audit(1000, program);
}

fn program5(mut graph: usize, profile: usize) -> Program {
    let template = program(0, profile);
    let mut instructions = Vec::new();
    for pc in 0..5u64 {
        let assignments = template
            .instructions()
            .get(pc as usize)
            .map(|i| i.assignments.clone())
            .unwrap_or_default();
        let choice = if pc == 4 {
            11
        } else {
            let x = graph % 12;
            graph /= 12;
            x
        };
        let control = match choice {
            0 => Control::Next,
            1..=5 => Control::Jump(choice as u64 - 1),
            6..=10 => Control::Branch {
                condition: if profile == 2 {
                    Expr::select(r(0), Expr::load(r(1), Width::U8), k(0))
                } else {
                    r(0)
                },
                target: choice as u64 - 6,
            },
            _ => Control::Return(r(2)),
        };
        instructions.push(IrInstruction {
            address: pc,
            size: 1,
            assignments,
            control,
        });
    }
    Program::new(0, 3, instructions).unwrap()
}

#[test]
fn forward_latch_join_fits_one_copy_and_five_steps() {
    let source = program5(3285, 0);
    let step = |address| Node::Step {
        address,
        assignments: vec![],
    };
    let body = vec![
        Node::Loop(vec![
            step(0),
            Node::If {
                condition: r(0),
                taken: vec![],
                not_taken: vec![
                    step(1),
                    Node::If {
                        condition: r(0),
                        taken: vec![],
                        not_taken: vec![
                            step(2),
                            Node::If {
                                condition: r(0),
                                taken: vec![Node::Break],
                                not_taken: vec![],
                            },
                        ],
                    },
                ],
            },
            step(3),
        ]),
        step(4),
        Node::Return(r(2)),
    ];
    structure_verify::validate(&source, &body).unwrap();
    let function = StructuredFunction::recover_with_step_limit(&source, 1, 5)
        .expect("the shared latch has a validated one-copy, five-step tree");
    assert_eq!(function.stats().extra_block_copies, 0);
    assert_eq!(function.stats().emitted_block_copies, 5);
    for counter in [0, 1, 2, u64::MAX] {
        for budget in 0..=12 {
            let input = [counter, 0, 0x55];
            assert_eq!(
                source.run_with_memory(&input, 0, &[], budget).unwrap(),
                function.run_with_memory(&input, 0, &[], budget).unwrap()
            );
        }
    }
}

#[test]
#[ignore = "bounded 62208-program follow-up audit; run explicitly"]
fn generated_five_instruction_cfgs_preserve_complete_rust_reports() {
    audit(12usize.pow(4), program5);
}

#[test]
fn split_nested_loop_shares_its_exit_within_two_copies_and_six_steps() {
    for profile in 0..3 {
        let source = program5(2852, profile);
        let step = |address: usize| Node::Step {
            address: address as u64,
            assignments: source.instructions()[address].assignments.clone(),
        };
        let Control::Branch { condition, .. } = &source.instructions()[0].control else {
            unreachable!()
        };
        let branch = |taken, not_taken| Node::If {
            condition: condition.clone(),
            taken,
            not_taken,
        };
        let body = vec![Node::Loop(vec![
            step(0),
            branch(
                vec![step(2), branch(vec![], vec![step(3), Node::Continue])],
                vec![],
            ),
            Node::Loop(vec![
                step(1),
                branch(vec![Node::Break], vec![]),
                step(2),
                branch(vec![Node::Continue], vec![Node::Break]),
            ]),
            step(3),
        ])];
        structure_verify::validate(&source, &body).unwrap();
        let recovered = StructuredFunction::recover_with_step_limit(&source, 2, 6)
            .expect("the split inner loop has a validated two-copy, six-step tree");
        assert!(recovered.split_evidence().is_some());
        assert_eq!(recovered.evidence().compared_copies, 6);
        assert!(StructuredFunction::recover_with_step_limit(&source, 2, 5).is_err());
        assert!(StructuredFunction::recover_with_step_limit(&source, 1, 6).is_err());
        compare_split_reports(&source, &body, &recovered);
    }
}

#[test]
fn split_linear_entry_path_fits_two_copies_and_six_steps() {
    for profile in 0..3 {
        let source = program5(3572, profile);
        let step = |address: usize| Node::Step {
            address: address as u64,
            assignments: source.instructions()[address].assignments.clone(),
        };
        let Control::Branch { condition, .. } = &source.instructions()[0].control else {
            unreachable!()
        };
        let body = vec![
            step(0),
            Node::If {
                condition: condition.clone(),
                taken: vec![step(2), step(3)],
                not_taken: vec![],
            },
            Node::Loop(vec![
                step(1),
                Node::If {
                    condition: condition.clone(),
                    taken: vec![],
                    not_taken: vec![step(2)],
                },
                step(3),
            ]),
        ];
        structure_verify::validate(&source, &body).unwrap();
        let recovered = StructuredFunction::recover_with_step_limit(&source, 2, 6)
            .expect("cloning a bounded entry path produces a validated six-step tree");
        assert_eq!(recovered.split_evidence().unwrap().copied_steps, 2);
        assert_eq!(recovered.evidence().compared_copies, 6);
        assert!(StructuredFunction::recover_with_step_limit(&source, 2, 5).is_err());
        assert!(StructuredFunction::recover_with_step_limit(&source, 1, 6).is_err());
        compare_split_reports(&source, &body, &recovered);
    }
}

#[test]
fn split_loop_exits_share_a_divergent_follow_within_five_steps() {
    for profile in 0..3 {
        let source = program5(4376, profile);
        let step = |address: usize| Node::Step {
            address: address as u64,
            assignments: source.instructions()[address].assignments.clone(),
        };
        let Control::Branch { condition, .. } = &source.instructions()[0].control else {
            unreachable!()
        };
        let body = vec![
            Node::Loop(vec![
                step(0),
                Node::If {
                    condition: condition.clone(),
                    taken: vec![],
                    not_taken: vec![step(1), Node::Break],
                },
                step(2),
                Node::If {
                    condition: condition.clone(),
                    taken: vec![Node::Continue],
                    not_taken: vec![Node::Break],
                },
            ]),
            Node::Loop(vec![step(3), step(1)]),
        ];
        structure_verify::validate(&source, &body).unwrap();
        let recovered = StructuredFunction::recover_with_step_limit(&source, 2, 5)
            .expect("distinct exits share the next loop without an enclosing parent loop");
        assert_eq!(recovered.evidence().compared_copies, 5);
        assert!(StructuredFunction::recover_with_step_limit(&source, 1, 5).is_err());
        compare_split_reports(&source, &body, &recovered);
    }
}

#[test]
fn split_forward_entry_path_keeps_internal_natural_backedges() {
    for profile in 0..3 {
        let source = program5(4412, profile);
        let step = |address: usize| Node::Step {
            address: address as u64,
            assignments: source.instructions()[address].assignments.clone(),
        };
        let Control::Branch { condition, .. } = &source.instructions()[0].control else {
            unreachable!()
        };
        let branch = |taken, not_taken| Node::If {
            condition: condition.clone(),
            taken,
            not_taken,
        };
        let body = vec![Node::Loop(vec![
            step(0),
            branch(
                vec![step(2), branch(vec![Node::Continue], vec![step(3)])],
                vec![],
            ),
            Node::Loop(vec![
                step(1),
                branch(vec![Node::Continue], vec![]),
                step(2),
                branch(vec![Node::ContinueOuter { levels: 1 }], vec![]),
                step(3),
            ]),
        ])];
        structure_verify::validate(&source, &body).unwrap();
        let recovered = StructuredFunction::recover_with_step_limit(&source, 2, 6)
            .expect("a proven natural backedge does not block the forward entry path");
        assert_eq!(recovered.split_evidence().unwrap().copied_steps, 2);
        assert_eq!(recovered.evidence().compared_copies, 6);
        // Closing the copied self-loop also permits a shorter tree. Check
        // that tighter budgets constrain the accepted original-step count.
        let shorter = StructuredFunction::recover_with_step_limit(&source, 2, 5).unwrap();
        assert!(shorter.evidence().compared_copies <= 5);
        assert!(StructuredFunction::recover_with_step_limit(&source, 2, 4).is_err());
        assert!(StructuredFunction::recover_with_step_limit(&source, 1, 6).is_err());
        compare_split_reports(&source, &body, &recovered);
        compare_split_reports(&source, &body, &shorter);
    }
}

#[test]
fn split_entry_path_stops_at_another_entry_header() {
    for (graph, steps) in [(4556, 6), (4988, 8)] {
        for profile in 0..3 {
            let source = program5(graph, profile);
            let step = |address: usize| Node::Step {
                address: address as u64,
                assignments: source.instructions()[address].assignments.clone(),
            };
            let Control::Branch { condition, .. } = &source.instructions()[0].control else {
                unreachable!()
            };
            let branch = |taken, not_taken| Node::If {
                condition: condition.clone(),
                taken,
                not_taken,
            };
            let returned = || vec![step(4), Node::Return(r(2))];
            let prefix_exit = if graph == 4988 { returned() } else { vec![] };
            let loop_exit = if graph == 4988 {
                returned()
            } else {
                vec![Node::Continue]
            };
            let body = vec![
                step(0),
                branch(vec![step(2), branch(prefix_exit, vec![step(3)])], vec![]),
                Node::Loop(vec![
                    step(1),
                    branch(vec![Node::Continue], vec![]),
                    step(2),
                    branch(loop_exit, vec![]),
                    step(3),
                ]),
            ];
            structure_verify::validate(&source, &body).unwrap();
            let recovered = StructuredFunction::recover_with_step_limit(&source, 2, steps)
                .unwrap_or_else(|error| panic!("graph={graph}: {error}"));
            assert_eq!(recovered.split_evidence().unwrap().copied_steps, 2);
            assert!(recovered.evidence().compared_copies <= steps);
            assert!(StructuredFunction::recover_with_step_limit(&source, 1, steps).is_err());
            compare_split_reports(&source, &body, &recovered);
        }
    }
}

#[test]
fn split_entry_region_keeps_its_last_internal_backedge() {
    for profile in 0..3 {
        let source = program5(6201, profile);
        let step = |address: usize| Node::Step {
            address: address as u64,
            assignments: source.instructions()[address].assignments.clone(),
        };
        let Control::Branch { condition, .. } = &source.instructions()[0].control else {
            unreachable!()
        };
        let exit = || Node::If {
            condition: condition.clone(),
            taken: vec![Node::Break],
            not_taken: vec![],
        };
        let body = vec![
            step(0),
            Node::If {
                condition: condition.clone(),
                taken: vec![Node::Loop(vec![step(3), step(2), exit()])],
                not_taken: vec![],
            },
            Node::Loop(vec![step(1), Node::Loop(vec![step(2), exit(), step(3)])]),
        ];
        structure_verify::validate(&source, &body).unwrap();
        let recovered = StructuredFunction::recover_with_step_limit(&source, 2, 6)
            .expect("a copied entry cycle has a checked six-step representation");
        assert!(recovered.evidence().compared_copies <= 6);
        assert!(recovered.split_evidence().unwrap().attempted_candidates <= 16);
        assert!(StructuredFunction::recover_with_step_limit(&source, 1, 6).is_err());
        compare_split_reports(&source, &body, &recovered);
    }
}

#[test]
fn splitting_a_whole_cyclic_component_shares_the_return_tail() {
    for graph in [13652, 14961, 15393] {
        for profile in 0..3 {
            let source = program5(graph, profile);
            let recovered = StructuredFunction::recover_with_step_limit(&source, 2, 8)
                .unwrap_or_else(|error| panic!("graph={graph}: {error}"));
            assert!(recovered.evidence().compared_copies <= 8);
            assert!(recovered.split_evidence().unwrap().attempted_candidates <= 16);
            assert!(StructuredFunction::recover_with_step_limit(&source, 1, 8).is_err());
            // Count return Steps independently of loop/if nesting; the
            // shared epilogue must fit the original two-copy policy.
            fn count(nodes: &[Node]) -> usize {
                nodes
                    .iter()
                    .map(|node| match node {
                        Node::Step { address: 4, .. } => 1,
                        Node::Loop(body) => count(body),
                        Node::If {
                            taken, not_taken, ..
                        } => count(taken) + count(not_taken),
                        _ => 0,
                    })
                    .sum()
            }
            assert_eq!(count(recovered.body()), 1);
            compare_split_reports(&source, recovered.body(), &recovered);
        }
    }
}

#[test]
fn whole_component_copies_obey_the_eight_original_instruction_limit() {
    let base = program5(13652, 0);
    for width in [2, 3] {
        let lengths = [1, 3, 3, width, 1];
        let mut starts = [0u64; 5];
        for index in 1..5 {
            starts[index] = starts[index - 1] + lengths[index - 1];
        }
        let mut instructions = Vec::new();
        for (index, original) in base.instructions().iter().enumerate() {
            for offset in 0..lengths[index] {
                let control = if offset + 1 < lengths[index] {
                    Control::Next
                } else {
                    match &original.control {
                        Control::Branch { condition, target } => Control::Branch {
                            condition: condition.clone(),
                            target: starts[*target as usize],
                        },
                        control => control.clone(),
                    }
                };
                instructions.push(IrInstruction {
                    address: starts[index] + offset,
                    size: 1,
                    assignments: vec![],
                    control,
                });
            }
        }
        let source = Program::new(0, 3, instructions).unwrap();
        let recovered = StructuredFunction::recover(&source);
        if width == 2 {
            let function = recovered.as_ref().expect("an eight-step component fits");
            assert_eq!(function.split_evidence().unwrap().copied_steps, 8);
        }
        if let Ok(function) = recovered {
            // A nine-step component may use another valid smaller proposal,
            // but cannot be copied whole by bypassing the region-step limit.
            assert!(function.split_evidence().unwrap().copied_steps <= 8);
            for counter in [0, 1, 2, u64::MAX] {
                for budget in 0..=30 {
                    let input = [counter, 0, 0x55];
                    assert_eq!(
                        source.run_with_memory(&input, 0, &[], budget).unwrap(),
                        function.run_with_memory(&input, 0, &[], budget).unwrap()
                    );
                }
            }
        }
    }
}

fn compare_split_reports(source: &Program, body: &[Node], recovered: &StructuredFunction) {
    for counter in [0, 1, 2, u64::MAX] {
        for pointer in [0, 1, 3, u64::MAX] {
            for memory in [&[][..], &[1, 2, 3, 4][..]] {
                for budget in 0..=12 {
                    let input = [counter, pointer, 0x55];
                    let expected = source.run_with_memory(&input, 0, memory, budget).unwrap();
                    assert_eq!(expected, run_ast(body, &input, memory, budget));
                    assert_eq!(
                        expected,
                        recovered
                            .run_with_memory(&input, 0, memory, budget)
                            .unwrap()
                    );
                }
            }
        }
    }
}

#[test]
fn aliased_transfer_edits_keep_events_while_a_real_exit_change_is_rejected() {
    for profile in 0..3 {
        let source = larger_program(7, 12126506, profile);
        let function = StructuredFunction::recover(&source).unwrap();
        let mut edited = function.clone();
        assert!(mutate(&mut edited.body, 5));
        structure_verify::validate(&source, &edited.body).unwrap();
        let mut wrong = function.body.clone();
        let Some(Node::Loop(body)) = wrong.last_mut() else {
            unreachable!()
        };
        assert_eq!(body.last(), Some(&Node::Continue));
        *body.last_mut().unwrap() = Node::Break;
        assert!(structure_verify::validate(&source, &wrong).is_err());
        for counter in [0, 1, 2, u64::MAX] {
            for pointer in [0, 1, 3, u64::MAX] {
                for memory in [&[][..], &[1, 2, 3, 4][..]] {
                    for budget in 0..=64 {
                        let input = [counter, pointer, 0x55];
                        assert_eq!(
                            source.run_with_memory(&input, 0, memory, budget).unwrap(),
                            edited.run_with_memory(&input, 0, memory, budget).unwrap()
                        );
                    }
                }
            }
        }
    }
}

fn larger_program(count: usize, mut graph: usize, profile: usize) -> Program {
    let radix = 2 * count + 2;
    let template = program(0, profile);
    let mut instructions = Vec::new();
    for pc in 0..count {
        let choice = if pc + 1 == count {
            radix - 1
        } else {
            let choice = graph % radix;
            graph /= radix;
            choice
        };
        let control = if choice == 0 {
            Control::Next
        } else if choice <= count {
            Control::Jump((choice - 1) as u64)
        } else if choice <= 2 * count {
            Control::Branch {
                condition: if profile == 2 {
                    Expr::select(r(0), Expr::load(r(1), Width::U8), k(0))
                } else {
                    r(0)
                },
                target: (choice - count - 1) as u64,
            }
        } else {
            Control::Return(r(2))
        };
        instructions.push(IrInstruction {
            address: pc as u64,
            size: 1,
            assignments: if pc + 1 == count {
                vec![]
            } else {
                template.instructions()[pc % 3].assignments.clone()
            },
            control,
        });
    }
    Program::new(0, 3, instructions).unwrap()
}

fn sampled_larger_graphs(count: usize) -> Vec<usize> {
    let space = (2 * count + 2).pow((count - 1) as u32);
    let mut seen = std::collections::BTreeSet::new();
    let mut cases = Vec::new();
    // Two separate multiple-entry cycles, followed by Return(r2).
    if count == 7 {
        cases.push(0xc6d93a);
        seen.insert(0xc6d93a);
    }
    let mut index = 0;
    while cases.len() < 4096 {
        let graph = (index * 214013 + 2531011) % space;
        if seen.insert(graph) {
            cases.push(graph);
        }
        index += 1;
    }
    cases
}

#[test]
#[ignore = "bounded4096-topology six-instruction sample; run explicitly"]
fn sampled_six_instruction_cfgs_preserve_complete_rust_reports() {
    audit_cases(
        &sampled_larger_graphs(6),
        |graph, profile| larger_program(6, graph, profile),
        10,
    );
}

#[test]
#[ignore = "bounded4096-topology seven-instruction sample; run explicitly"]
fn sampled_seven_instruction_cfgs_preserve_complete_rust_reports() {
    audit_cases(
        &sampled_larger_graphs(7),
        |graph, profile| larger_program(7, graph, profile),
        10,
    );
}

fn audit(graphs: usize, make: fn(usize, usize) -> Program) {
    let cases: Vec<_> = (0..graphs).collect();
    assert_eq!(audit_cases(&cases, make, 6), (graphs * 3, 0));
}

fn audit_cases(
    graphs: &[usize],
    make: impl Fn(usize, usize) -> Program,
    maximum_budget: usize,
) -> (usize, usize) {
    let requested = graphs.len() * 3;
    let mut recovered = 0;
    let mut comparisons = 0;
    let mut rejected = BTreeMap::<String, (usize, usize, usize)>::new();
    let mut refused_cases = Vec::new();
    let mut mutants = 0;
    let mut accepted_mutants = 0;
    let mut accepted_edit_cases = Vec::new();
    for profile in 0..3 {
        for &graph in graphs {
            let source = make(graph, profile);
            let function = match StructuredFunction::recover(&source) {
                Ok(f) => f,
                Err(error) => {
                    refused_cases.push([profile, graph]);
                    rejected
                        .entry(format!("{error:?}"))
                        .or_insert((0, graph, profile))
                        .0 += 1;
                    continue;
                }
            };
            recovered += 1;
            let mut candidates = vec![function.clone()];
            for kind in 0..6 {
                let mut candidate = function.body().to_vec();
                if !mutate(&mut candidate, kind) {
                    continue;
                }
                mutants += 1;
                if structure_verify::validate(&source, &candidate).is_ok() {
                    accepted_edit_cases.push([profile, graph, kind]);
                    accepted_mutants += 1;
                    let mut altered = function.clone();
                    altered.body = candidate;
                    candidates.push(altered);
                }
            }
            for candidate in candidates {
                let nodes = candidate.body();
                for counter in [0, 1, 2, u64::MAX] {
                    for pointer in [0, 1, 3, u64::MAX] {
                        let input = [counter, pointer, 0x55];
                        for memory in [&[][..], &[1, 2, 3, 4][..]] {
                            for budget in 0..=maximum_budget {
                                let expected =
                                    source.run_with_memory(&input, 0, memory, budget).unwrap();
                                let actual = candidate
                                    .run_with_memory(&input, 0, memory, budget)
                                    .unwrap();
                                comparisons += 1;
                                assert_eq!(
                                    expected,
                                    actual,
                                    "profile={profile} graph={graph} input={input:?} memory={memory:?} budget={budget}\nIR={:?}\nAST={nodes:?}",
                                    source.instructions()
                                );
                            }
                        }
                    }
                }
            }
        }
    }
    let mut errors = String::new();
    for (i, (error, (count, graph, profile))) in rejected.iter().enumerate() {
        if i != 0 {
            errors.push(',');
        }
        write!(errors,"{{\"error\":{error:?},\"count\":{count},\"example_graph\":{graph},\"example_profile\":{profile}}}").unwrap();
    }
    let accepted_details = if accepted_edit_cases.is_empty() {
        String::new()
    } else {
        format!(",\"accepted_edit_cases\":{accepted_edit_cases:?}")
    };
    let report = format!(
        "{{\"schema\":\"nirvana-rust-structure-audit-v1\",\"requested\":{requested},\"recovered\":{recovered},\"comparisons\":{comparisons},\"mutants\":{mutants},\"accepted_mutants\":{accepted_mutants},\"rejected\":[{errors}],\"refused_cases\":{refused_cases:?}{accepted_details}}}\n"
    );
    if let Some(path) = std::env::var_os("NIRVANA_STRUCTURE_AUDIT_REPORT") {
        std::fs::write(path, &report).unwrap();
    }
    println!("{report}");
    assert_eq!(
        recovered + rejected.values().map(|(count, _, _)| count).sum::<usize>(),
        requested
    );
    assert!(recovered > 0 && comparisons > 0 && mutants > 0);
    // A syntactic transfer edit may preserve the entire event sequence.
    // Accepted edits were replayed above; known-negative fixtures stay
    // strict in model_trial_tests. The legacy cohorts still require zero.
    (recovered, accepted_mutants)
}

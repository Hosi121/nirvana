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
    let mut recovered = 0;
    let mut comparisons = 0;
    let mut rejected = BTreeMap::<String, (usize, usize, usize)>::new();
    let mut mutants = 0;
    let mut accepted_mutants = 0;
    for profile in 0..3 {
        for graph in 0..1000 {
            let source = program(graph, profile);
            let function = match StructuredFunction::recover(&source) {
                Ok(f) => f,
                Err(error) => {
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
                            for budget in 0..=6 {
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
    let report = format!(
        "{{\"schema\":\"nirvana-rust-structure-audit-v1\",\"requested\":3000,\"recovered\":{recovered},\"comparisons\":{comparisons},\"mutants\":{mutants},\"accepted_mutants\":{accepted_mutants},\"rejected\":[{errors}]}}\n"
    );
    if let Some(path) = std::env::var_os("NIRVANA_STRUCTURE_AUDIT_REPORT") {
        std::fs::write(path, &report).unwrap();
    }
    println!("{report}");
    assert_eq!(
        recovered + rejected.values().map(|(count, _, _)| count).sum::<usize>(),
        3000
    );
    assert!(recovered > 0 && comparisons > 0 && mutants > 0);
}

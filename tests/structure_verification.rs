use nirvana::ir::{Assignment, Control, Expr, IrInstruction, Place, Program, Reg, Width};
use nirvana::structure::{Node, StructuredFunction};
use nirvana::structure_verify::{FlowGraph, ValidationError, validate};

#[path = "../examples/programs/mod.rs"]
mod programs;

fn instruction(address: u64, assignments: Vec<Assignment>, control: Control) -> IrInstruction {
    IrInstruction {
        address,
        size: 1,
        assignments,
        control,
    }
}
fn step(address: u64) -> Node {
    Node::Step {
        address,
        assignments: vec![],
    }
}
fn c(value: u64) -> Expr {
    Expr::Const(value)
}
fn r(index: usize) -> Expr {
    Expr::Register(Reg(index))
}

fn alter_first(nodes: &mut [Node], change: &impl Fn(&mut Node) -> bool) -> bool {
    for node in nodes {
        if change(node) {
            return true;
        }
        match node {
            Node::If {
                taken, not_taken, ..
            } => {
                if alter_first(taken, change) || alter_first(not_taken, change) {
                    return true;
                }
            }
            Node::Loop(body) => {
                if alter_first(body, change) {
                    return true;
                }
            }
            _ => {}
        }
    }
    false
}

#[test]
fn recovered_shapes_and_shared_copies_have_exact_flow_evidence() {
    for name in programs::NAMES {
        let p = programs::named(name).unwrap();
        match StructuredFunction::recover_with_copy_limit(&p, 3) {
            Ok(function) => {
                let evidence = validate(&p, function.body()).unwrap();
                assert_eq!(evidence, function.evidence());
                assert!(evidence.compared_copies >= evidence.original_steps);
                assert!(evidence.flow_nodes > evidence.compared_copies);
                if *name == "shared-tail" {
                    assert_eq!(evidence.compared_copies, evidence.original_steps);
                }
                let graph = FlowGraph::from_nodes(function.body()).unwrap();
                assert!(graph.to_dot().starts_with("digraph structured_flow"));
                assert!(graph.entry().index() < graph.nodes().len());
            }
            Err(error) => assert_eq!(*name, "irreducible", "{name}: {error}"),
        }
    }
}

#[test]
fn swapped_arms_and_changed_conditions_are_rejected_without_inputs() {
    let p = programs::named("diamond").unwrap();
    let function = StructuredFunction::recover(&p).unwrap();
    let mut swapped = function.body().to_vec();
    assert!(alter_first(&mut swapped, &|node| {
        if let Node::If {
            taken, not_taken, ..
        } = node
        {
            std::mem::swap(taken, not_taken);
            true
        } else {
            false
        }
    }));
    assert!(matches!(
        validate(&p, &swapped),
        Err(ValidationError::Address { .. })
    ));
    let mut condition = function.body().to_vec();
    assert!(alter_first(&mut condition, &|node| {
        if let Node::If { condition, .. } = node {
            *condition = c(0);
            true
        } else {
            false
        }
    }));
    assert!(matches!(
        validate(&p, &condition),
        Err(ValidationError::Control { .. })
    ));
}

#[test]
fn assignment_changes_order_and_omitted_empty_steps_are_rejected() {
    let p = Program::new(
        0,
        2,
        vec![
            instruction(
                0,
                vec![
                    Assignment {
                        destination: Reg(0).into(),
                        value: c(7),
                    },
                    Assignment {
                        destination: Reg(1).into(),
                        value: r(0),
                    },
                ],
                Control::Next,
            ),
            instruction(1, vec![], Control::Return(r(1))),
        ],
    )
    .unwrap();
    let function = StructuredFunction::recover(&p).unwrap();
    let mut reordered = function.body().to_vec();
    assert!(alter_first(&mut reordered, &|node| {
        if let Node::Step { assignments, .. } = node {
            assignments.reverse();
            true
        } else {
            false
        }
    }));
    assert!(matches!(
        validate(&p, &reordered),
        Err(ValidationError::Assignments { address: 0, .. })
    ));
    let mut omitted = function.body().to_vec();
    omitted.retain(|node| !matches!(node, Node::Step { address: 1, .. }));
    assert!(matches!(
        validate(&p, &omitted),
        Err(ValidationError::ExpectedStep {
            expected_address: 1,
            ..
        })
    ));
}

#[test]
fn equal_successor_branch_must_still_evaluate_its_faulting_condition_once() {
    let condition = Expr::load(c(100), Width::U64);
    let p = Program::new(
        0,
        0,
        vec![
            instruction(
                0,
                vec![],
                Control::Branch {
                    condition: condition.clone(),
                    target: 1,
                },
            ),
            instruction(1, vec![], Control::Return(c(7))),
        ],
    )
    .unwrap();
    let function = StructuredFunction::recover(&p).unwrap();
    let mut omitted = function.body().to_vec();
    omitted.retain(|node| !matches!(node, Node::Evaluate(_)));
    assert!(matches!(
        validate(&p, &omitted),
        Err(ValidationError::Control { .. })
    ));
    let mut doubled = function.body().to_vec();
    doubled.insert(1, Node::Evaluate(condition.clone()));
    assert!(validate(&p, &doubled).is_err());
    let explicit = vec![
        step(0),
        Node::If {
            condition,
            taken: vec![],
            not_taken: vec![],
        },
        step(1),
        Node::Return(c(7)),
    ];
    assert!(validate(&p, &explicit).is_ok());
}

#[test]
fn unreachable_source_instructions_are_excluded_but_reachable_ast_tails_are_not() {
    let p = Program::new(
        1,
        0,
        vec![
            instruction(0, vec![], Control::Return(c(99))),
            instruction(1, vec![], Control::Return(c(7))),
        ],
    )
    .unwrap();
    assert_eq!(
        validate(&p, &[step(1), Node::Return(c(7))])
            .unwrap()
            .original_steps,
        1
    );
    assert!(validate(&p, &[step(0), Node::Return(c(99))]).is_err());
    assert!(validate(&p, &[step(1)]).is_err());
    assert!(validate(&p, &[step(1), Node::Return(c(8))]).is_err());
}

#[test]
fn loop_targets_are_lexical_and_outer_transfers_cannot_be_rebound() {
    let p = Program::new(
        0,
        3,
        vec![
            instruction(
                0,
                vec![],
                Control::Branch {
                    condition: r(0),
                    target: 2,
                },
            ),
            instruction(1, vec![], Control::Return(c(7))),
            instruction(
                2,
                vec![],
                Control::Branch {
                    condition: r(1),
                    target: 4,
                },
            ),
            instruction(3, vec![], Control::Jump(0)),
            instruction(4, vec![], Control::Jump(1)),
        ],
    )
    .unwrap();
    let body = vec![
        Node::Loop(vec![
            step(0),
            Node::If {
                condition: r(0),
                taken: vec![],
                not_taken: vec![Node::Break],
            },
            Node::Loop(vec![
                step(2),
                Node::If {
                    condition: r(1),
                    taken: vec![],
                    not_taken: vec![Node::Break],
                },
                step(4),
                Node::BreakOuter { levels: 1 },
            ]),
            step(3),
            Node::Continue,
        ]),
        step(1),
        Node::Return(c(7)),
    ];
    assert!(validate(&p, &body).is_ok());
    for replacement in [
        Node::Break,
        Node::Continue,
        Node::ContinueOuter { levels: 1 },
    ] {
        let mut mutant = body.clone();
        assert!(alter_first(&mut mutant, &|node| {
            if matches!(node, Node::BreakOuter { .. }) {
                *node = replacement.clone();
                true
            } else {
                false
            }
        }));
        assert!(validate(&p, &mutant).is_err());
    }
    let p = programs::named("nonlocal-exit").unwrap();
    let mut body = StructuredFunction::recover(&p).unwrap().body().to_vec();
    assert!(alter_first(&mut body, &|node| {
        if matches!(node, Node::ContinueOuter { .. }) {
            *node = Node::Continue;
            true
        } else {
            false
        }
    }));
    assert!(validate(&p, &body).is_err());
}

#[test]
fn silent_cycles_invalid_scopes_and_resource_limits_are_explicit_errors() {
    let p = Program::new(0, 0, vec![instruction(0, vec![], Control::Jump(0))]).unwrap();
    let body = vec![Node::Loop(vec![step(0)])];
    assert!(
        validate(&p, &body).is_ok(),
        "a real infinite loop still has original steps"
    );
    assert!(matches!(
        validate(&p, &[Node::Loop(vec![])]),
        Err(ValidationError::SilentCycle { .. })
    ));
    assert!(matches!(
        validate(&p, &[Node::Break]),
        Err(ValidationError::InvalidTransfer { .. })
    ));
    assert!(matches!(
        validate(
            &p,
            &[Node::Loop(vec![Node::ContinueOuter { levels: usize::MAX }])]
        ),
        Err(ValidationError::InvalidTransfer { .. })
    ));
    let mut deep = vec![step(0)];
    for _ in 0..258 {
        deep = vec![Node::Loop(deep)];
    }
    assert_eq!(validate(&p, &deep), Err(ValidationError::ResourceLimit));
}

#[test]
fn faulting_assignments_are_compared_as_ordered_memory_operations() {
    let a = Assignment {
        destination: Place::Memory {
            address: c(0),
            width: Width::U8,
        },
        value: c(99),
    };
    let b = Assignment {
        destination: Reg(0).into(),
        value: Expr::load(c(99), Width::U64),
    };
    let p = Program::new(
        0,
        1,
        vec![instruction(
            0,
            vec![a.clone(), b.clone()],
            Control::Return(c(0)),
        )],
    )
    .unwrap();
    let mutant = vec![
        Node::Step {
            address: 0,
            assignments: vec![b, a],
        },
        Node::Return(c(0)),
    ];
    assert!(matches!(
        validate(&p, &mutant),
        Err(ValidationError::Assignments { .. })
    ));
}

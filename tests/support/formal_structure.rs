//! Small raw IR/AST pairs shared by the exporter and private-executor replay.
use super::library::ir::{Assignment, Control, Expr, IrInstruction, Program, Reg, Width};
use super::library::structure::{Node, StructuredFunction};

pub struct Case {
    pub name: &'static str,
    pub program: Program,
    pub body: Vec<Node>,
    pub early_budget: bool,
}

fn r(index: usize) -> Expr {
    Expr::Register(Reg(index))
}
fn body(value: u64) -> Vec<Assignment> {
    vec![
        Assignment {
            destination: Reg(1).into(),
            value: Expr::Const(value),
        },
        Assignment {
            destination: Reg(0).into(),
            value: r(1),
        },
    ]
}
fn instruction(address: u64, assignments: Vec<Assignment>, control: Control) -> IrInstruction {
    IrInstruction {
        address,
        size: 1,
        assignments,
        control,
    }
}
fn step(address: u64, assignments: Vec<Assignment>) -> Node {
    Node::Step {
        address,
        assignments,
    }
}
fn diamond() -> Case {
    Case {
        name: "shared-tail",
        program: Program::new(
            0,
            2,
            vec![
                instruction(
                    0,
                    vec![],
                    Control::Branch {
                        condition: r(0),
                        target: 2,
                    },
                ),
                instruction(1, body(7), Control::Jump(3)),
                instruction(2, body(9), Control::Jump(3)),
                instruction(3, vec![], Control::Return(r(1))),
            ],
        )
        .unwrap(),
        body: vec![
            step(0, vec![]),
            Node::If {
                condition: r(0),
                taken: vec![step(2, body(9))],
                not_taken: vec![step(1, body(7))],
            },
            step(3, vec![]),
            Node::Return(r(1)),
        ],
        early_budget: false,
    }
}
fn outer() -> Case {
    Case {
        name: "outer-continue",
        program: Program::new(
            0,
            2,
            vec![
                instruction(0, vec![], Control::Next),
                instruction(
                    1,
                    vec![],
                    Control::Branch {
                        condition: r(0),
                        target: 0,
                    },
                ),
                instruction(2, vec![], Control::Return(r(1))),
            ],
        )
        .unwrap(),
        body: vec![Node::Loop(vec![
            step(0, vec![]),
            Node::Loop(vec![
                step(1, vec![]),
                Node::If {
                    condition: r(0),
                    taken: vec![Node::ContinueOuter { levels: 1 }],
                    not_taken: vec![step(2, vec![]), Node::Return(r(1))],
                },
            ]),
        ])],
        early_budget: false,
    }
}
fn equal() -> Case {
    let condition = Expr::load(r(1), Width::U8);
    Case {
        name: "equal-successor-evaluation",
        program: Program::new(
            0,
            2,
            vec![
                instruction(
                    0,
                    vec![],
                    Control::Branch {
                        condition: condition.clone(),
                        target: 1,
                    },
                ),
                instruction(1, vec![], Control::Return(r(0))),
            ],
        )
        .unwrap(),
        body: vec![
            step(0, vec![]),
            Node::Evaluate(condition),
            step(1, vec![]),
            Node::Return(r(0)),
        ],
        early_budget: false,
    }
}

pub fn cases() -> Vec<Case> {
    let mut swapped = diamond();
    swapped.name = "swapped-arms";
    if let Node::If {
        taken, not_taken, ..
    } = &mut swapped.body[1]
    {
        std::mem::swap(taken, not_taken);
    }
    let mut missing = diamond();
    missing.name = "missing-step";
    if let Node::If { not_taken, .. } = &mut missing.body[1] {
        not_taken.clear();
    }
    let mut dropped = equal();
    dropped.name = "dropped-evaluation";
    dropped.body.remove(1);
    let mut wrong_outer = outer();
    wrong_outer.name = "wrong-outer-depth";
    if let Node::Loop(out) = &mut wrong_outer.body[0]
        && let Node::Loop(inner) = &mut out[1]
        && let Node::If { taken, .. } = &mut inner[1]
    {
        taken[0] = Node::Continue;
    }
    let mut reordered = diamond();
    reordered.name = "reordered-assignments";
    if let Node::If { taken, .. } = &mut reordered.body[1]
        && let Node::Step { assignments, .. } = &mut taken[0]
    {
        assignments.reverse();
    }
    let mut early = diamond();
    early.name = "early-budget-executor";
    early.early_budget = true;
    let mut result = vec![
        diamond(),
        outer(),
        equal(),
        swapped,
        missing,
        dropped,
        wrong_outer,
        reordered,
        early,
    ];
    for (mut case, name) in [
        (diamond(), "recovered-shared-tail"),
        (outer(), "recovered-outer-loop"),
        (equal(), "recovered-equal-successor"),
    ] {
        case.name = name;
        case.body = StructuredFunction::recover(&case.program)
            .unwrap()
            .body()
            .to_vec();
        result.push(case);
    }
    let branch = |target| Control::Branch {
        condition: r(0),
        target,
    };
    let program = || {
        Program::new(
            0,
            2,
            [
                branch(2),
                Control::Jump(1),
                branch(1),
                Control::Next,
                branch(1),
                branch(3),
                Control::Return(r(1)),
            ]
            .into_iter()
            .enumerate()
            .map(|(pc, control)| instruction(pc as u64, vec![], control))
            .collect(),
        )
        .unwrap()
    };
    let original = StructuredFunction::recover(&program())
        .unwrap()
        .body()
        .to_vec();
    let mut edited = original.clone();
    fn replace_inner_continue(nodes: &mut [Node]) -> bool {
        for node in nodes {
            if let Node::Loop(body) = node
                && matches!(
                    body.as_slice(),
                    [Node::Step { address: 1, .. }, Node::Continue]
                )
            {
                body[1] = Node::Break;
                return true;
            }
            let changed = match node {
                Node::Loop(body) => replace_inner_continue(body),
                Node::If {
                    taken, not_taken, ..
                } => replace_inner_continue(taken) || replace_inner_continue(not_taken),
                _ => false,
            };
            if changed {
                return true;
            }
        }
        false
    }
    assert!(replace_inner_continue(&mut edited));
    result.push(Case {
        name: "recovered-routing-alias",
        program: program(),
        body: original,
        early_budget: false,
    });
    result.push(Case {
        name: "equivalent-transfer-edit",
        program: program(),
        body: edited,
        early_budget: false,
    });
    result
}

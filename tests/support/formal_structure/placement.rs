//! Placement witnesses keep arithmetic payloads, source PCs and real recovery.
use super::super::library::ir::BinaryOp;
use super::*;

fn branch(target: u64) -> Control {
    Control::Branch {
        condition: r(0),
        target,
    }
}
fn increment(value: u64) -> Assignment {
    Assignment {
        destination: Reg(1).into(),
        value: Expr::binary(BinaryOp::Add, r(1), Expr::Const(value)),
    }
}
fn decrement() -> Assignment {
    Assignment {
        destination: Reg(0).into(),
        value: Expr::binary(BinaryOp::Sub, r(0), Expr::Const(1)),
    }
}
fn at(program: &Program, pc: u64) -> Node {
    step(pc, program.instructions()[pc as usize].assignments.clone())
}
fn divergent_follow() -> Case {
    let program = Program::new(
        0,
        2,
        [
            branch(4),
            Control::Jump(2),
            Control::Jump(1),
            branch(1),
            branch(1),
            branch(3),
            Control::Return(r(1)),
        ]
        .into_iter()
        .enumerate()
        .map(|(pc, control)| {
            instruction(
                pc as u64,
                match pc {
                    1 => vec![increment(1)],
                    4 => vec![increment(4), decrement()],
                    _ => vec![],
                },
                control,
            )
        })
        .collect(),
    )
    .unwrap();
    let s = |pc| at(&program, pc);
    let body = vec![
        s(0),
        Node::If {
            condition: r(0),
            taken: vec![Node::Loop(vec![
                s(4),
                Node::If {
                    condition: r(0),
                    taken: vec![Node::Break],
                    not_taken: vec![],
                },
                s(5),
                Node::If {
                    condition: r(0),
                    taken: vec![
                        s(3),
                        Node::If {
                            condition: r(0),
                            taken: vec![Node::Break],
                            not_taken: vec![],
                        },
                    ],
                    not_taken: vec![s(6), Node::Return(r(1))],
                },
            ])],
            not_taken: vec![],
        },
        Node::Loop(vec![s(1), s(2)]),
    ];
    Case {
        name: "shared-divergent-follow",
        program,
        body,
        early_budget: false,
    }
}
fn shared_entries() -> Case {
    let program = Program::new(
        0,
        2,
        [
            branch(3),
            branch(4),
            Control::Jump(3),
            branch(3),
            branch(2),
            Control::Return(r(1)),
        ]
        .into_iter()
        .enumerate()
        .map(|(pc, control)| {
            instruction(
                pc as u64,
                match pc {
                    2 => vec![increment(1)],
                    3 => vec![increment(3), decrement()],
                    4 => vec![increment(2)],
                    _ => vec![],
                },
                control,
            )
        })
        .collect(),
    )
    .unwrap();
    let s = |pc| at(&program, pc);
    let body = vec![
        s(0),
        Node::If {
            condition: r(0),
            taken: vec![],
            not_taken: vec![
                s(1),
                Node::If {
                    condition: r(0),
                    taken: vec![
                        s(4),
                        Node::If {
                            condition: r(0),
                            taken: vec![],
                            not_taken: vec![s(5), Node::Return(r(1))],
                        },
                    ],
                    not_taken: vec![],
                },
                s(2),
            ],
        },
        Node::Loop(vec![
            s(3),
            Node::If {
                condition: r(0),
                taken: vec![Node::Continue],
                not_taken: vec![],
            },
            s(4),
            Node::If {
                condition: r(0),
                taken: vec![s(2)],
                not_taken: vec![s(5), Node::Return(r(1))],
            },
        ]),
    ];
    Case {
        name: "shared-entry-region",
        program,
        body,
        early_budget: false,
    }
}
pub(super) fn cases() -> Vec<Case> {
    let mut result = Vec::new();
    for (case, name) in [
        (divergent_follow(), "recovered-divergent-follow"),
        (shared_entries(), "recovered-shared-entry-region"),
    ] {
        let recovered = StructuredFunction::recover(&case.program).unwrap();
        let actual = Case {
            name,
            program: case.program.clone(),
            body: recovered.body().to_vec(),
            early_budget: false,
        };
        result.push(case);
        result.push(actual);
    }
    result
}

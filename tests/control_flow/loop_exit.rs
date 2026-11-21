use nirvana::loop_exit;
use nirvana::{ir, structure};

use ir::{
    AccessKind, Assignment, BinaryOp, Control, Expr, IrInstruction, MemoryFault, Place, Program,
    Reg, RunStatus, Width,
};
use loop_exit::{ExitLoop, recover};
use structure::Node;

const BASE: u64 = 0x1000;
use crate::support::ir::c;
use crate::support::ir::r;
fn b(op: BinaryOp, a: Expr, z: Expr) -> Expr {
    Expr::binary(op, a, z)
}
fn set(id: usize, value: Expr) -> Assignment {
    Assignment {
        destination: Reg(id).into(),
        value,
    }
}
fn store(address: Expr, width: Width, value: Expr) -> Assignment {
    Assignment {
        destination: Place::Memory { address, width },
        value,
    }
}
fn step(address: u64, assignments: Vec<Assignment>) -> Node {
    Node::Step {
        address,
        assignments,
    }
}
fn last(continue_when: bool, exit: Vec<Node>) -> Node {
    Node::If {
        condition: b(BinaryOp::Ult, r(0), r(1)),
        taken: if continue_when {
            vec![Node::Continue]
        } else {
            exit.clone()
        },
        not_taken: if continue_when {
            exit
        } else {
            vec![Node::Continue]
        },
    }
}
fn body(continue_when: bool) -> Vec<Node> {
    let condition = if continue_when {
        b(BinaryOp::Ult, r(0), r(1))
    } else {
        b(BinaryOp::Ule, r(1), r(0))
    };
    let exit = vec![
        step(
            20,
            vec![store(
                c(BASE + 8),
                Width::U32,
                b(BinaryOp::Add, r(0), Expr::load(r(3), Width::U8)),
            )],
        ),
        Node::Evaluate(Expr::select(
            r(5),
            Expr::load(c(u64::MAX), Width::U8),
            Expr::load(c(BASE + 1), Width::U8),
        )),
        Node::Return(b(BinaryOp::Add, Expr::load(c(BASE + 8), Width::U32), r(0))),
    ];
    let mut tail = last(continue_when, exit);
    let Node::If {
        condition: tail_condition,
        ..
    } = &mut tail
    else {
        unreachable!()
    };
    *tail_condition = condition;
    vec![
        step(10, vec![store(c(BASE + 15), Width::U8, c(0xa1))]),
        step(
            11,
            vec![
                set(0, b(BinaryOp::Add, r(0), c(1))),
                set(
                    4,
                    Expr::select(
                        c(1),
                        Expr::load(r(2), Width::U8),
                        Expr::load(c(u64::MAX), Width::U64),
                    ),
                ),
            ],
        ),
        step(
            12,
            vec![store(
                r(3),
                Width::U16,
                b(
                    BinaryOp::Add,
                    Expr::load(r(2), Width::U16),
                    Expr::load(c(BASE), Width::U8),
                ),
            )],
        ),
        tail,
    ]
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum Access {
    Read {
        point: (u64, usize),
        address: u64,
        width: Width,
    },
    StoreCheck {
        point: (u64, usize),
        address: u64,
        width: Width,
    },
    StoreCommit {
        point: (u64, usize),
        address: u64,
        width: Width,
        value: u64,
    },
}
#[derive(Clone, Debug, Eq, PartialEq)]
enum Stop {
    Fault(MemoryFault),
    Budget,
}
#[derive(Clone, Debug, Eq, PartialEq)]
struct Report {
    result: Result<u64, Stop>,
    registers: Vec<u64>,
    memory: Vec<u8>,
    accesses: Vec<Access>,
}
#[derive(Clone, Copy)]
enum Flow {
    Next,
    Break,
    Continue,
    Return(u64),
}
struct Machine {
    registers: Vec<u64>,
    memory: Vec<u8>,
    accesses: Vec<Access>,
    fuel: usize,
}
impl Machine {
    fn tick(&mut self) -> Result<(), Stop> {
        self.fuel = self.fuel.checked_sub(1).ok_or(Stop::Budget)?;
        Ok(())
    }
    // Each primitive uses the existing executable IR for exact unsigned and
    // checked little-endian semantics. The AST/control interpreter is separate.
    fn model(&self, assignments: Vec<Assignment>, value: Expr) -> Result<(u64, Vec<u8>), Stop> {
        let program = Program::new(
            0,
            0,
            vec![IrInstruction {
                address: 0,
                size: 1,
                assignments,
                control: Control::Return(value),
            }],
        )
        .unwrap();
        let report = program.run_with_memory(&[], BASE, &self.memory, 1).unwrap();
        match report.status {
            RunStatus::Returned(value) => Ok((value, report.state.memory)),
            RunStatus::Fault(fault) => Err(Stop::Fault(fault)),
            RunStatus::Suspended => panic!("primitive IR suspended"),
        }
    }
    fn expression(&mut self, value: &Expr, point: (u64, usize)) -> Result<u64, Stop> {
        self.tick()?;
        Ok(match value {
            Expr::Const(value) => *value,
            Expr::Register(reg) => self.registers[reg.0],
            Expr::Binary(op, a, z) => {
                let a = self.expression(a, point)?;
                let z = self.expression(z, point)?;
                self.model(vec![], b(*op, c(a), c(z)))?.0
            }
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => {
                let condition = self.expression(condition, point)?;
                self.expression(if condition != 0 { taken } else { not_taken }, point)?
            }
            Expr::Load { address, width } => {
                let address = self.expression(address, point)?;
                self.accesses.push(Access::Read {
                    point,
                    address,
                    width: *width,
                });
                self.model(vec![], Expr::load(c(address), *width))?.0
            }
        })
    }
    fn assignment(&mut self, assignment: &Assignment, point: (u64, usize)) -> Result<(), Stop> {
        self.tick()?;
        match &assignment.destination {
            Place::Register(reg) => {
                self.registers[reg.0] = self.expression(&assignment.value, point)?
            }
            Place::Memory { address, width } => {
                let address = self.expression(address, point)?;
                self.accesses.push(Access::StoreCheck {
                    point,
                    address,
                    width: *width,
                });
                // Probe on a discarded memory clone before evaluating the RHS,
                // matching the IR's destination-check-before-RHS contract.
                self.model(vec![store(c(address), *width, c(0))], c(0))?;
                let value = self.expression(&assignment.value, point)?;
                self.memory = self
                    .model(vec![store(c(address), *width, c(value))], c(0))?
                    .1;
                self.accesses.push(Access::StoreCommit {
                    point,
                    address,
                    width: *width,
                    value,
                });
            }
        }
        Ok(())
    }
    fn nodes(&mut self, nodes: &[Node]) -> Result<Flow, Stop> {
        for node in nodes {
            self.tick()?;
            let flow = match node {
                Node::Step {
                    address,
                    assignments,
                } => {
                    for (index, assignment) in assignments.iter().enumerate() {
                        self.assignment(assignment, (*address, index))?;
                    }
                    Flow::Next
                }
                Node::Evaluate(value) => {
                    self.expression(value, (u64::MAX, 0))?;
                    Flow::Next
                }
                Node::Return(value) => Flow::Return(self.expression(value, (u64::MAX, 1))?),
                Node::If {
                    condition,
                    taken,
                    not_taken,
                } => {
                    let condition = self.expression(condition, (u64::MAX, 2))?;
                    self.nodes(if condition != 0 { taken } else { not_taken })?
                }
                Node::Loop(body) => loop {
                    self.tick()?;
                    match self.nodes(body)? {
                        Flow::Next | Flow::Continue => {}
                        Flow::Break => break Flow::Next,
                        other => break other,
                    }
                },
                Node::Break => Flow::Break,
                Node::Continue => Flow::Continue,
                _ => panic!("test interpreter excludes nonlocal transfers"),
            };
            if !matches!(flow, Flow::Next) {
                return Ok(flow);
            }
        }
        Ok(Flow::Next)
    }
    fn report(self, result: Result<u64, Stop>) -> Report {
        Report {
            result,
            registers: self.registers,
            memory: self.memory,
            accesses: self.accesses,
        }
    }
}
fn original(nodes: &[Node], registers: Vec<u64>, memory: Vec<u8>, fuel: usize) -> Report {
    let mut machine = Machine {
        registers,
        memory,
        accesses: vec![],
        fuel,
    };
    let result = (|| loop {
        machine.tick()?;
        match machine.nodes(nodes)? {
            Flow::Next | Flow::Continue => {}
            Flow::Return(value) => break Ok(value),
            Flow::Break => panic!("current break unsupported"),
        }
    })();
    machine.report(result)
}
fn displayed(view: ExitLoop<'_>, registers: Vec<u64>, memory: Vec<u8>, fuel: usize) -> Report {
    let mut machine = Machine {
        registers,
        memory,
        accesses: vec![],
        fuel,
    };
    let result = (|| {
        loop {
            machine.tick()?;
            match machine.nodes(view.body)? {
                Flow::Return(value) => return Ok(value),
                Flow::Next => {}
                _ => panic!("prefix escapes current loop"),
            }
            let condition = machine.expression(view.condition, (u64::MAX, 2))?;
            if (condition != 0) != view.continue_when {
                break;
            }
        }
        match machine.nodes(view.exit)? {
            Flow::Return(value) => Ok(value),
            _ => panic!("exit must return"),
        }
    })();
    machine.report(result)
}

#[test]
fn view_borrows_the_exact_condition_body_and_exit_for_both_branch_directions() {
    for continue_when in [false, true] {
        let nodes = body(continue_when);
        let before = nodes.clone();
        let view = recover(&nodes).unwrap();
        let Node::If {
            condition,
            taken,
            not_taken,
        } = nodes.last().unwrap()
        else {
            unreachable!()
        };
        assert!(std::ptr::eq(view.condition, condition));
        assert_eq!(view.continue_when, continue_when);
        assert!(std::ptr::eq(view.body, &nodes[..nodes.len() - 1]));
        assert!(std::ptr::eq(
            view.exit,
            if continue_when {
                not_taken.as_slice()
            } else {
                taken.as_slice()
            }
        ));
        assert_eq!(nodes, before);
    }
}

#[test]
fn returning_post_test_loop_preserves_return_memory_first_fault_and_ordered_accesses() {
    for continue_when in [false, true] {
        let nodes = body(continue_when);
        let view = recover(&nodes).unwrap();
        for a in [BASE, BASE + 7, BASE + 15, u64::MAX] {
            for z in [BASE, BASE + 8, BASE + 15, u64::MAX] {
                for limit in [0, 1, 3] {
                    for fail_exit in [0, 1] {
                        let registers = vec![0, limit, a, z, 0, fail_exit, 0, 0];
                        let memory: Vec<_> = (1..=16).collect();
                        let expected = original(&nodes, registers.clone(), memory.clone(), 50000);
                        let actual = displayed(view, registers, memory, 50000);
                        assert_eq!(
                            actual, expected,
                            "direction={continue_when}, a={a:#x}, z={z:#x},limit={limit},exit={fail_exit}"
                        );
                        assert!(!matches!(actual.result, Err(Stop::Budget)));
                    }
                }
            }
        }
    }
    let nodes = body(true);
    let view = recover(&nodes).unwrap();
    let report = displayed(
        view,
        vec![0, 1, BASE + 15, u64::MAX, 0, 0, 0, 0],
        (1..=16).collect(),
        10000,
    );
    assert_eq!(
        report.result,
        Err(Stop::Fault(MemoryFault {
            access: AccessKind::Write,
            address: u64::MAX,
            width: Width::U16
        }))
    );
    assert_eq!(report.memory[15], 0xa1, "earlier write remains committed");
    assert!(matches!(
        report.accesses.last(),
        Some(Access::StoreCheck {
            address: u64::MAX,
            ..
        })
    ));
}

#[test]
fn nested_local_transfers_and_early_return_keep_their_targets() {
    let mut nodes = body(true);
    nodes.insert(
        0,
        Node::If {
            condition: r(5),
            taken: vec![Node::Return(Expr::load(r(2), Width::U64))],
            not_taken: vec![],
        },
    );
    nodes.insert(1, step(8, vec![set(6, c(0))]));
    nodes.insert(
        2,
        Node::Loop(vec![
            step(9, vec![set(6, b(BinaryOp::Add, r(6), c(1)))]),
            Node::If {
                condition: b(BinaryOp::Ult, r(6), c(2)),
                taken: vec![Node::Continue],
                not_taken: vec![Node::Break],
            },
        ]),
    );
    let view = recover(&nodes).unwrap();
    for early in [0, 1] {
        for address in [BASE, u64::MAX] {
            let registers = vec![0, 3, address, BASE, 0, early, 0, 0];
            let memory: Vec<_> = (1..=16).collect();
            let expected = original(&nodes, registers.clone(), memory.clone(), 50000);
            assert_eq!(displayed(view, registers, memory, 50000), expected);
        }
    }
    let mut endless = vec![Node::Loop(vec![Node::Continue])];
    endless.push(last(true, vec![Node::Return(c(1))]));
    let view = recover(&endless).unwrap();
    // Both interpreters exhaust fuel here. No exact cutoff-state, instruction
    // count or termination-equivalence claim is made for arbitrary budgets.
    assert_eq!(
        original(&endless, vec![0; 8], vec![], 100).result,
        Err(Stop::Budget)
    );
    assert_eq!(
        displayed(view, vec![0; 8], vec![], 100).result,
        Err(Stop::Budget)
    );
}

#[test]
fn prefix_current_loop_transfers_and_all_nonlocal_transfers_are_rejected() {
    for transfer in [
        Node::Break,
        Node::Continue,
        Node::BreakOuter { levels: 0 },
        Node::ContinueOuter { levels: 1 },
        Node::Loop(vec![Node::Loop(vec![Node::BreakOuter { levels: 1 }])]),
    ] {
        let nodes = vec![
            Node::If {
                condition: c(0),
                taken: vec![transfer],
                not_taken: vec![],
            },
            last(true, vec![Node::Return(c(1))]),
        ];
        assert!(recover(&nodes).is_none());
    }
}

#[test]
fn exit_shape_strict_continue_arm_and_memory_free_condition_are_required() {
    for exit in [
        vec![],
        vec![Node::Evaluate(c(0))],
        vec![Node::Return(c(1)), Node::Return(c(2))],
        vec![
            Node::If {
                condition: c(1),
                taken: vec![],
                not_taken: vec![],
            },
            Node::Return(c(1)),
        ],
        vec![Node::Loop(vec![Node::Break]), Node::Return(c(1))],
    ] {
        assert!(recover(&[last(true, exit)]).is_none());
    }
    for condition in [
        Expr::load(c(BASE), Width::U8),
        Expr::select(c(1), c(1), Expr::load(c(u64::MAX), Width::U64)),
    ] {
        assert!(
            recover(&[Node::If {
                condition,
                taken: vec![Node::Continue],
                not_taken: vec![Node::Return(c(1))]
            }])
            .is_none()
        );
    }
    assert!(
        recover(&[Node::If {
            condition: c(1),
            taken: vec![Node::Continue],
            not_taken: vec![Node::Continue]
        }])
        .is_none()
    );
    assert!(
        recover(&[Node::If {
            condition: c(1),
            taken: vec![step(0, vec![]), Node::Continue],
            not_taken: vec![Node::Return(c(1))]
        }])
        .is_none()
    );
    assert!(recover(&[]).is_none());
    assert!(recover(&[Node::Return(c(1))]).is_none());
}

#[test]
fn whole_ast_depth_size_expression_and_work_limits_discard_the_view() {
    let mut wide = vec![Node::Evaluate(c(0)); loop_exit::MAX_NODES];
    wide.push(last(true, vec![Node::Return(c(0))]));
    assert!(recover(&wide).is_none());
    let mut deep = Node::Evaluate(c(0));
    for _ in 0..=loop_exit::MAX_NODE_DEPTH {
        deep = Node::Loop(vec![deep]);
    }
    assert!(recover(&[deep, last(true, vec![Node::Return(c(0))])]).is_none());
    let mut value = c(0);
    for _ in 0..=loop_exit::MAX_EXPRESSION_DEPTH {
        value = b(BinaryOp::Add, value, c(0));
    }
    assert!(recover(&[last(true, vec![Node::Return(value)])]).is_none());
    fn balanced(leaves: usize) -> Expr {
        if leaves == 1 {
            return c(1);
        }
        b(
            BinaryOp::Add,
            balanced(leaves / 2),
            balanced(leaves - leaves / 2),
        )
    }
    // 65535 condition expression nodes fit the syntax ceiling; inspecting it
    // again for memory purity exhausts the independent whole-work ceiling.
    assert!(
        recover(&[Node::If {
            condition: balanced(32768),
            taken: vec![Node::Continue],
            not_taken: vec![Node::Return(c(0))]
        }])
        .is_none()
    );
}

#[test]
fn compacted_return_tail_keeps_both_directions_and_nonboolean_conditions() {
    for continue_when in [false, true] {
        for truth in [2, u64::MAX] {
            let mut nodes = body(continue_when);
            let Node::If {
                condition,
                taken,
                not_taken,
            } = nodes.pop().unwrap()
            else {
                unreachable!()
            };
            // Preserve the predicate's truth values while exercising raw
            // nonboolean C conditions and their inverted continuation arm.
            let condition = Expr::select(condition, c(truth), c(0));
            let exit = if continue_when { not_taken } else { taken };
            nodes.push(Node::If {
                condition,
                taken: if continue_when {
                    vec![Node::Continue]
                } else {
                    vec![]
                },
                not_taken: if continue_when {
                    vec![]
                } else {
                    vec![Node::Continue]
                },
            });
            let exit_start = nodes.len();
            nodes.extend(exit);
            let view = recover(&nodes).unwrap();
            assert_eq!(view.exit.as_ptr(), nodes[exit_start..].as_ptr());
            assert_eq!(view.continue_when, continue_when);
            for limit in [0, 1, 3] {
                for read in [BASE, u64::MAX] {
                    for write in [BASE + 4, BASE + 15] {
                        let registers = vec![0, limit, read, write, 0, 0];
                        let memory = (1..=16).collect::<Vec<u8>>();
                        assert_eq!(
                            original(&nodes, registers.clone(), memory.clone(), 2000),
                            displayed(view, registers, memory, 2000),
                        );
                    }
                }
            }
        }
    }
}

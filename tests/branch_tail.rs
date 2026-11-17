use nirvana::branch_tail::{MAX_EXPRESSION_DEPTH, MAX_ITEMS, MAX_NODE_DEPTH, factor};
use nirvana::ir::{
    AccessKind, Assignment, BinaryOp, Control, Expr, IrInstruction, MemoryFault, Place, Program,
    Reg, RunStatus, Width,
};
use nirvana::structure::Node;

fn r(index: usize) -> Expr {
    Expr::Register(Reg(index))
}
fn c(value: u64) -> Expr {
    Expr::Const(value)
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
fn store(address: u64, width: Width, value: Expr) -> Assignment {
    Assignment {
        destination: Place::Memory {
            address: c(address),
            width,
        },
        value,
    }
}
fn step(address: u64, assignments: Vec<Assignment>) -> Node {
    Node::Step {
        address,
        assignments,
    }
}
fn branch(condition: Expr, taken: Vec<Node>, not_taken: Vec<Node>) -> Node {
    Node::If {
        condition,
        taken,
        not_taken,
    }
}

#[derive(Debug, Eq, PartialEq)]
struct Observation {
    status: RunStatus,
    registers: Vec<u64>,
    memory: Vec<u8>,
    steps: Vec<u64>,
}
struct Machine {
    registers: Vec<u64>,
    memory: Vec<u8>,
    fuel: usize,
    steps: Vec<u64>,
}
enum Flow {
    Normal,
    Break(usize),
    Continue(usize),
    Return(u64),
    Stop(RunStatus),
}
impl Machine {
    // Expression/assignment semantics come from the checked IR rather than the
    // factoring implementation. Fuel observes each condition, Evaluate, Step,
    // and Return, so moving a guard or effect across the suffix is detectable.
    fn execute(
        &mut self,
        pc: Option<u64>,
        assignments: Vec<Assignment>,
        expression: Expr,
    ) -> Result<u64, RunStatus> {
        if self.fuel == 0 {
            return Err(RunStatus::Suspended);
        }
        self.fuel -= 1;
        if let Some(pc) = pc {
            self.steps.push(pc);
        }
        let p = Program::new(
            0,
            self.registers.len(),
            vec![IrInstruction {
                address: 0,
                size: 1,
                assignments,
                control: Control::Return(expression),
            }],
        )
        .unwrap();
        let report = p
            .run_with_memory(&self.registers, 0, &self.memory, 1)
            .unwrap();
        self.registers = report.state.registers;
        self.memory = report.state.memory;
        match report.status {
            RunStatus::Returned(value) => Ok(value),
            status => Err(status),
        }
    }
    fn nodes(&mut self, nodes: &[Node]) -> Flow {
        for node in nodes {
            let flow = match node {
                Node::Step {
                    address,
                    assignments,
                } => match self.execute(Some(*address), assignments.clone(), c(0)) {
                    Ok(_) => Flow::Normal,
                    Err(status) => Flow::Stop(status),
                },
                Node::Evaluate(expression) => {
                    match self.execute(None, vec![], expression.clone()) {
                        Ok(_) => Flow::Normal,
                        Err(status) => Flow::Stop(status),
                    }
                }
                Node::If {
                    condition,
                    taken,
                    not_taken,
                } => match self.execute(None, vec![], condition.clone()) {
                    Ok(value) => self.nodes(if value != 0 { taken } else { not_taken }),
                    Err(status) => Flow::Stop(status),
                },
                Node::Loop(body) => loop {
                    match self.nodes(body) {
                        Flow::Normal | Flow::Continue(0) => {}
                        Flow::Break(0) => break Flow::Normal,
                        Flow::Break(levels) => break Flow::Break(levels - 1),
                        Flow::Continue(levels) => break Flow::Continue(levels - 1),
                        flow => break flow,
                    }
                },
                Node::Break => Flow::Break(0),
                Node::Continue => Flow::Continue(0),
                Node::BreakOuter { levels } => Flow::Break(*levels),
                Node::ContinueOuter { levels } => Flow::Continue(*levels),
                Node::Return(expression) => match self.execute(None, vec![], expression.clone()) {
                    Ok(value) => Flow::Return(value),
                    Err(status) => Flow::Stop(status),
                },
            };
            if !matches!(flow, Flow::Normal) {
                return flow;
            }
        }
        Flow::Normal
    }
}
fn run(nodes: &[Node], input: &[u64; 4], memory: &[u8], fuel: usize) -> Observation {
    let mut machine = Machine {
        registers: input.to_vec(),
        memory: memory.to_vec(),
        fuel,
        steps: vec![],
    };
    let status = match machine.nodes(nodes) {
        Flow::Return(value) => RunStatus::Returned(value),
        Flow::Stop(status) => status,
        Flow::Normal => RunStatus::Returned(0),
        _ => panic!("escaped loop transfer"),
    };
    Observation {
        status,
        registers: machine.registers,
        memory: machine.memory,
        steps: machine.steps,
    }
}
fn compare(nodes: &[Node], input: &[u64; 4], memory: &[u8]) -> Observation {
    let saved = nodes.to_vec();
    let output = factor(nodes).unwrap();
    assert_eq!(nodes, saved, "source AST must remain untouched");
    assert_eq!(factor(&output).unwrap(), output, "factoring is idempotent");
    for fuel in 0..80 {
        assert_eq!(
            run(nodes, input, memory, fuel),
            run(&output, input, memory, fuel),
            "fuel={fuel}"
        );
    }
    let expected = run(nodes, input, memory, 500);
    assert_eq!(expected, run(&output, input, memory, 500));
    expected
}

#[test]
fn common_steps_hoist_once_after_unchanged_branch_prefixes() {
    let tail = step(30, vec![store(0, Width::U8, r(1))]);
    let nodes = vec![
        branch(
            r(0),
            vec![step(10, vec![set(1, c(11))]), tail.clone()],
            vec![step(20, vec![set(1, c(22))]), tail.clone()],
        ),
        Node::Return(Expr::load(c(0), Width::U8)),
    ];
    assert_eq!(
        factor(&nodes).unwrap(),
        vec![
            branch(
                r(0),
                vec![step(10, vec![set(1, c(11))])],
                vec![step(20, vec![set(1, c(22))])]
            ),
            tail,
            Node::Return(Expr::load(c(0), Width::U8))
        ]
    );
    for condition in [0, 1, u64::MAX] {
        compare(&nodes, &[condition, 0, 0, 0], &[0x5a; 8]);
    }
}

#[test]
fn empty_prefixes_keep_all_guard_reads_even_when_the_guard_is_pure() {
    for condition in [r(3), c(0), Expr::load(c(12), Width::U16)] {
        let tail = Node::Return(Expr::load(c(24), Width::U64));
        let nodes = vec![branch(
            condition.clone(),
            vec![tail.clone()],
            vec![tail.clone()],
        )];
        assert_eq!(
            factor(&nodes).unwrap(),
            vec![Node::Evaluate(condition.clone()), tail]
        );
        let report = compare(&nodes, &[0, 0, 0, 7], &[0; 8]);
        let fault = if matches!(condition, Expr::Load { .. }) {
            (12, Width::U16)
        } else {
            (24, Width::U64)
        };
        assert_eq!(
            report.status,
            RunStatus::Fault(MemoryFault {
                access: AccessKind::Read,
                address: fault.0,
                width: fault.1
            })
        );
    }
    assert_eq!(
        factor(&[branch(r(0), vec![], vec![])]).unwrap(),
        [Node::Evaluate(r(0))]
    );
}

#[test]
fn instruction_pc_and_full_ordered_assignments_are_part_of_equality() {
    for (left, right) in [
        (step(30, vec![set(1, c(7))]), step(31, vec![set(1, c(7))])),
        (
            step(30, vec![set(1, c(7)), set(2, c(8))]),
            step(30, vec![set(2, c(8)), set(1, c(7))]),
        ),
        (
            step(30, vec![store(0, Width::U8, c(7))]),
            step(30, vec![store(0, Width::U16, c(7))]),
        ),
        (step(30, vec![set(1, r(2))]), step(30, vec![set(1, r(3))])),
    ] {
        let nodes = vec![branch(r(0), vec![left], vec![right])];
        assert_eq!(factor(&nodes).unwrap(), nodes);
        compare(&nodes, &[0, 1, 2, 3], &[0; 8]);
        compare(&nodes, &[1, 1, 2, 3], &[0; 8]);
    }
}

#[test]
fn conditions_prefix_stores_and_first_fault_order_remain_exact() {
    let tail = Node::Return(binary(
        BinaryOp::Add,
        Expr::load(c(12), Width::U16),
        Expr::load(c(24), Width::U8),
    ));
    let nodes = vec![branch(
        r(0),
        vec![step(10, vec![store(0, Width::U8, c(1))]), tail.clone()],
        vec![step(20, vec![store(0, Width::U8, c(2))]), tail],
    )];
    for condition in [0, 1] {
        let report = compare(&nodes, &[condition, 0, 0, 0], &[0; 8]);
        assert_eq!(
            report.status,
            RunStatus::Fault(MemoryFault {
                access: AccessKind::Read,
                address: 12,
                width: Width::U16
            })
        );
        assert_eq!(report.memory[0], if condition == 0 { 2 } else { 1 });
    }
    let common = step(30, vec![store(0, Width::U8, c(99))]);
    let nodes = vec![branch(
        binary(
            BinaryOp::Xor,
            Expr::load(c(9), Width::U8),
            Expr::load(c(10), Width::U16),
        ),
        vec![common.clone()],
        vec![common],
    )];
    let report = compare(&nodes, &[0; 4], &[0; 8]);
    assert_eq!(
        report.status,
        RunStatus::Fault(MemoryFault {
            access: AccessKind::Read,
            address: 9,
            width: Width::U8
        })
    );
    assert_eq!(report.memory, [0; 8]);
}

#[test]
fn nested_if_and_loop_bodies_are_factored_recursively() {
    let tail = step(50, vec![set(1, binary(BinaryOp::Add, r(1), c(1)))]);
    let nested = branch(r(2), vec![tail.clone()], vec![tail.clone()]);
    let common_loop = Node::Loop(vec![nested, Node::Break]);
    let nodes = vec![
        branch(r(0), vec![common_loop.clone()], vec![common_loop]),
        Node::Return(r(1)),
    ];
    let output = factor(&nodes).unwrap();
    assert_eq!(output[0], Node::Evaluate(r(0)));
    assert_eq!(
        output[1],
        Node::Loop(vec![Node::Evaluate(r(2)), tail, Node::Break])
    );
    for condition in [0, 1] {
        compare(&nodes, &[condition, 0, 7, 0], &[0; 8]);
    }
}

#[test]
fn common_local_and_outer_breaks_keep_their_lexical_loop_targets() {
    for transfer in [Node::Break, Node::BreakOuter { levels: 1 }] {
        let branched = branch(
            r(0),
            vec![step(10, vec![set(1, c(11))]), transfer.clone()],
            vec![step(20, vec![set(1, c(22))]), transfer.clone()],
        );
        let nested = Node::Loop(vec![branched, step(90, vec![set(1, c(99))])]);
        let nodes = if matches!(transfer, Node::Break) {
            vec![nested, Node::Return(r(1))]
        } else {
            vec![
                Node::Loop(vec![nested, step(91, vec![set(1, c(100))]), Node::Break]),
                Node::Return(r(1)),
            ]
        };
        for condition in [0, 1] {
            let report = compare(&nodes, &[condition, 0, 0, 0], &[0; 8]);
            assert_eq!(
                report.status,
                RunStatus::Returned(if condition == 0 { 22 } else { 11 })
            );
        }
    }
}

#[test]
fn common_continue_and_outer_continue_revisit_the_original_loop() {
    let increment = step(10, vec![set(1, binary(BinaryOp::Add, r(1), c(1)))]);
    for outer in [false, true] {
        let transfer = if outer {
            Node::ContinueOuter { levels: 1 }
        } else {
            Node::Continue
        };
        let branched = branch(
            r(0),
            vec![increment.clone(), transfer.clone()],
            vec![increment.clone(), transfer],
        );
        let body = if outer {
            vec![Node::Loop(vec![branched]), step(90, vec![set(2, c(99))])]
        } else {
            vec![branched]
        };
        let loop_body = vec![branch(
            binary(BinaryOp::Ult, r(1), c(3)),
            body,
            vec![Node::Break],
        )];
        let nodes = vec![Node::Loop(loop_body), Node::Return(r(1))];
        for condition in [0, 1] {
            let report = compare(&nodes, &[condition, 0, 0, 0], &[0; 8]);
            assert_eq!(report.status, RunStatus::Returned(3));
            assert_eq!(report.registers[2], 0);
        }
    }
}

#[test]
fn early_returns_and_breaks_bypass_hoisted_suffix_as_before() {
    let tail = Node::Return(r(1));
    let nodes = vec![branch(
        r(0),
        vec![Node::Return(c(7)), tail.clone()],
        vec![step(20, vec![set(1, c(9))]), tail],
    )];
    assert_eq!(
        compare(&nodes, &[1, 0, 0, 0], &[0; 8]).status,
        RunStatus::Returned(7)
    );
    assert_eq!(
        compare(&nodes, &[0, 0, 0, 0], &[0; 8]).status,
        RunStatus::Returned(9)
    );
}

fn work_bomb(depth: usize, seed: u64) -> Node {
    if depth == 0 {
        return Node::Evaluate(c(seed));
    }
    branch(
        c(seed),
        vec![Node::Loop(vec![work_bomb(depth - 1, seed * 2)])],
        vec![Node::Loop(vec![work_bomb(depth - 1, seed * 2 + 1)])],
    )
}

#[test]
fn whole_input_bounds_cover_expressions_addresses_assignments_depth_and_work() {
    assert_eq!(factor(&[]), Some(vec![]));
    assert!(factor(&vec![Node::Break; MAX_ITEMS + 1]).is_none());
    let mut expression = c(0);
    for _ in 0..MAX_EXPRESSION_DEPTH {
        expression = Expr::load(expression, Width::U8);
    }
    // A deep address on an otherwise unmatched branch must still be validated.
    let nodes = vec![branch(
        r(0),
        vec![step(
            10,
            vec![Assignment {
                destination: Place::Memory {
                    address: expression,
                    width: Width::U8,
                },
                value: c(1),
            }],
        )],
        vec![Node::Break],
    )];
    assert!(factor(&nodes).is_none());
    let mut nested = Node::Break;
    for _ in 0..MAX_NODE_DEPTH {
        nested = Node::Loop(vec![nested]);
    }
    assert!(factor(&[nested]).is_none());
    assert!(factor(&[step(0, vec![set(1, c(0)); MAX_ITEMS / 2])]).is_none());
    // Each unequal arm stays large. Repeated structural comparisons would cost
    // much more than the input's item count without the separate work budget.
    assert!(factor(&[work_bomb(13, 1)]).is_none());
}

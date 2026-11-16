use nirvana::ir::{
    AccessKind, Assignment, BinaryOp, Control, Expr, IrInstruction, MemoryFault, Place, Program,
    Reg, RunReport, RunStatus, Width,
};
use nirvana::loop_shape::{MAX_HEADER_EXPRESSION_DEPTH, MAX_SETUP_ASSIGNMENTS, while_header};
use nirvana::structure::Node;

const BASE: u64 = 0x1000;

fn register(index: usize) -> Expr {
    Expr::Register(Reg(index))
}

fn binary(operator: BinaryOp, left: Expr, right: Expr) -> Expr {
    Expr::binary(operator, left, right)
}

fn assign(destination: usize, value: Expr) -> Assignment {
    Assignment {
        destination: Reg(destination).into(),
        value,
    }
}

fn step(address: u64, assignments: Vec<Assignment>) -> Node {
    Node::Step {
        address,
        assignments,
    }
}

fn guard(condition: Expr, break_when_taken: bool) -> Node {
    Node::If {
        condition,
        taken: if break_when_taken {
            vec![Node::Break]
        } else {
            vec![]
        },
        not_taken: if break_when_taken {
            vec![]
        } else {
            vec![Node::Break]
        },
    }
}

fn instruction(address: u64, assignments: Vec<Assignment>, control: Control) -> IrInstruction {
    IrInstruction {
        address,
        size: 1,
        assignments,
        control,
    }
}

fn evaluate(expression: Expr) -> u64 {
    Program::new(
        0,
        0,
        vec![instruction(0, vec![], Control::Return(expression))],
    )
    .unwrap()
    .execute(&[], 1)
    .unwrap()
    .value
}

#[test]
fn header_borrows_original_step_and_body_slices_with_positions_unchanged() {
    let nodes = vec![
        step(10, vec![assign(2, Expr::load(register(3), Width::U8))]),
        step(
            20,
            vec![assign(4, Expr::Const(1)), assign(4, Expr::Const(2))],
        ),
        guard(binary(BinaryOp::Eq, register(1), Expr::Const(0)), true),
        step(200, vec![assign(0, register(2))]),
        Node::Continue,
    ];
    let header = while_header(&nodes).unwrap();
    assert!(std::ptr::eq(header.setup, &nodes[..2]));
    assert!(std::ptr::eq(header.body, &nodes[3..]));
    assert_eq!(header.setup, &nodes[..2]);
    assert_eq!(header.body.last(), Some(&Node::Continue));
    let Node::Step {
        address,
        assignments,
    } = &header.setup[1]
    else {
        unreachable!()
    };
    assert_eq!(*address, 20);
    assert_eq!(assignments[0], assign(4, Expr::Const(1)));
    assert_eq!(assignments[1], assign(4, Expr::Const(2)));
}

#[test]
fn zero_prefix_and_empty_steps_are_allowed() {
    for prefix in [vec![], vec![step(10, vec![]), step(20, vec![])]] {
        let prefix_len = prefix.len();
        let mut nodes = prefix;
        nodes.push(guard(Expr::Const(7), false));
        let header = while_header(&nodes).unwrap();
        assert_eq!(header.setup.len(), prefix_len);
        assert!(header.body.is_empty());
        assert_eq!(header.condition, Expr::Const(7));
    }
    assert!(while_header(&[]).is_none());
    assert!(while_header(&[step(10, vec![])]).is_none());
}

#[test]
fn continuing_truth_is_correct_for_zero_one_and_arbitrary_nonzero_guards() {
    for value in [0, 1, 2, 7, u64::MAX] {
        for break_when_taken in [false, true] {
            let nodes = [guard(Expr::Const(value), break_when_taken)];
            let header = while_header(&nodes).unwrap();
            assert_eq!(
                evaluate(header.condition) != 0,
                (value != 0) != break_when_taken,
            );
        }
    }
}

// Compile the original guard and the borrowed while header independently into
// CFGs. The original branches to the break target according to its source arm;
// the proposed header branches to the body according to its continuing truth.
// Both retain the same setup steps and execute them again on every continue.
fn loop_program(nodes: &[Node], use_header: bool) -> Program {
    let prefix_len = nodes
        .iter()
        .take_while(|node| matches!(node, Node::Step { .. }))
        .count();
    let Node::If {
        condition,
        taken,
        not_taken,
    } = &nodes[prefix_len]
    else {
        unreachable!()
    };
    let header;
    let (setup, condition, body, target, fallthrough) = if use_header {
        header = while_header(nodes).unwrap();
        (header.setup, header.condition, header.body, 200, 300)
    } else {
        let break_when_taken = matches!(taken.as_slice(), [Node::Break]);
        assert!(taken.is_empty() || not_taken.is_empty());
        (
            &nodes[..prefix_len],
            condition.clone(),
            &nodes[prefix_len + 1..],
            if break_when_taken { 300 } else { 200 },
            if break_when_taken { 200 } else { 300 },
        )
    };
    let entry = match setup.first() {
        Some(Node::Step { address, .. }) => *address,
        None => 100,
        _ => unreachable!(),
    };
    let mut instructions = vec![];
    for (index, node) in setup.iter().enumerate() {
        let Node::Step {
            address,
            assignments,
        } = node
        else {
            unreachable!()
        };
        let next = match setup.get(index + 1) {
            Some(Node::Step { address, .. }) => *address,
            None => 100,
            _ => unreachable!(),
        };
        instructions.push(instruction(
            *address,
            assignments.clone(),
            Control::Jump(next),
        ));
    }
    instructions.push(instruction(
        100,
        vec![],
        Control::Branch { condition, target },
    ));
    instructions.push(instruction(101, vec![], Control::Jump(fallthrough)));
    let mut body_assignments = vec![];
    for node in body {
        match node {
            Node::Step { assignments, .. } => body_assignments.extend(assignments.clone()),
            Node::Continue => {}
            _ => panic!("test lowering supports flat step/continue bodies"),
        }
    }
    instructions.push(instruction(200, body_assignments, Control::Jump(entry)));
    instructions.push(instruction(300, vec![], Control::Return(register(0))));
    Program::new(entry, 5, instructions).unwrap()
}

fn compare_loop(nodes: &[Node], input: [u64; 5], memory: &[u8]) -> RunReport {
    let source = loop_program(nodes, false)
        .run_with_memory(&input, BASE, memory, 1_000)
        .unwrap();
    let header = loop_program(nodes, true)
        .run_with_memory(&input, BASE, memory, 1_000)
        .unwrap();
    assert_eq!(source.status, header.status);
    assert_eq!(source.state.registers, header.state.registers);
    assert_eq!(source.state.memory_base, header.state.memory_base);
    assert_eq!(source.state.memory, header.state.memory);
    assert!(!matches!(source.status, RunStatus::Suspended));
    source
}

#[test]
fn sum_like_loop_repeats_setup_on_continue_and_on_the_final_failed_guard() {
    let nodes = vec![
        step(
            10,
            vec![assign(
                2,
                Expr::load(binary(BinaryOp::Add, register(3), register(1)), Width::U8),
            )],
        ),
        step(
            20,
            vec![assign(
                4,
                binary(BinaryOp::Add, register(4), Expr::Const(1)),
            )],
        ),
        guard(binary(BinaryOp::Eq, register(1), Expr::Const(0)), true),
        step(
            200,
            vec![
                assign(0, binary(BinaryOp::Add, register(0), register(2))),
                assign(1, binary(BinaryOp::Sub, register(1), Expr::Const(1))),
            ],
        ),
        Node::Continue,
    ];
    let memory: Vec<u8> = (0..32).collect();
    for count in 0..16 {
        let report = compare_loop(&nodes, [0, count, 0, BASE, 0], &memory);
        assert_eq!(report.status, RunStatus::Returned(count * (count + 1) / 2));
        assert_eq!(report.state.registers[4], count + 1);
        assert_eq!(report.state.registers[2], 0);
    }
}

#[test]
fn setup_faults_preserve_order_and_prior_register_writes() {
    let nodes = vec![
        step(
            10,
            vec![
                assign(4, Expr::Const(77)),
                assign(2, Expr::load(Expr::Const(12), Width::U16)),
                assign(3, Expr::load(Expr::Const(13), Width::U8)),
            ],
        ),
        guard(Expr::Const(1), true),
    ];
    let report = compare_loop(&nodes, [9, 0, 42, BASE, 0], &[0; 32]);
    assert_eq!(
        report.status,
        RunStatus::Fault(MemoryFault {
            access: AccessKind::Read,
            address: 12,
            width: Width::U16,
        })
    );
    assert_eq!(report.state.registers, [9, 0, 42, BASE, 77]);
    assert_eq!(report.state.instruction, Some(10));
}

#[test]
fn a_later_iteration_fault_retains_previous_body_memory_writes() {
    let nodes = vec![
        step(
            10,
            vec![assign(
                2,
                Expr::load(binary(BinaryOp::Add, register(3), register(1)), Width::U8),
            )],
        ),
        guard(Expr::Const(0), true),
        step(
            200,
            vec![
                Assignment {
                    destination: Place::Memory {
                        address: Expr::Const(BASE + 31),
                        width: Width::U8,
                    },
                    value: register(2),
                },
                assign(1, binary(BinaryOp::Sub, register(1), Expr::Const(1))),
            ],
        ),
        Node::Continue,
    ];
    let mut memory = [0; 32];
    memory[0] = 0x79;
    let report = compare_loop(&nodes, [0, 0, 0, BASE, 0], &memory);
    assert_eq!(
        report.status,
        RunStatus::Fault(MemoryFault {
            access: AccessKind::Read,
            address: BASE - 1,
            width: Width::U8,
        })
    );
    assert_eq!(report.state.registers[1], u64::MAX);
    assert_eq!(report.state.memory[31], 0x79);
}

#[test]
fn guard_load_is_retained_even_when_the_other_operand_forces_its_truth() {
    let condition = binary(
        BinaryOp::Mul,
        Expr::load(Expr::Const(12), Width::U32),
        Expr::Const(0),
    );
    for break_when_taken in [false, true] {
        let nodes = vec![guard(condition.clone(), break_when_taken)];
        let report = compare_loop(&nodes, [9, 0, 42, BASE, 0], &[0; 32]);
        assert_eq!(
            report.status,
            RunStatus::Fault(MemoryFault {
                access: AccessKind::Read,
                address: 12,
                width: Width::U32,
            })
        );
    }
}

#[test]
fn setup_store_and_more_than_sixteen_assignments_are_rejected() {
    let store = Assignment {
        destination: Place::Memory {
            address: Expr::Const(BASE),
            width: Width::U8,
        },
        value: Expr::Const(1),
    };
    assert!(while_header(&[step(10, vec![store]), guard(Expr::Const(1), true)]).is_none());
    let assignments = vec![assign(0, Expr::Const(1)); MAX_SETUP_ASSIGNMENTS];
    let mut nodes = vec![step(10, assignments), guard(Expr::Const(1), true)];
    assert!(while_header(&nodes).is_some());
    nodes.insert(1, step(20, vec![assign(1, Expr::Const(2))]));
    assert!(while_header(&nodes).is_none());
}

#[test]
fn nested_and_multiple_loads_are_rejected_in_both_setup_and_guard() {
    let load = || Expr::load(register(3), Width::U8);
    for expression in [
        Expr::load(load(), Width::U16),
        binary(BinaryOp::Add, load(), load()),
        Expr::select(Expr::Const(0), load(), load()),
        Expr::select(load(), Expr::Const(1), load()),
    ] {
        assert!(while_header(&[guard(expression.clone(), true)]).is_none());
        assert!(
            while_header(&[
                step(10, vec![assign(0, expression)]),
                guard(Expr::Const(1), true),
            ])
            .is_none()
        );
    }
    let lazy = Expr::select(Expr::Const(0), load(), Expr::Const(1));
    assert!(while_header(&[guard(lazy, true)]).is_some());
}

#[test]
fn prefixes_cannot_cross_control_nodes_or_loop_boundaries() {
    for prefix in [
        Node::Evaluate(Expr::Const(0)),
        Node::If {
            condition: Expr::Const(1),
            taken: vec![],
            not_taken: vec![],
        },
        Node::Loop(vec![guard(Expr::Const(1), true)]),
        Node::Continue,
        Node::Break,
        Node::BreakOuter { levels: 1 },
        Node::Return(Expr::Const(0)),
    ] {
        assert!(while_header(&[prefix, guard(Expr::Const(1), true)]).is_none());
    }
}

#[test]
fn guard_must_contain_one_direct_local_break_and_nothing_else() {
    for (taken, not_taken) in [
        (vec![Node::BreakOuter { levels: 1 }], vec![]),
        (vec![Node::BreakOuter { levels: 0 }], vec![]),
        (vec![Node::Loop(vec![Node::Break])], vec![]),
        (
            vec![Node::If {
                condition: Expr::Const(1),
                taken: vec![Node::Break],
                not_taken: vec![],
            }],
            vec![],
        ),
        (vec![Node::Break], vec![Node::Break]),
        (vec![Node::Break], vec![Node::Continue]),
        (vec![Node::Evaluate(Expr::Const(0)), Node::Break], vec![]),
        (vec![], vec![]),
    ] {
        assert!(
            while_header(&[Node::If {
                condition: Expr::Const(1),
                taken,
                not_taken
            }])
            .is_none()
        );
    }
}

#[test]
fn body_may_keep_nested_and_nonlocal_control_without_being_scanned() {
    let nodes = vec![
        guard(Expr::Const(1), false),
        Node::Loop(vec![Node::Break]),
        Node::ContinueOuter { levels: 1 },
        Node::BreakOuter { levels: 2 },
    ];
    let header = while_header(&nodes).unwrap();
    assert!(std::ptr::eq(header.body, &nodes[1..]));
    assert_eq!(header.body, &nodes[1..]);
}

#[test]
fn deeply_nested_expressions_fall_back_without_recursive_inspection() {
    let mut expression = Expr::Const(0);
    for _ in 0..MAX_HEADER_EXPRESSION_DEPTH {
        expression = binary(BinaryOp::Add, expression, Expr::Const(1));
    }
    assert!(while_header(&[guard(expression.clone(), true)]).is_none());
    assert!(
        while_header(&[
            step(10, vec![assign(0, expression)]),
            guard(Expr::Const(1), true),
        ])
        .is_none()
    );
}

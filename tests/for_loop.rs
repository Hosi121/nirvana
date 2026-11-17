use nirvana::for_loop::{ForLoop, MAX_BODY_NODES, MAX_UPDATE_ASSIGNMENTS, recover};
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
fn add(left: Expr, right: Expr) -> Expr {
    Expr::binary(BinaryOp::Add, left, right)
}
fn set(index: usize, value: Expr) -> Assignment {
    Assignment {
        destination: Reg(index).into(),
        value,
    }
}
fn store(address: Expr, value: Expr) -> Assignment {
    Assignment {
        destination: Place::Memory {
            address,
            width: Width::U64,
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
fn guard() -> Node {
    Node::If {
        condition: Expr::binary(BinaryOp::Ult, r(1), r(0)),
        taken: vec![],
        not_taken: vec![Node::Break],
    }
}
fn slot(reg: Reg) -> Option<usize> {
    Some(reg.0)
}
fn normal() -> Vec<Node> {
    vec![
        step(1, vec![set(5, add(r(5), c(1)))]),
        guard(),
        step(2, vec![set(3, add(r(3), r(1)))]),
        step(3, vec![set(1, add(r(1), c(1)))]),
        Node::Continue,
    ]
}

#[derive(Debug, Eq, PartialEq)]
struct Observation {
    status: RunStatus,
    registers: Vec<u64>,
    memory: Vec<u8>,
}
struct Machine {
    registers: Vec<u64>,
    memory: Vec<u8>,
    fuel: usize,
}
#[derive(Debug)]
enum Flow {
    Normal,
    Break,
    Continue,
    Return(u64),
    Stop(RunStatus),
}

impl Machine {
    // Delegate expression and sequential assignment semantics to the executable
    // IR, independent of the recognizer. One AST step or condition consumes one
    // observation unit, so original and for lowering can be checked at cutoffs.
    fn execute(&mut self, assignments: Vec<Assignment>, value: Expr) -> Result<u64, RunStatus> {
        if self.fuel == 0 {
            return Err(RunStatus::Suspended);
        }
        self.fuel -= 1;
        let program = Program::new(
            0,
            self.registers.len(),
            vec![IrInstruction {
                address: 0,
                size: 1,
                assignments,
                control: Control::Return(value),
            }],
        )
        .unwrap();
        let report = program
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
                Node::Step { assignments, .. } => match self.execute(assignments.clone(), c(0)) {
                    Ok(_) => Flow::Normal,
                    Err(status) => Flow::Stop(status),
                },
                Node::Evaluate(value) => match self.execute(vec![], value.clone()) {
                    Ok(_) => Flow::Normal,
                    Err(status) => Flow::Stop(status),
                },
                Node::If {
                    condition,
                    taken,
                    not_taken,
                } => match self.execute(vec![], condition.clone()) {
                    Ok(value) => self.nodes(if value != 0 { taken } else { not_taken }),
                    Err(status) => Flow::Stop(status),
                },
                Node::Return(value) => match self.execute(vec![], value.clone()) {
                    Ok(value) => Flow::Return(value),
                    Err(status) => Flow::Stop(status),
                },
                Node::Break => Flow::Break,
                Node::Continue => Flow::Continue,
                _ => panic!("unsupported transfer in independent test interpreter"),
            };
            if !matches!(flow, Flow::Normal) {
                return flow;
            }
        }
        Flow::Normal
    }
    fn finish(mut self, flow: Flow) -> Observation {
        let status = match flow {
            Flow::Break => match self.execute(vec![], r(3)) {
                Ok(value) => RunStatus::Returned(value),
                Err(status) => status,
            },
            Flow::Return(value) => RunStatus::Returned(value),
            Flow::Stop(status) => status,
            _ => panic!("loop did not exit"),
        };
        Observation {
            status,
            registers: self.registers,
            memory: self.memory,
        }
    }
}

fn original(nodes: &[Node], registers: &[u64; 6], memory: &[u8], fuel: usize) -> Observation {
    let mut machine = Machine {
        registers: registers.to_vec(),
        memory: memory.to_vec(),
        fuel,
    };
    let exit = loop {
        match machine.nodes(nodes) {
            Flow::Normal | Flow::Continue => {}
            exit => break exit,
        }
    };
    machine.finish(exit)
}

fn lowered(plan: &ForLoop<'_>, registers: &[u64; 6], memory: &[u8], fuel: usize) -> Observation {
    let mut machine = Machine {
        registers: registers.to_vec(),
        memory: memory.to_vec(),
        fuel,
    };
    let exit = loop {
        match machine.nodes(plan.setup) {
            Flow::Normal => {}
            exit => break exit,
        }
        match machine.execute(vec![], plan.condition.clone()) {
            Ok(0) => break Flow::Break,
            Ok(_) => {}
            Err(status) => break Flow::Stop(status),
        }
        match machine.nodes(plan.body) {
            Flow::Normal | Flow::Continue => {}
            exit => break exit,
        }
        match machine.nodes(plan.update) {
            Flow::Normal => {}
            exit => break exit,
        }
    };
    machine.finish(exit)
}

fn compare(nodes: &[Node], registers: &[u64; 6], memory: &[u8]) -> Observation {
    let plan = recover(nodes, slot).unwrap();
    for fuel in 0..80 {
        assert_eq!(
            original(nodes, registers, memory, fuel),
            lowered(&plan, registers, memory, fuel),
            "cutoff={fuel}"
        );
    }
    let expected = original(nodes, registers, memory, 1_000);
    assert_eq!(expected, lowered(&plan, registers, memory, 1_000));
    expected
}

#[test]
fn minimal_suffix_borrows_exact_slices_and_retains_final_setup_visit() {
    let nodes = normal();
    let plan = recover(&nodes, slot).unwrap();
    assert!(std::ptr::eq(plan.setup, &nodes[..1]));
    assert!(std::ptr::eq(plan.body, &nodes[2..3]));
    assert!(std::ptr::eq(plan.update, &nodes[3..4]));
    for limit in 0..7 {
        let result = compare(&nodes, &[limit, 0, 0, 0, 0, 0], &[0x5a; 32]);
        assert_eq!(
            result.status,
            RunStatus::Returned(limit * limit.saturating_sub(1) / 2)
        );
        assert_eq!(result.registers[5], limit + 1);
    }
}

#[test]
fn copyback_tails_and_coalesced_virtual_registers_are_supported() {
    let mut nodes = normal();
    nodes[3] = step(3, vec![set(2, add(r(1), c(1)))]);
    nodes.insert(4, step(4, vec![set(1, r(2))]));
    let plan = recover(&nodes, slot).unwrap();
    assert!(std::ptr::eq(plan.update, &nodes[3..5]));
    compare(&nodes, &[5, 0, 0, 0, 0, 0], &[0; 32]);
    let aliases = |reg: Reg| Some(if reg.0 == 2 { 1 } else { reg.0 });
    assert!(recover(&nodes, aliases).is_some());
    nodes.remove(4);
    assert!(recover(&nodes, slot).is_none());
    assert!(recover(&nodes, aliases).is_some());
}

#[test]
fn memory_counter_update_includes_its_adjacent_reload_and_keeps_order() {
    let nodes = vec![
        step(
            1,
            vec![
                set(1, Expr::load(c(0), Width::U64)),
                set(5, add(r(5), c(1))),
            ],
        ),
        guard(),
        step(2, vec![set(3, add(r(3), r(1))), store(c(16), r(3))]),
        step(3, vec![set(1, Expr::load(c(0), Width::U64))]),
        step(4, vec![store(c(0), add(r(1), c(1)))]),
        Node::Continue,
    ];
    let plan = recover(&nodes, slot).unwrap();
    assert!(std::ptr::eq(plan.body, &nodes[2..3]));
    assert!(std::ptr::eq(plan.update, &nodes[3..5]));
    for limit in 0..7 {
        let result = compare(&nodes, &[limit, 0, 0, 0, 0, 0], &[0; 32]);
        assert_eq!(result.registers[5], limit + 1);
        assert_eq!(
            u64::from_le_bytes(result.memory[..8].try_into().unwrap()),
            limit
        );
    }
}

#[test]
fn memory_anchor_does_not_claim_address_alias_and_still_preserves_faults() {
    let mut nodes = normal();
    nodes[3] = step(3, vec![store(c(31), add(r(1), c(1)))]);
    let result = compare(&nodes, &[3, 0, 0, 0, 0, 0], &[0; 32]);
    assert_eq!(
        result.status,
        RunStatus::Fault(MemoryFault {
            access: AccessKind::Write,
            address: 31,
            width: Width::U64,
        })
    );
    assert_eq!(result.registers[5], 1);
}

#[test]
fn guarded_break_and_return_skip_the_update_exactly_as_before() {
    for exit in [
        Node::Break,
        Node::Return(c(77)),
        Node::Return(Expr::load(c(40), Width::U8)),
    ] {
        let mut nodes = normal();
        nodes.insert(
            3,
            Node::If {
                condition: r(2),
                taken: vec![exit],
                not_taken: vec![],
            },
        );
        for enabled in [0, 1, u64::MAX] {
            compare(&nodes, &[3, 0, enabled, 0, 0, 0], &[0; 32]);
        }
    }
}

#[test]
fn trailing_single_load_fault_retains_prior_counter_update_and_body_writes() {
    let mut nodes = normal();
    nodes[2] = step(2, vec![store(c(8), c(0x1234))]);
    nodes.insert(4, step(4, vec![set(2, Expr::load(c(31), Width::U64))]));
    let result = compare(&nodes, &[3, 0, 0, 0, 0, 0], &[0; 32]);
    assert_eq!(
        result.status,
        RunStatus::Fault(MemoryFault {
            access: AccessKind::Read,
            address: 31,
            width: Width::U64,
        })
    );
    assert_eq!(result.registers[1], 1);
    assert_eq!(result.memory[8..16], 0x1234u64.to_le_bytes());
}

#[test]
fn early_continue_nonlocal_transfer_and_nested_loops_are_rejected() {
    for transfer in [
        Node::Continue,
        Node::ContinueOuter { levels: 1 },
        Node::BreakOuter { levels: 1 },
        Node::Loop(vec![Node::Break]),
        Node::If {
            condition: r(2),
            taken: vec![Node::Continue],
            not_taken: vec![],
        },
        Node::If {
            condition: r(2),
            taken: vec![Node::If {
                condition: r(3),
                taken: vec![],
                not_taken: vec![Node::ContinueOuter { levels: 1 }],
            }],
            not_taken: vec![],
        },
    ] {
        let mut nodes = normal();
        nodes.insert(3, transfer);
        assert!(recover(&nodes, slot).is_none());
    }
}

#[test]
fn only_nonzero_affine_self_updates_or_condition_sourced_stores_anchor() {
    for value in [
        add(r(1), c(0)),
        Expr::binary(BinaryOp::Sub, r(1), c(0)),
        Expr::binary(BinaryOp::Sub, c(1), r(1)),
        Expr::binary(BinaryOp::Mul, r(1), c(2)),
        add(r(2), c(1)),
    ] {
        let mut nodes = normal();
        nodes[3] = step(3, vec![set(1, value)]);
        assert!(recover(&nodes, slot).is_none());
    }
    for value in [add(c(2), r(1)), Expr::binary(BinaryOp::Sub, r(1), c(2))] {
        let mut nodes = normal();
        nodes[3] = step(3, vec![set(1, value)]);
        assert!(recover(&nodes, slot).is_some());
    }
    let mut nodes = normal();
    nodes[3] = step(3, vec![set(0, add(r(1), c(1)))]);
    assert!(
        recover(&nodes, slot).is_none(),
        "an unrelated limit assignment is not a self update"
    );
    assert!(recover(&normal(), |_| None).is_none());
}

#[test]
fn moving_requires_load_free_stores_and_at_most_one_load_per_register_rhs() {
    let load = || Expr::load(c(0), Width::U8);
    for assignment in [
        set(2, add(load(), load())),
        set(2, Expr::load(load(), Width::U8)),
        store(load(), c(1)),
        store(c(0), load()),
    ] {
        let mut nodes = normal();
        nodes.insert(4, step(4, vec![assignment]));
        assert!(recover(&nodes, slot).is_none());
    }
}

#[test]
fn terminal_continue_is_optional_and_unrelated_body_steps_stay_outside_update() {
    let mut nodes = normal();
    nodes.pop();
    let plan = recover(&nodes, slot).unwrap();
    assert!(std::ptr::eq(plan.body, &nodes[2..3]));
    assert!(std::ptr::eq(plan.update, &nodes[3..4]));
    compare(&nodes, &[4, 0, 0, 0, 0, 0], &[0; 32]);
}

#[test]
fn resource_limits_return_none_instead_of_partial_recovery() {
    let mut nodes = normal();
    let mut assignments = vec![set(2, c(0)); MAX_UPDATE_ASSIGNMENTS - 1];
    assignments.push(set(1, add(r(1), c(1))));
    nodes[3] = step(3, assignments);
    assert!(recover(&nodes, slot).is_some());
    let Node::Step { assignments, .. } = &mut nodes[3] else {
        unreachable!()
    };
    assignments.push(set(2, c(0)));
    assert!(recover(&nodes, slot).is_none());
    assert!(recover(&vec![Node::Evaluate(c(0)); MAX_BODY_NODES + 1], slot).is_none());
    let mut deep = c(0);
    for _ in 0..129 {
        deep = add(deep, c(1));
    }
    nodes = normal();
    nodes[2] = Node::Evaluate(deep);
    assert!(recover(&nodes, slot).is_none());
}

fn distinct_memory_counter() -> Vec<Node> {
    vec![
        step(1, vec![set(1, Expr::load(r(5), Width::U64))]),
        step(2, vec![set(1, Expr::load(add(c(16), r(1)), Width::U64))]),
        guard(),
        step(3, vec![set(3, add(r(3), c(1)))]),
        step(4, vec![set(4, Expr::load(r(5), Width::U64))]),
        step(5, vec![set(4, add(r(4), c(16)))]),
        step(6, vec![set(2, Expr::load(r(4), Width::U64))]),
        step(7, vec![store(r(4), add(r(2), c(1)))]),
        Node::Continue,
    ]
}

#[test]
fn split_value_and_address_slots_keep_a_memory_counter_for_update() {
    let nodes = distinct_memory_counter();
    let plan = recover(&nodes, slot).unwrap();
    assert!(std::ptr::eq(plan.setup, &nodes[..2]));
    assert!(std::ptr::eq(plan.body, &nodes[3..4]));
    assert!(std::ptr::eq(plan.update, &nodes[4..8]));
    // Physical slots are all distinct: neither address r4 nor reload r2 shares
    // the guard's r1, unlike the accidental address/value coalescing regression.
    for limit in 0..7 {
        let mut memory = [0; 64];
        memory[..8].copy_from_slice(&8u64.to_le_bytes());
        let result = compare(&nodes, &[limit, 0, 0, 0, 0, 0], &memory);
        assert_eq!(result.status, RunStatus::Returned(limit));
        assert_eq!(
            u64::from_le_bytes(result.memory[24..32].try_into().unwrap()),
            limit
        );
    }
}

#[test]
fn symbolic_shapes_never_forward_header_values_across_body_stores() {
    let mut nodes = distinct_memory_counter();
    nodes[3] = step(3, vec![set(3, c(1)), store(c(24), c(6))]);
    let mut memory = [0; 64];
    memory[..8].copy_from_slice(&8u64.to_le_bytes());
    let result = compare(&nodes, &[5, 0, 0, 0, 0, 0], &memory);
    assert_eq!(result.status, RunStatus::Returned(1));
    assert_eq!(
        u64::from_le_bytes(result.memory[24..32].try_into().unwrap()),
        7
    );

    // The pointed-to location itself changes between header and update. The
    // borrowed reloads must read the new pointer and then the new counter.
    nodes[3] = step(
        3,
        vec![set(3, c(1)), store(c(0), c(16)), store(c(32), c(1))],
    );
    let result = compare(&nodes, &[2, 0, 0, 0, 0, 0], &memory);
    assert_eq!(result.status, RunStatus::Returned(1));
    assert_eq!(
        u64::from_le_bytes(result.memory[24..32].try_into().unwrap()),
        0
    );
    assert_eq!(
        u64::from_le_bytes(result.memory[32..40].try_into().unwrap()),
        2
    );

    nodes[3] = step(3, vec![set(3, c(1)), store(c(0), c(56))]);
    let result = compare(&nodes, &[2, 0, 0, 0, 0, 0], &memory);
    assert_eq!(
        result.status,
        RunStatus::Fault(MemoryFault {
            access: AccessKind::Read,
            address: 72,
            width: Width::U64
        })
    );
    assert_eq!(result.registers[4], 72);
    assert_eq!(result.memory[0], 56);
}

#[test]
fn memory_recurrence_requires_matching_read_store_header_width_and_nonzero_delta() {
    for replacement in [
        step(7, vec![store(add(r(4), c(8)), add(r(2), c(1)))]),
        step(7, vec![store(r(4), add(r(2), c(0)))]),
        step(
            7,
            vec![store(r(4), Expr::binary(BinaryOp::Mul, r(2), c(2)))],
        ),
    ] {
        let mut nodes = distinct_memory_counter();
        nodes[7] = replacement;
        assert!(recover(&nodes, slot).is_none());
    }
    let mut nodes = distinct_memory_counter();
    nodes[5] = step(5, vec![set(4, add(r(4), c(24)))]);
    assert!(
        recover(&nodes, slot).is_none(),
        "an unrelated read/store location is not the header counter"
    );
    let mut nodes = distinct_memory_counter();
    nodes[6] = step(6, vec![set(2, Expr::load(r(4), Width::U8))]);
    assert!(recover(&nodes, slot).is_none());
}

#[test]
fn memory_symbol_budget_returns_none_for_the_whole_candidate() {
    fn balanced(first: u64, count: u64) -> Expr {
        if count == 1 {
            return c(first);
        }
        add(
            balanced(first, count / 2),
            balanced(first + count / 2, count / 2),
        )
    }
    let mut nodes = distinct_memory_counter();
    nodes[2] = Node::If {
        condition: Expr::binary(BinaryOp::Ult, r(1), balanced(1, 4096)),
        taken: vec![],
        not_taken: vec![Node::Break],
    };
    assert!(recover(&nodes, slot).is_none());
}

#[test]
fn optional_memory_budget_failure_keeps_an_earlier_existing_slot_anchor() {
    fn balanced(first: u64, count: u64) -> Expr {
        if count == 1 {
            return c(first);
        }
        add(
            balanced(first, count / 2),
            balanced(first + count / 2, count / 2),
        )
    }
    let mut nodes = normal();
    nodes[1] = Node::If {
        condition: Expr::binary(BinaryOp::Ult, r(1), balanced(1, 4096)),
        taken: vec![],
        not_taken: vec![Node::Break],
    };
    nodes.insert(4, step(4, vec![store(c(8), c(7))]));
    let plan = recover(&nodes, slot)
        .expect("optional symbolic failure must not hide the earlier r1 += 1 anchor");
    assert!(std::ptr::eq(plan.body, &nodes[2..3]));
    assert!(std::ptr::eq(plan.update, &nodes[3..5]));
}

#[path = "support/native.rs"]
#[allow(dead_code)]
mod native;

#[test]
fn actual_nested_loops_o0_recovers_inner_update_with_all_register_slots_distinct() {
    use nirvana::{frontend, reduce, structure::StructuredFunction};
    fn remove_empty(nodes: &[Node]) -> Vec<Node> {
        nodes
            .iter()
            .filter_map(|node| match node {
                Node::Step { assignments, .. } if assignments.is_empty() => None,
                Node::If {
                    condition,
                    taken,
                    not_taken,
                } => Some(Node::If {
                    condition: condition.clone(),
                    taken: remove_empty(taken),
                    not_taken: remove_empty(not_taken),
                }),
                Node::Loop(body) => Some(Node::Loop(remove_empty(body))),
                other => Some(other.clone()),
            })
            .collect()
    }
    fn found(nodes: &[Node]) -> bool {
        nodes.iter().any(|node| match node {
            Node::Loop(body) => recover(body, slot).is_some() || found(body),
            Node::If {
                taken, not_taken, ..
            } => found(taken) || found(not_taken),
            _ => false,
        })
    }
    let scratch = native::Scratch::new();
    let object = scratch.0.join("nested-loops-O0.o");
    native::object(
        &native::fixture_root().join("cases/nested-loops.c"),
        &object,
        "-O0",
        "fixture",
    );
    let lifted = frontend::lift_elf(&std::fs::read(object).unwrap(), "fixture").unwrap();
    let reduced = reduce::reduce(&lifted.program).unwrap();
    let structured = StructuredFunction::recover(reduced.program()).unwrap();
    let nodes = remove_empty(structured.body());
    assert!(
        found(&nodes),
        "real inner memory counter must recover without coalesced aliases"
    );
}

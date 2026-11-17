use nirvana::guarded_loop::{Facts, GuardedLoop, MAX_NODES, MAX_SLOTS, recover};
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
fn ne(left: Expr, right: Expr) -> Expr {
    binary(BinaryOp::Ne, left, right)
}
fn set(index: usize, value: Expr) -> Assignment {
    Assignment {
        destination: Reg(index).into(),
        value,
    }
}
fn step(assignments: Vec<Assignment>) -> Node {
    Node::Step {
        address: 10,
        assignments,
    }
}
fn slot(reg: Reg) -> Option<usize> {
    Some(reg.0)
}
fn initial() -> Facts {
    let mut facts = Facts::new(&[0, 2, 3]);
    facts.observe(&step(vec![set(1, c(1))]), slot);
    facts
}
fn latch(condition: Expr, reverse: bool) -> Node {
    Node::If {
        condition,
        taken: vec![if reverse { Node::Break } else { Node::Continue }],
        not_taken: vec![if reverse { Node::Continue } else { Node::Break }],
    }
}
fn loop_taken(prefix: Vec<Node>, condition: Expr, reverse: bool) -> Vec<Node> {
    let mut body = prefix;
    body.push(latch(condition, reverse));
    vec![Node::Loop(body)]
}
fn typical() -> Vec<Node> {
    loop_taken(
        vec![step(vec![
            set(2, binary(BinaryOp::Add, r(2), r(1))),
            set(1, binary(BinaryOp::Add, r(1), c(2))),
        ])],
        ne(r(0), r(1)),
        false,
    )
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
enum Flow {
    Normal,
    Break,
    Continue,
    Return(u64),
    Stop(RunStatus),
}
impl Machine {
    // IR executes each expression/step independently. Fuel counts the same
    // expression tests and sequential assignment groups before/after folding.
    fn execute(
        &mut self,
        assignments: Vec<Assignment>,
        expression: Expr,
    ) -> Result<u64, RunStatus> {
        if self.fuel == 0 {
            return Err(RunStatus::Suspended);
        }
        self.fuel -= 1;
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
        let result = p
            .run_with_memory(&self.registers, 0, &self.memory, 1)
            .unwrap();
        self.registers = result.state.registers;
        self.memory = result.state.memory;
        match result.status {
            RunStatus::Returned(value) => Ok(value),
            other => Err(other),
        }
    }
    fn nodes(&mut self, nodes: &[Node]) -> Flow {
        for node in nodes {
            let flow = match node {
                Node::Step { assignments, .. } => match self.execute(assignments.clone(), c(0)) {
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
                Node::Loop(body) => loop {
                    match self.nodes(body) {
                        Flow::Normal | Flow::Continue => {}
                        Flow::Break => break Flow::Normal,
                        other => break other,
                    }
                },
                Node::Evaluate(expression) => match self.execute(vec![], expression.clone()) {
                    Ok(_) => Flow::Normal,
                    Err(status) => Flow::Stop(status),
                },
                Node::Return(expression) => match self.execute(vec![], expression.clone()) {
                    Ok(value) => Flow::Return(value),
                    Err(status) => Flow::Stop(status),
                },
                Node::Break => Flow::Break,
                Node::Continue => Flow::Continue,
                _ => panic!("nonlocal transfer unsupported in replay"),
            };
            if !matches!(flow, Flow::Normal) {
                return flow;
            }
        }
        Flow::Normal
    }
    fn finish(mut self, flow: Flow) -> Observation {
        let status = match flow {
            Flow::Normal | Flow::Break => match self.execute(vec![], r(2)) {
                Ok(value) => RunStatus::Returned(value),
                Err(status) => status,
            },
            Flow::Return(value) => RunStatus::Returned(value),
            Flow::Stop(status) => status,
            Flow::Continue => panic!("escaped continue"),
        };
        Observation {
            status,
            registers: self.registers,
            memory: self.memory,
        }
    }
}
fn original(
    entry: &Expr,
    taken: &[Node],
    registers: &[u64; 6],
    memory: &[u8],
    fuel: usize,
) -> Observation {
    let mut machine = Machine {
        registers: registers.to_vec(),
        memory: memory.to_vec(),
        fuel,
    };
    let flow = machine.nodes(&[Node::If {
        condition: entry.clone(),
        taken: taken.to_vec(),
        not_taken: vec![],
    }]);
    machine.finish(flow)
}
fn folded(plan: &GuardedLoop<'_>, registers: &[u64; 6], memory: &[u8], fuel: usize) -> Observation {
    let mut machine = Machine {
        registers: registers.to_vec(),
        memory: memory.to_vec(),
        fuel,
    };
    let flow = loop {
        match machine.execute(vec![], plan.condition.clone()) {
            Ok(0) => break Flow::Normal,
            Ok(_) => {}
            Err(status) => break Flow::Stop(status),
        }
        match machine.nodes(plan.body) {
            Flow::Normal | Flow::Continue => {}
            other => break other,
        }
    };
    machine.finish(flow)
}
fn compare(
    entry: &Expr,
    taken: &[Node],
    facts: &Facts,
    registers: &[u64; 6],
    memory: &[u8],
) -> Observation {
    let plan = recover(entry, taken, &[], facts, slot).unwrap();
    for fuel in 0..70 {
        assert_eq!(
            original(entry, taken, registers, memory, fuel),
            folded(&plan, registers, memory, fuel),
            "cutoff={fuel}"
        );
    }
    let expected = original(entry, taken, registers, memory, 500);
    assert_eq!(expected, folded(&plan, registers, memory, 500));
    expected
}

#[test]
fn odd_counter_guard_folds_but_returns_raw_latch_for_every_later_iteration() {
    let taken = typical();
    let facts = initial();
    let entry = ne(r(0), c(1));
    let plan = recover(&entry, &taken, &[], &facts, slot).unwrap();
    let [Node::Loop(nodes)] = taken.as_slice() else {
        unreachable!()
    };
    assert!(std::ptr::eq(plan.body, &nodes[..1]));
    assert_eq!(
        plan.condition,
        ne(r(0), r(1)),
        "proof constants must not escape into the emitted latch"
    );
    for limit in [1u64, 3, 5, 7, 9, 15] {
        let result = compare(&entry, &taken, &facts, &[limit, 1, 0, 0, 0, 0], &[0x5a; 32]);
        let count = (limit - 1) / 2;
        assert_eq!(result.status, RunStatus::Returned(count * count));
        assert_eq!(result.registers[1], limit);
    }
    // Both nonterminating cases retain the same finite prefixes at all cutoffs.
    compare(&entry, &taken, &facts, &[0, 1, 0, 0, 0, 0], &[0; 32]);
}

#[test]
fn reversed_latch_and_constant_left_entry_are_compared_by_truth() {
    let prefix = vec![step(vec![set(1, binary(BinaryOp::Add, r(1), c(2)))])];
    let taken = loop_taken(prefix, binary(BinaryOp::Eq, r(0), r(1)), true);
    let entry = ne(c(1), r(0));
    let plan = recover(&entry, &taken, &[], &initial(), slot).unwrap();
    assert_eq!(
        plan.condition,
        binary(BinaryOp::Eq, binary(BinaryOp::Eq, r(0), r(1)), c(0))
    );
    for limit in [1, 3, 5, 11] {
        compare(
            &entry,
            &taken,
            &initial(),
            &[limit, 1, 0, 0, 0, 0],
            &[0; 16],
        );
    }
    let taken = loop_taken(vec![step(vec![set(2, c(7))])], c(u64::MAX), false);
    assert!(recover(&c(2), &taken, &[], &Facts::new(&[]), slot).is_some());
    assert!(recover(&c(0), &taken, &[], &Facts::new(&[]), slot).is_none());
}

#[test]
fn pure_sequential_constants_and_slot_aliases_are_observed_in_order() {
    let mut facts = Facts::new(&[0]);
    facts.observe(
        &step(vec![
            set(1, c(1)),
            set(1, binary(BinaryOp::Add, r(1), c(2))),
            set(2, r(1)),
        ]),
        slot,
    );
    let taken = loop_taken(
        vec![step(vec![set(1, binary(BinaryOp::Add, r(1), c(2)))])],
        ne(r(0), r(1)),
        false,
    );
    assert!(recover(&ne(r(0), c(3)), &taken, &[], &facts, slot).is_some());
    assert!(recover(&ne(r(0), c(1)), &taken, &[], &facts, slot).is_none());
    let aliases = |reg: Reg| Some(if reg.0 == 4 { 1 } else { reg.0 });
    let mut facts = Facts::new(&[0]);
    facts.observe(&step(vec![set(4, c(1))]), aliases);
    assert!(recover(&ne(r(0), c(1)), &typical(), &[], &facts, aliases).is_some());
}

#[test]
fn unknown_and_load_assignments_initialize_but_kill_constant_values() {
    let mut facts = initial();
    facts.observe(&step(vec![set(1, Expr::load(c(0), Width::U8))]), slot);
    let raw = ne(r(0), r(1));
    assert!(recover(&raw, &typical(), &[], &facts, slot).is_some());
    assert!(recover(&ne(r(0), c(1)), &typical(), &[], &facts, slot).is_none());
    let mut facts = Facts::new(&[0]);
    facts.observe(&step(vec![set(1, r(4))]), slot);
    assert!(recover(&raw, &typical(), &[], &facts, slot).is_some());
}

#[test]
fn every_raw_latch_slot_must_be_initialized_even_if_proof_can_erase_its_read() {
    let facts = Facts::new(&[0]);
    assert!(recover(&ne(r(0), c(1)), &typical(), &[], &facts, slot).is_none());
    let entry = ne(r(0), c(1));
    let hidden = binary(
        BinaryOp::Add,
        entry.clone(),
        binary(BinaryOp::Mul, r(5), c(0)),
    );
    let taken = loop_taken(vec![], hidden, false);
    assert!(recover(&entry, &taken, &[], &facts, slot).is_none());
}

#[test]
fn entry_only_slots_are_rejected_before_constant_substitution() {
    let mut facts = initial();
    facts.observe(&step(vec![set(5, c(0))]), slot);
    let entry = binary(
        BinaryOp::Add,
        ne(r(0), c(1)),
        binary(BinaryOp::Mul, r(5), c(0)),
    );
    assert!(recover(&entry, &typical(), &[], &facts, slot).is_none());
    let missing = |reg: Reg| if reg.0 == 1 { None } else { Some(reg.0) };
    assert!(recover(&ne(r(0), c(1)), &typical(), &[], &initial(), missing).is_none());
}

#[test]
fn branch_and_loop_observation_kill_possible_constants_without_new_initialization() {
    for node in [
        Node::If {
            condition: r(0),
            taken: vec![step(vec![set(1, c(3))])],
            not_taken: vec![],
        },
        Node::Loop(vec![step(vec![set(1, c(3))]), Node::Break]),
    ] {
        let mut facts = initial();
        facts.observe(&node, slot);
        assert!(recover(&ne(r(0), c(1)), &typical(), &[], &facts, slot).is_none());
        assert!(recover(&ne(r(0), r(1)), &typical(), &[], &facts, slot).is_some());
        let mut uninitialized = Facts::new(&[0]);
        uninitialized.observe(&node, slot);
        assert!(recover(&ne(r(0), r(1)), &typical(), &[], &uninitialized, slot).is_none());
    }
}

#[test]
fn enter_loop_prevents_cross_iteration_constant_leakage_and_does_not_mutate_parent() {
    let facts = initial();
    let body = vec![step(vec![set(1, binary(BinaryOp::Add, r(1), c(2)))])];
    let mut inside = facts.enter_loop(&body, slot);
    assert!(recover(&ne(r(0), c(1)), &typical(), &[], &inside, slot).is_none());
    assert!(recover(&ne(r(0), c(1)), &typical(), &[], &facts, slot).is_some());
    inside.observe(&step(vec![set(1, c(1))]), slot);
    assert!(recover(&ne(r(0), c(1)), &typical(), &[], &inside, slot).is_some());
}

#[test]
fn memory_effects_and_faults_inside_prefix_keep_their_original_order() {
    let prefix = vec![step(vec![
        Assignment {
            destination: Place::Memory {
                address: c(0),
                width: Width::U8,
            },
            value: r(1),
        },
        set(1, binary(BinaryOp::Add, r(1), c(2))),
        set(4, Expr::load(r(3), Width::U64)),
    ])];
    let taken = loop_taken(prefix, ne(r(0), r(1)), false);
    let result = compare(
        &ne(r(0), c(1)),
        &taken,
        &initial(),
        &[3, 1, 0, 7, 0, 0],
        &[0; 8],
    );
    assert_eq!(
        result.status,
        RunStatus::Fault(MemoryFault {
            access: AccessKind::Read,
            address: 7,
            width: Width::U64
        })
    );
    assert_eq!(result.memory[0], 1);
    assert_eq!(result.registers[1], 3);
    // False initial guard still performs no prefix memory access.
    compare(
        &ne(r(0), c(1)),
        &taken,
        &initial(),
        &[1, 1, 0, 7, 0, 0],
        &[],
    );
}

#[test]
fn load_guards_early_continues_nonlocal_transfers_and_nested_loops_are_rejected() {
    let load = Expr::load(c(0), Width::U8);
    assert!(recover(&load, &typical(), &[], &initial(), slot).is_none());
    let loaded = loop_taken(vec![], load.clone(), false);
    assert!(recover(&load, &loaded, &[], &initial(), slot).is_none());
    for node in [
        Node::Continue,
        Node::ContinueOuter { levels: 1 },
        Node::BreakOuter { levels: 1 },
        Node::Loop(vec![Node::Break]),
        Node::If {
            condition: r(0),
            taken: vec![Node::Continue],
            not_taken: vec![],
        },
    ] {
        let taken = loop_taken(vec![node], ne(r(0), r(1)), false);
        assert!(recover(&ne(r(0), c(1)), &taken, &[], &initial(), slot).is_none());
    }
    assert!(
        recover(
            &ne(r(0), c(1)),
            &typical(),
            &[Node::Break],
            &initial(),
            slot
        )
        .is_none()
    );
}

#[test]
fn final_pure_copy_can_supply_an_initialized_alias_for_a_latch_temporary() {
    let prefix = vec![
        step(vec![
            set(
                4,
                binary(BinaryOp::And, binary(BinaryOp::Add, r(1), c(1)), c(7)),
            ),
            set(2, binary(BinaryOp::Add, r(2), r(1))),
        ]),
        step(vec![set(1, r(4))]),
    ];
    let taken = loop_taken(prefix, ne(r(0), r(4)), false);
    let entry = ne(r(1), r(0));
    let facts = Facts::new(&[0, 1, 2, 3]);
    let plan = recover(&entry, &taken, &[], &facts, slot).unwrap();
    assert_eq!(plan.condition, ne(r(0), r(1)));
    let [Node::Loop(nodes)] = taken.as_slice() else {
        unreachable!()
    };
    assert!(std::ptr::eq(plan.body, &nodes[..2]));
    assert_eq!(plan.body[1], step(vec![set(1, r(4))]));
    for stop in 0u64..8 {
        let result = compare(
            &entry,
            &taken,
            &facts,
            &[stop, 0, 0, 0, 0xdead_beef, 0],
            &[0x5a; 32],
        );
        assert_eq!(
            result.status,
            RunStatus::Returned(stop * stop.saturating_sub(1) / 2)
        );
        assert_eq!(result.registers[1], stop);
    }
}

#[test]
fn later_copy_writes_and_unused_copy_destinations_cannot_supply_aliases() {
    let facts = Facts::new(&[0, 1, 2, 3]);
    let entry = ne(r(1), r(0));
    for copies in [
        vec![set(1, r(4)), set(4, r(3))],
        vec![set(1, r(4)), set(1, r(3))],
        vec![set(1, r(4)), set(1, c(0))],
        // Replacing a copy destination would leave tmp assigned but never read.
        vec![set(4, r(1))],
    ] {
        let taken = loop_taken(vec![step(copies)], ne(r(0), r(4)), false);
        assert!(recover(&entry, &taken, &[], &facts, slot).is_none());
    }
    // A non-copy step after the copy prevents an end-of-prefix equivalence.
    let taken = loop_taken(
        vec![step(vec![set(1, r(4))]), step(vec![set(4, c(7))])],
        ne(r(0), r(4)),
        false,
    );
    assert!(recover(&entry, &taken, &[], &facts, slot).is_none());
}

#[test]
fn mixed_scalar_write_and_counter_copy_keep_exact_end_value_aliases() {
    let prefix = vec![
        step(vec![set(
            4,
            binary(BinaryOp::And, binary(BinaryOp::Add, r(1), c(1)), c(7)),
        )]),
        step(vec![
            set(
                2,
                binary(
                    BinaryOp::Xor,
                    binary(BinaryOp::Add, r(2), binary(BinaryOp::Shl, r(2), c(5))),
                    r(1),
                ),
            ),
            set(1, r(4)),
        ]),
    ];
    let taken = loop_taken(prefix, ne(r(0), r(4)), false);
    let entry = ne(r(1), r(0));
    let facts = Facts::new(&[0, 1, 2, 3]);
    assert_eq!(
        recover(&entry, &taken, &[], &facts, slot)
            .unwrap()
            .condition,
        ne(r(0), r(1))
    );
    for stop in 0..8 {
        compare(
            &entry,
            &taken,
            &facts,
            &[stop, 0, 17, 0, 99, 0],
            &[0x5a; 32],
        );
    }

    // Exact virtual-register/slot shape observed in the compiled cyclic fixture.
    let named = |reg: Reg| match reg.0 {
        0 => Some(2),
        2 | 50 => Some(3),
        6 | 63 => Some(4),
        141 => Some(5),
        _ => None,
    };
    let actual = loop_taken(
        vec![step(vec![
            set(
                0,
                binary(
                    BinaryOp::Xor,
                    binary(BinaryOp::Add, r(0), binary(BinaryOp::Shl, r(0), c(5))),
                    r(2),
                ),
            ),
            set(2, r(141)),
            set(199, r(198)),
        ])],
        ne(r(6), r(141)),
        false,
    );
    assert_eq!(
        recover(
            &ne(r(50), r(63)),
            &actual,
            &[],
            &Facts::new(&[2, 3, 4]),
            named
        )
        .unwrap()
        .condition,
        ne(r(6), r(50))
    );
}

#[test]
fn fresh_tokens_from_scalar_and_unknown_source_writes_cannot_match_old_values() {
    let facts = Facts::new(&[0, 1, 2, 3]);
    let named = |reg: Reg| (reg.0 < 6).then_some(reg.0);
    for writes in [
        vec![set(1, r(4)), set(4, binary(BinaryOp::Add, r(4), c(1)))],
        vec![set(1, r(4)), set(1, binary(BinaryOp::Xor, r(1), c(7)))],
        vec![set(1, r(4)), set(1, r(99))],
    ] {
        let taken = loop_taken(vec![step(writes)], ne(r(0), r(4)), false);
        assert!(recover(&ne(r(1), r(0)), &taken, &[], &facts, named).is_none());
    }
}

#[test]
fn resource_failure_disables_the_whole_fact_set_and_candidate() {
    let mut facts = initial();
    facts.observe(
        &Node::If {
            condition: c(1),
            taken: vec![Node::Evaluate(c(0)); MAX_NODES + 1],
            not_taken: vec![],
        },
        slot,
    );
    assert!(recover(&ne(r(0), c(1)), &typical(), &[], &facts, slot).is_none());
    let initialized: Vec<_> = (0..=MAX_SLOTS).collect();
    assert!(
        recover(
            &c(1),
            &loop_taken(vec![], c(1), false),
            &[],
            &Facts::new(&initialized),
            slot
        )
        .is_none()
    );
    let mut deep = r(0);
    for _ in 0..65 {
        deep = binary(BinaryOp::Add, deep, c(0));
    }
    assert!(recover(&deep, &typical(), &[], &initial(), slot).is_none());
}

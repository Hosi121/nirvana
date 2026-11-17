use nirvana::{ir, load_mask};
#[allow(dead_code)]
#[path = "support/native.rs"]
mod native;

use ir::{
    AccessKind, Assignment, BinaryOp as B, Control, Expr, IrInstruction, MemoryFault, Place,
    Program, Reg, RunStatus, Width,
};
use load_mask::{LoadMaskError as Error, propose, validate};
use std::collections::BTreeSet;

fn r(n: usize) -> Expr {
    Expr::Register(Reg(n))
}
fn c(n: u64) -> Expr {
    Expr::Const(n)
}
fn b(op: B, a: Expr, z: Expr) -> Expr {
    Expr::binary(op, a, z)
}
fn set(n: usize, value: Expr) -> Assignment {
    Assignment {
        destination: Place::Register(Reg(n)),
        value,
    }
}
fn store(address: Expr, width: Width, value: Expr) -> Assignment {
    Assignment {
        destination: Place::Memory { address, width },
        value,
    }
}
fn program(count: usize, rows: Vec<(Vec<Assignment>, Control)>) -> Program {
    Program::new(
        0,
        count,
        rows.into_iter()
            .enumerate()
            .map(|(i, (assignments, control))| IrInstruction {
                address: i as u64,
                size: 1,
                assignments,
                control,
            })
            .collect(),
    )
    .unwrap()
}
fn replace(program: &Program, mut change: impl FnMut(&mut [IrInstruction])) -> Program {
    let mut instructions = program.instructions().to_vec();
    change(&mut instructions);
    Program::new(
        program.cfg().block(program.cfg().entry()).start,
        program.register_count(),
        instructions,
    )
    .unwrap()
}
fn basic(width: Width, mask: u64) -> Program {
    program(
        7,
        vec![
            (
                vec![
                    store(c(0x1000), Width::U8, c(0xaa)),
                    set(2, Expr::load(r(0), width)),
                    set(4, Expr::load(r(1), Width::U64)),
                ],
                Control::Next,
            ),
            (
                vec![
                    store(r(3), Width::U8, c(0xbb)),
                    set(3, b(B::And, r(2), c(mask))),
                    set(5, Expr::select(r(4), r(3), c(7))),
                ],
                Control::Next,
            ),
            (
                vec![store(b(B::Add, c(0x1000), r(3)), Width::U8, r(4))],
                Control::Return(b(B::Add, r(3), r(5))),
            ),
        ],
    )
}
fn forced(
    original: &Program,
    load: (usize, usize),
    consumer: (usize, usize),
    temp: usize,
    mask: u64,
) -> Program {
    replace(original, |instructions| {
        let value = &mut instructions[load.0].assignments[load.1].value;
        let old = std::mem::replace(value, c(0));
        *value = b(B::And, old, c(mask));
        instructions[consumer.0].assignments[consumer.1].value = r(temp);
    })
}

// A small independent executable observer records every attempted read/store
// and original assignment point. Its arithmetic is specified directly here;
// the unchanged original is also cross-checked against the production IR VM.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Event {
    Read((u64, usize), u64, Width),
    StoreCheck((u64, usize), u64, Width),
    StoreCommit((u64, usize), u64, Width, u64),
}
struct Observer {
    registers: Vec<u64>,
    memory: Vec<u8>,
    base: u64,
    events: Vec<Event>,
    trace: Vec<u64>,
}
impl Observer {
    fn access(&self, address: u64, width: Width, access: AccessKind) -> Result<usize, MemoryFault> {
        address
            .checked_add(width.bytes() as u64 - 1)
            .and_then(|_| address.checked_sub(self.base))
            .and_then(|offset| usize::try_from(offset).ok())
            .filter(|offset| {
                offset
                    .checked_add(width.bytes())
                    .is_some_and(|end| end <= self.memory.len())
            })
            .ok_or(MemoryFault {
                access,
                address,
                width,
            })
    }
    fn value(&mut self, e: &Expr, point: (u64, usize)) -> Result<u64, MemoryFault> {
        Ok(match e {
            Expr::Const(n) => *n,
            Expr::Register(reg) => self.registers[reg.0],
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => {
                if self.value(condition, point)? != 0 {
                    self.value(taken, point)?
                } else {
                    self.value(not_taken, point)?
                }
            }
            Expr::Load { address, width } => {
                let address = self.value(address, point)?;
                self.events.push(Event::Read(point, address, *width));
                let offset = self.access(address, *width, AccessKind::Read)?;
                let mut value = 0;
                for i in 0..width.bytes() {
                    value |= u64::from(self.memory[offset + i]) << (i * 8);
                }
                value
            }
            Expr::Binary(op, a, z) => {
                let a = self.value(a, point)?;
                let z = self.value(z, point)?;
                match op {
                    B::Add => a.wrapping_add(z),
                    B::Sub => a.wrapping_sub(z),
                    B::Mul => a.wrapping_mul(z),
                    B::UMulHigh => ((u128::from(a) * u128::from(z)) >> 64) as u64,
                    B::And => a & z,
                    B::Or => a | z,
                    B::Xor => a ^ z,
                    B::Shl => a.wrapping_shl((z & 63) as u32),
                    B::Shr => a.wrapping_shr((z & 63) as u32),
                    B::Eq => u64::from(a == z),
                    B::Ne => u64::from(a != z),
                    B::Ult => u64::from(a < z),
                    B::Ule => u64::from(a <= z),
                }
            }
        })
    }
    fn step(&mut self, instruction: &IrInstruction) -> Result<Option<u64>, MemoryFault> {
        for (i, assignment) in instruction.assignments.iter().enumerate() {
            let point = (instruction.address, i);
            match &assignment.destination {
                Place::Register(reg) => {
                    let value = self.value(&assignment.value, point)?;
                    self.registers[reg.0] = value;
                }
                Place::Memory { address, width } => {
                    let address = self.value(address, point)?;
                    self.events.push(Event::StoreCheck(point, address, *width));
                    let offset = self.access(address, *width, AccessKind::Write)?;
                    let value = self.value(&assignment.value, point)?;
                    for i in 0..width.bytes() {
                        self.memory[offset + i] = (value >> (i * 8)) as u8;
                    }
                    self.events
                        .push(Event::StoreCommit(point, address, *width, value));
                }
            }
        }
        Ok(match &instruction.control {
            Control::Next => Some(instruction.address + u64::from(instruction.size)),
            Control::Jump(target) => Some(*target),
            Control::Branch { condition, target } => Some(
                if self.value(
                    condition,
                    (instruction.address, instruction.assignments.len()),
                )? != 0
                {
                    *target
                } else {
                    instruction.address + u64::from(instruction.size)
                },
            ),
            Control::Return(_) => None,
        })
    }
    fn run(&mut self, program: &Program) -> RunStatus {
        let mut pc = program.cfg().block(program.cfg().entry()).start;
        for _ in 0..10_000 {
            let instruction = program
                .instructions()
                .iter()
                .find(|i| i.address == pc)
                .unwrap();
            self.trace.push(pc);
            match self.step(instruction) {
                Err(fault) => return RunStatus::Fault(fault),
                Ok(Some(next)) => pc = next,
                Ok(None) => {
                    let Control::Return(value) = &instruction.control else {
                        unreachable!()
                    };
                    return match self
                        .value(value, (instruction.address, instruction.assignments.len()))
                    {
                        Ok(value) => RunStatus::Returned(value),
                        Err(fault) => RunStatus::Fault(fault),
                    };
                }
            }
        }
        RunStatus::Suspended
    }
}
fn replay(
    original: &Program,
    candidate: &Program,
    parameters: &[Reg],
    input: &[u64],
    memory: &[u8],
) {
    let evidence = validate(original, candidate, parameters).unwrap();
    let temps: BTreeSet<_> = evidence.folds.iter().map(|fold| fold.temporary.0).collect();
    let mut before = Observer {
        registers: input.to_vec(),
        memory: memory.to_vec(),
        base: 0x1000,
        events: vec![],
        trace: vec![],
    };
    let mut after = Observer {
        registers: input.to_vec(),
        memory: memory.to_vec(),
        base: 0x1000,
        events: vec![],
        trace: vec![],
    };
    let a = before.run(original);
    let z = after.run(candidate);
    assert_ne!(a, RunStatus::Suspended);
    assert_eq!(
        (&a, &before.memory, &before.events, &before.trace),
        (&z, &after.memory, &after.events, &after.trace)
    );
    for (i, (a, z)) in before.registers.iter().zip(&after.registers).enumerate() {
        if !temps.contains(&i) {
            assert_eq!(a, z, "unmodified register{i}");
        }
    }
    let reference = original
        .run_with_memory(input, 0x1000, memory, 10000)
        .unwrap();
    assert_eq!(a, reference.status);
    assert_eq!(before.memory, reference.state.memory);
    assert_eq!(before.registers, reference.state.registers);
    assert_eq!(before.trace, reference.state.trace);
}

#[test]
fn masks_stay_at_load_sites_and_preserve_faults_prior_stores_and_lazy_work() {
    let addresses = [0x1000, 0x1001, 0x1078, 0x107f, 0x0fff, u64::MAX];
    let memory: Vec<_> = (0..128usize).map(|i| (i * 29 + 7) as u8).collect();
    let mut cases = 0;
    for width in [Width::U8, Width::U16, Width::U32, Width::U64] {
        for mask in [0, 7] {
            let original = basic(width, mask);
            let candidate = propose(&original, &[Reg(0), Reg(1), Reg(3)]).unwrap();
            let evidence = validate(&original, &candidate, &[Reg(0), Reg(1), Reg(3)]).unwrap();
            assert_eq!(evidence.folds.len(), 1);
            let fold = &evidence.folds[0];
            assert_eq!(
                (
                    fold.load_instruction,
                    fold.load_assignment,
                    fold.consumer_instruction,
                    fold.consumer_assignment
                ),
                (0, 1, 1, 1)
            );
            for a in addresses {
                for z in addresses {
                    for store in addresses {
                        let input = [a, z, u64::MAX, store, 11, 29, 31];
                        replay(
                            &original,
                            &candidate,
                            &[Reg(0), Reg(1), Reg(3)],
                            &input,
                            &memory,
                        );
                        cases += 1;
                    }
                }
            }
        }
    }
    println!("{cases} exact read/check/commit traces and partial-memory/register cases");
}

#[test]
fn loops_reapply_the_same_pointwise_rule_without_initial_value_assumptions() {
    let original = program(
        5,
        vec![
            (vec![set(2, Expr::load(r(0), Width::U64))], Control::Next),
            (
                vec![set(3, b(B::And, r(2), c(7))), set(4, b(B::Sub, r(4), c(1)))],
                Control::Branch {
                    condition: r(4),
                    target: 0,
                },
            ),
            (vec![], Control::Return(r(3))),
        ],
    );
    let candidate = propose(&original, &[Reg(0), Reg(4)]).unwrap();
    for iterations in 1..=4 {
        for address in [0x1000, 0x1078, 0x107f, u64::MAX] {
            replay(
                &original,
                &candidate,
                &[Reg(0), Reg(4)],
                &[address, 0, 0xdead, 0xbeef, iterations],
                &[0xf5; 128],
            );
        }
    }
}

#[test]
fn nested_address_loads_keep_raw_addresses_widths_and_execution_order() {
    let original = program(
        4,
        vec![(
            vec![
                set(2, Expr::load(Expr::load(r(0), Width::U64), Width::U16)),
                set(3, b(B::And, c(31), r(2))),
            ],
            Control::Return(r(3)),
        )],
    );
    let candidate = propose(&original, &[Reg(0)]).unwrap();
    for address in [0x1000, 0x107f, u64::MAX] {
        for nested in [0x1008u64, 0x107f, u64::MAX] {
            let mut memory = vec![0x8f; 128];
            memory[..8].copy_from_slice(&nested.to_le_bytes());
            replay(
                &original,
                &candidate,
                &[Reg(0)],
                &[address, 9, 11, 13],
                &memory,
            );
        }
    }
    let select = replace(&original, |rows| {
        rows[0].assignments[0].value = Expr::load(Expr::select(c(1), r(0), c(0)), Width::U16)
    });
    assert!(propose(&select, &[Reg(0)]).is_none());
    assert!(validate(&select, &forced(&select, (0, 0), (0, 1), 2, 31), &[Reg(0)]).is_err());
}

#[test]
fn multiple_pairs_validate_independently_and_identity_keeps_every_load() {
    let original = program(
        6,
        vec![(
            vec![
                set(2, Expr::load(r(0), Width::U64)),
                set(3, Expr::load(r(1), Width::U8)),
                set(4, b(B::And, r(2), c(7))),
                set(5, b(B::And, c(3), r(3))),
            ],
            Control::Return(b(B::Add, r(4), r(5))),
        )],
    );
    let candidate = propose(&original, &[Reg(0), Reg(1)]).unwrap();
    let evidence = validate(&original, &candidate, &[Reg(0), Reg(1)]).unwrap();
    assert_eq!(evidence.folds.len(), 2);
    assert_eq!(evidence.folds[0].load_assignment, 0);
    assert_eq!(evidence.folds[1].load_assignment, 1);
    replay(
        &original,
        &candidate,
        &[Reg(0), Reg(1)],
        &[0x1000, 0x1008, 0, 0, 0, 0],
        &[0xff; 128],
    );
    assert!(
        validate(&original, &original, &[])
            .unwrap()
            .folds
            .is_empty()
    );
    let full = program(
        4,
        vec![(
            vec![
                set(2, Expr::load(r(0), Width::U64)),
                set(3, b(B::And, r(2), c(u64::MAX))),
            ],
            Control::Return(r(3)),
        )],
    );
    assert!(propose(&full, &[]).is_none());
    let manually_valid = forced(&full, (0, 0), (0, 1), 2, u64::MAX);
    replay(
        &full,
        &manually_valid,
        &[],
        &[0x1000, 0, 0, 0],
        &[0xaf; 128],
    );
}

#[test]
fn distinct_syntactic_reads_definitions_inputs_and_actual_cfg_membership_are_required() {
    let source = basic(Width::U64, 7);
    let candidate = forced(&source, (0, 1), (1, 1), 2, 7);
    for parameters in [
        vec![Reg(2)],
        vec![Reg(0), Reg(0)],
        vec![Reg(7)],
        vec![Reg(usize::MAX)],
    ] {
        assert!(propose(&source, &parameters).is_none());
        assert!(validate(&source, &candidate, &parameters).is_err());
    }
    for extra in [
        r(2),
        b(B::Add, r(2), r(2)),
        Expr::select(c(0), r(2), c(0)),
        Expr::load(r(2), Width::U8),
    ] {
        let other = replace(&source, |rows| {
            rows[1].assignments.push(set(6, extra.clone()))
        });
        assert!(propose(&other, &[]).is_none());
        assert!(validate(&other, &forced(&other, (0, 1), (1, 1), 2, 7), &[]).is_err());
    }
    let address_use = replace(&source, |rows| {
        rows[1].assignments.push(store(r(2), Width::U8, c(3)))
    });
    assert!(propose(&address_use, &[]).is_none());
    assert!(
        validate(
            &address_use,
            &forced(&address_use, (0, 1), (1, 1), 2, 7),
            &[]
        )
        .is_err()
    );
    let twice = replace(&source, |rows| rows[0].assignments.insert(0, set(2, c(9))));
    assert!(propose(&twice, &[]).is_none());
    assert!(validate(&twice, &forced(&twice, (0, 2), (1, 1), 2, 7), &[]).is_err());
    let self_destination = replace(&source, |rows| {
        rows[1].assignments[1].destination = Place::Register(Reg(2))
    });
    assert!(propose(&self_destination, &[]).is_none());
    assert!(
        validate(
            &self_destination,
            &forced(&self_destination, (0, 1), (1, 1), 2, 7),
            &[]
        )
        .is_err()
    );
    let incoming = program(
        4,
        vec![(
            vec![
                set(3, b(B::And, r(2), c(7))),
                set(2, Expr::load(r(0), Width::U64)),
            ],
            Control::Return(r(3)),
        )],
    );
    assert!(propose(&incoming, &[]).is_none());
    assert!(validate(&incoming, &forced(&incoming, (0, 1), (0, 0), 2, 7), &[]).is_err());
    let cross = program(
        4,
        vec![
            (vec![set(2, Expr::load(r(0), Width::U64))], Control::Jump(1)),
            (vec![set(3, b(B::And, r(2), c(7)))], Control::Return(r(3))),
        ],
    );
    assert!(propose(&cross, &[]).is_none());
    assert!(validate(&cross, &forced(&cross, (0, 0), (1, 0), 2, 7), &[]).is_err());
    let memory_consumer = program(
        3,
        vec![(
            vec![
                set(2, Expr::load(r(0), Width::U64)),
                store(r(1), Width::U64, b(B::And, r(2), c(7))),
            ],
            Control::Return(c(0)),
        )],
    );
    assert!(propose(&memory_consumer, &[]).is_none());
    assert!(
        validate(
            &memory_consumer,
            &forced(&memory_consumer, (0, 0), (0, 1), 2, 7),
            &[]
        )
        .is_err()
    );
}

#[test]
fn validator_checks_candidate_syntax_not_the_proposers_preferred_spelling() {
    let source = basic(Width::U64, 7);
    let valid = forced(&source, (0, 1), (1, 1), 2, 7);
    let commuted = replace(&valid, |rows| {
        let Expr::Binary(_, a, z) = &mut rows[0].assignments[1].value else {
            unreachable!()
        };
        std::mem::swap(a, z);
    });
    validate(&source, &commuted, &[]).unwrap();
    for mutant in [
        replace(&valid, |rows| {
            rows[0].assignments[1].value = b(B::And, Expr::load(r(1), Width::U64), c(7))
        }),
        replace(&valid, |rows| {
            rows[0].assignments[1].value = b(B::And, Expr::load(r(0), Width::U32), c(7))
        }),
        replace(&valid, |rows| {
            rows[0].assignments[1].value = b(B::And, Expr::load(r(0), Width::U64), c(3))
        }),
        replace(&valid, |rows| rows[1].assignments[1].value = r(4)),
        replace(&valid, |rows| {
            rows[1].assignments[1].destination = Place::Register(Reg(6))
        }),
        replace(&valid, |rows| rows[0].assignments[0].value = c(99)),
        replace(&valid, |rows| rows[2].control = Control::Return(r(4))),
        replace(&valid, |rows| {
            rows[1].assignments.remove(0);
        }),
        replace(&valid, |rows| {
            rows[0].assignments[1].value = Expr::load(r(0), Width::U64)
        }),
    ] {
        assert!(validate(&source, &mutant, &[]).is_err());
    }
    let unreachable = program(
        4,
        vec![
            (vec![], Control::Return(c(1))),
            (
                vec![
                    set(2, Expr::load(r(0), Width::U64)),
                    set(3, b(B::And, r(2), c(7))),
                ],
                Control::Return(r(3)),
            ),
        ],
    );
    assert!(propose(&unreachable, &[]).is_none());
    assert!(
        validate(
            &unreachable,
            &forced(&unreachable, (1, 0), (1, 1), 2, 7),
            &[]
        )
        .is_err()
    );
}

#[test]
fn whole_input_bounds_precede_clones_and_no_partial_folds_escape() {
    let original = basic(Width::U64, 7);
    let mut deep = c(0);
    for _ in 0..=load_mask::MAX_DEPTH {
        deep = b(B::Add, deep, c(0));
    }
    let deep = replace(&original, |rows| {
        rows[2].control = Control::Return(deep.clone())
    });
    assert!(propose(&deep, &[]).is_none());
    assert!(validate(&deep, &deep, &[]).unwrap_err().is_resource_limit());
    let huge_registers = Program::new(
        0,
        load_mask::MAX_REGISTERS + 1,
        vec![IrInstruction {
            address: 0,
            size: 1,
            assignments: vec![],
            control: Control::Return(c(0)),
        }],
    )
    .unwrap();
    assert!(propose(&huge_registers, &[]).is_none());
    assert!(
        validate(&huge_registers, &huge_registers, &[])
            .unwrap_err()
            .is_resource_limit()
    );
    let too_many = program(
        4,
        vec![(
            vec![set(3, c(0)); load_mask::MAX_ASSIGNMENTS + 1],
            Control::Return(r(3)),
        )],
    );
    assert!(propose(&too_many, &[]).is_none());
    assert!(
        validate(&too_many, &too_many, &[])
            .unwrap_err()
            .is_resource_limit()
    );
    let mut assignments = Vec::new();
    for i in 0..=load_mask::MAX_FOLDS {
        let temp = 2 + i * 2;
        assignments.extend([
            set(temp, Expr::load(r(0), Width::U64)),
            set(temp + 1, b(B::And, r(temp), c(7))),
        ]);
    }
    let folds = program(
        2 + (load_mask::MAX_FOLDS + 1) * 2,
        vec![(assignments, Control::Return(c(0)))],
    );
    assert!(propose(&folds, &[]).is_none());
    let candidate = replace(&folds, |rows| {
        for i in 0..=load_mask::MAX_FOLDS {
            let temp = 2 + i * 2;
            let load = rows[0].assignments[i * 2].value.clone();
            rows[0].assignments[i * 2].value = b(B::And, load, c(7));
            rows[0].assignments[i * 2 + 1].value = r(temp);
        }
    });
    assert_eq!(validate(&folds, &candidate, &[]), Err(Error::ResourceLimit));
}

#[test]
fn node_instruction_block_and_wrapped_depth_bounds_cover_unrelated_code() {
    fn balanced(leaves: usize) -> Expr {
        if leaves == 1 {
            return c(0);
        }
        b(B::Add, balanced(leaves / 2), balanced(leaves - leaves / 2))
    }
    let nodes = program(
        0,
        vec![
            (vec![], Control::Return(c(0))),
            (
                vec![],
                Control::Return(balanced(load_mask::MAX_NODES / 2 + 1)),
            ),
        ],
    );
    assert!(propose(&nodes, &[]).is_none());
    assert!(
        validate(&nodes, &nodes, &[])
            .unwrap_err()
            .is_resource_limit()
    );
    let instructions = program(
        0,
        (0..=load_mask::MAX_INSTRUCTIONS)
            .map(|i| {
                (
                    vec![],
                    if i == load_mask::MAX_INSTRUCTIONS {
                        Control::Return(c(0))
                    } else {
                        Control::Next
                    },
                )
            })
            .collect(),
    );
    assert!(propose(&instructions, &[]).is_none());
    assert!(
        validate(&instructions, &instructions, &[])
            .unwrap_err()
            .is_resource_limit()
    );
    let blocks = program(
        0,
        (0..=load_mask::MAX_BLOCKS)
            .map(|i| {
                (
                    vec![],
                    if i == load_mask::MAX_BLOCKS {
                        Control::Return(c(0))
                    } else {
                        Control::Jump(i as u64 + 1)
                    },
                )
            })
            .collect(),
    );
    assert!(propose(&blocks, &[]).is_none());
    assert!(
        validate(&blocks, &blocks, &[])
            .unwrap_err()
            .is_resource_limit()
    );
    let mut address = r(0);
    for _ in 0..load_mask::MAX_DEPTH - 2 {
        address = b(B::Add, address, c(0));
    }
    let depth = program(
        4,
        vec![(
            vec![
                set(2, Expr::load(address, Width::U64)),
                set(3, b(B::And, r(2), c(7))),
            ],
            Control::Return(r(3)),
        )],
    );
    assert!(validate(&depth, &depth, &[]).is_ok());
    assert!(
        propose(&depth, &[]).is_none(),
        "reserve wrapping depth before cloning"
    );
    let too_deep = forced(&depth, (0, 0), (0, 1), 2, 7);
    assert!(
        validate(&depth, &too_deep, &[])
            .unwrap_err()
            .is_resource_limit()
    );
}

#[test]
fn sparse_register_labels_do_not_require_dense_use_tables() {
    let temp = load_mask::MAX_REGISTERS - 2;
    let destination = temp + 1;
    let original = program(
        load_mask::MAX_REGISTERS,
        vec![(
            vec![
                set(temp, Expr::load(r(0), Width::U64)),
                set(destination, b(B::And, r(temp), c(7))),
            ],
            Control::Return(r(destination)),
        )],
    );
    let candidate = propose(&original, &[Reg(0)]).unwrap();
    let evidence = validate(&original, &candidate, &[Reg(0)]).unwrap();
    assert_eq!(evidence.folds[0].temporary, Reg(temp));
    assert_eq!(candidate.register_count(), original.register_count());
}

#[test]
#[ignore = "requires pinned NIRVANA_Z3; actual block-memory obligations and negative controls"]
fn actual_sum_candidates_have_all_live_outputs_and_memory_fault_obligations() {
    use nirvana::{
        block_verify::{self, BlockVerdict},
        verify::Solver,
    };
    let solver = Solver::new(std::env::var_os("NIRVANA_Z3").expect("set NIRVANA_Z3"));
    let scratch = native::Scratch::new();
    for (name, path) in [
        ("sum", "cases/sum.c"),
        ("seeded-sum", "recovery/seeded-sum.c"),
    ] {
        let object = scratch.0.join(format!("{name}.o"));
        native::object(
            &native::fixture_root().join(path),
            &object,
            "-O2",
            "fixture",
        );
        let lifted =
            nirvana::frontend::lift_elf(&std::fs::read(object).unwrap(), "fixture").unwrap();
        let source = nirvana::reduce::reduce(&lifted.program).unwrap();
        let candidate = propose(source.program(), source.parameters()).unwrap();
        let own = validate(source.program(), &candidate, source.parameters()).unwrap();
        assert_eq!(own.folds.len(), 1);
        let evidence = block_verify::validate_program(source.program(), &candidate, &solver);
        assert!(evidence.accepted(), "{name}: {evidence:?}");
        assert!(evidence.blocks[0].required_outputs.contains(&Reg(2)));
        assert!(
            !evidence.blocks[0]
                .required_outputs
                .contains(&own.folds[0].temporary)
        );
        nirvana::structure::StructuredFunction::recover(&candidate).unwrap();
        println!(
            "{name}: {} independent checked-memory-block-v1 obligations",
            evidence.blocks.len()
        );
    }
    // Boundary-live T must not be treated as an unobserved temporary.
    let boundary = program(
        4,
        vec![
            (
                vec![
                    set(2, Expr::load(r(0), Width::U64)),
                    set(3, b(B::And, r(2), c(7))),
                ],
                Control::Jump(1),
            ),
            (vec![], Control::Return(r(2))),
        ],
    );
    let bad = forced(&boundary, (0, 0), (0, 1), 2, 7);
    assert!(validate(&boundary, &bad, &[Reg(0)]).is_err());
    let verdict = block_verify::validate_program(&boundary, &bad, &solver);
    assert!(!verdict.accepted());
    assert!(verdict.blocks[0].required_outputs.contains(&Reg(2)));
    assert!(matches!(
        verdict.blocks[0].verdict,
        BlockVerdict::Counterexample(_)
    ));
    // A lazy consumer changes whether the original mandatory load faults.
    let lazy = program(
        4,
        vec![(
            vec![
                set(2, Expr::load(r(0), Width::U64)),
                set(3, Expr::select(r(1), r(2), c(0))),
            ],
            Control::Return(r(3)),
        )],
    );
    let lazy_bad = replace(&lazy, |rows| {
        rows[0].assignments[0].value = Expr::select(r(1), Expr::load(r(0), Width::U64), c(0));
        rows[0].assignments[1].value = r(2);
    });
    assert!(validate(&lazy, &lazy_bad, &[]).is_err());
    assert!(matches!(
        block_verify::block_query(&lazy, &lazy_bad, 0, &[Reg(0), Reg(1)], &[])
            .unwrap()
            .check(&solver),
        BlockVerdict::Counterexample(_)
    ));
    // Idempotent read coalescing passes the semantic memory model, yet must
    // fail this stricter exact read-count schema.
    let reads = program(
        4,
        vec![(
            vec![
                set(2, Expr::load(r(0), Width::U64)),
                set(3, Expr::load(r(0), Width::U64)),
            ],
            Control::Return(r(3)),
        )],
    );
    let fewer = replace(&reads, |rows| rows[0].assignments[1].value = r(2));
    assert!(validate(&reads, &fewer, &[]).is_err());
    assert_eq!(
        block_verify::block_query(&reads, &fewer, 0, &[Reg(0)], &[])
            .unwrap()
            .check(&solver),
        BlockVerdict::EquivalentUnderModel
    );
}

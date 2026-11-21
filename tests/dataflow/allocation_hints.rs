use nirvana::allocation::{LocalAllocation, allocate_locals, allocate_locals_with_hints};
use nirvana::ir::{Assignment, BinaryOp, Control, Expr, IrInstruction, Place, Program, Reg, Width};

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
fn ins(address: u64, assignments: Vec<Assignment>, control: Control) -> IrInstruction {
    IrInstruction {
        address,
        size: 1,
        assignments,
        control,
    }
}
fn allocation_vector(a: &LocalAllocation, eligible: &[Reg]) -> Vec<Option<usize>> {
    eligible.iter().map(|&reg| a.color(reg)).collect()
}
fn equivalent_allocation(a: &LocalAllocation, z: &LocalAllocation, eligible: &[Reg]) {
    assert_eq!(a.colors(), z.colors());
    assert_eq!(
        allocation_vector(a, eligible),
        allocation_vector(z, eligible)
    );
}
fn two_phases() -> Program {
    Program::new(
        0,
        4,
        vec![ins(
            0,
            vec![
                set(1, r(0)),
                set(2, b(BinaryOp::Add, r(0), c(3))),
                store(c(0), Width::U64, b(BinaryOp::Xor, r(1), r(2))),
                set(3, b(BinaryOp::Add, r(0), c(9))),
            ],
            Control::Return(r(3)),
        )],
    )
    .unwrap()
}

// This relabeler does not use allocator internals. Every eligible value moves
// into a fresh bank initialized with poison; inputs keep their original IDs.
fn remap(program: &Program, allocation: &LocalAllocation) -> Program {
    fn expression(value: &Expr, map: &impl Fn(Reg) -> Reg) -> Expr {
        match value {
            Expr::Const(_) => value.clone(),
            Expr::Register(reg) => Expr::Register(map(*reg)),
            Expr::Binary(op, a, z) => b(*op, expression(a, map), expression(z, map)),
            Expr::Load { address, width } => Expr::load(expression(address, map), *width),
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => Expr::select(
                expression(condition, map),
                expression(taken, map),
                expression(not_taken, map),
            ),
        }
    }
    let bank = program.register_count();
    let map = |reg: Reg| allocation.color(reg).map_or(reg, |color| Reg(bank + color));
    let instructions = program
        .instructions()
        .iter()
        .map(|instruction| {
            let assignments = instruction
                .assignments
                .iter()
                .map(|assignment| Assignment {
                    destination: match &assignment.destination {
                        Place::Register(reg) => Place::Register(map(*reg)),
                        Place::Memory { address, width } => Place::Memory {
                            address: expression(address, &map),
                            width: *width,
                        },
                    },
                    value: expression(&assignment.value, &map),
                })
                .collect();
            let control = match &instruction.control {
                Control::Branch { condition, target } => Control::Branch {
                    condition: expression(condition, &map),
                    target: *target,
                },
                Control::Return(value) => Control::Return(expression(value, &map)),
                other => other.clone(),
            };
            IrInstruction {
                assignments,
                control,
                ..instruction.clone()
            }
        })
        .collect();
    Program::new(
        program.cfg().block(program.cfg().entry()).start,
        bank + allocation.colors(),
        instructions,
    )
    .unwrap()
}
fn replay(
    program: &Program,
    allocation: &LocalAllocation,
    input: &[u64],
    memory: &[u8],
    limits: &[usize],
) {
    let mapped = remap(program, allocation);
    let mut poisoned = input.to_vec();
    poisoned.resize(mapped.register_count(), 0x95d3_7fba_02c1_864e);
    for &limit in limits {
        let expected = program.run_with_memory(input, 0, memory, limit).unwrap();
        let actual = mapped.run_with_memory(&poisoned, 0, memory, limit).unwrap();
        assert_eq!(
            actual.status, expected.status,
            "limit={limit}, input={input:?}"
        );
        assert_eq!(actual.state.memory, expected.state.memory);
        assert_eq!(actual.state.memory_base, expected.state.memory_base);
        assert_eq!(actual.state.trace, expected.state.trace);
        assert_eq!(actual.state.instruction, expected.state.instruction);
    }
}

#[test]
fn hints_join_nonoverlapping_versions_at_the_same_storage_count() {
    let program = two_phases();
    let eligible = [Reg(1), Reg(2), Reg(3)];
    let ordinary = allocate_locals(&program, &eligible).unwrap();
    let hinted = allocate_locals_with_hints(&program, &eligible, &[(Reg(2), Reg(3))]).unwrap();
    assert_ne!(ordinary.color(Reg(2)), ordinary.color(Reg(3)));
    assert_eq!(hinted.color(Reg(2)), hinted.color(Reg(3)));
    assert_eq!(hinted.colors(), ordinary.colors());
    for input in [0, 1, 255, 1 << 63, u64::MAX] {
        for memory in [&[][..], &[0x5a; 8][..]] {
            replay(&program, &hinted, &[input, 17, 18, 19], memory, &[0, 1, 2]);
        }
    }
}

#[test]
fn simultaneous_operands_and_later_overwrites_resist_preferences() {
    let program = Program::new(
        0,
        4,
        vec![ins(
            0,
            vec![
                set(1, r(0)),
                set(2, r(1)),
                set(1, c(11)),
                set(3, b(BinaryOp::Add, r(1), r(2))),
            ],
            Control::Return(r(3)),
        )],
    )
    .unwrap();
    let eligible = [Reg(1), Reg(2), Reg(3)];
    let allocation =
        allocate_locals_with_hints(&program, &eligible, &[(Reg(1), Reg(2)), (Reg(2), Reg(3))])
            .unwrap();
    assert_ne!(allocation.color(Reg(1)), allocation.color(Reg(2)));
    assert!(allocation.colors() <= allocate_locals(&program, &eligible).unwrap().colors());
    for input in [0, 1, 255, u64::MAX] {
        replay(&program, &allocation, &[input, 71, 72, 73], &[], &[0, 1, 2]);
    }
}

#[test]
fn empty_invalid_and_excessive_hints_return_the_exact_ordinary_result() {
    let program = two_phases();
    let eligible = [Reg(3), Reg(1), Reg(2)];
    let ordinary = allocate_locals(&program, &eligible).unwrap();
    let cases = vec![
        vec![],
        vec![(Reg(2), Reg(3)), (Reg(0), Reg(1))],
        vec![(Reg(2), Reg(3)), (Reg(1), Reg(999))],
        vec![(Reg(2), Reg(3)); 8193],
    ];
    for hints in cases {
        let allocation = allocate_locals_with_hints(&program, &eligible, &hints).unwrap();
        equivalent_allocation(&allocation, &ordinary, &eligible);
    }
    assert!(allocate_locals_with_hints(&program, &[Reg(0)], &[(Reg(0), Reg(0))]).is_none());
    assert!(allocate_locals_with_hints(&program, &[Reg(1), Reg(1)], &[]).is_none());
}

#[test]
fn hint_order_duplicates_and_sparse_register_ids_are_deterministic() {
    let program = Program::new(
        0,
        1001,
        vec![ins(
            0,
            vec![
                set(7, r(0)),
                set(99, b(BinaryOp::Add, r(0), c(3))),
                store(c(0), Width::U64, b(BinaryOp::Xor, r(7), r(99))),
                set(1000, c(9)),
            ],
            Control::Return(r(1000)),
        )],
    )
    .unwrap();
    let eligible = [Reg(7), Reg(99), Reg(1000)];
    let a = allocate_locals_with_hints(&program, &eligible, &[(Reg(99), Reg(1000))]).unwrap();
    let z = allocate_locals_with_hints(
        &program,
        &[Reg(1000), Reg(99), Reg(7)],
        &[(Reg(1000), Reg(99)), (Reg(99), Reg(1000)), (Reg(7), Reg(7))],
    )
    .unwrap();
    equivalent_allocation(&a, &z, &eligible);
    assert_eq!(a.color(Reg(99)), a.color(Reg(1000)));
    assert_eq!(a.color(Reg(0)), None);
    assert_eq!(a.color(Reg(999)), None);
}

#[test]
fn copy_aware_baseline_equalities_and_faulting_memory_remain_safe() {
    let program = Program::new(
        0,
        5,
        vec![
            ins(
                0,
                vec![
                    set(1, Expr::load(r(0), Width::U16)),
                    set(2, r(1)),
                    store(c(2), Width::U8, r(1)),
                ],
                Control::Next,
            ),
            ins(
                1,
                vec![
                    set(3, b(BinaryOp::Add, r(2), c(1))),
                    store(r(0), Width::U32, Expr::load(c(1), Width::U32)),
                    set(4, r(3)),
                ],
                Control::Return(r(4)),
            ),
        ],
    )
    .unwrap();
    let eligible = [Reg(1), Reg(2), Reg(3), Reg(4)];
    let ordinary = allocate_locals(&program, &eligible).unwrap();
    let hinted =
        allocate_locals_with_hints(&program, &eligible, &[(Reg(1), Reg(4)), (Reg(2), Reg(3))])
            .unwrap();
    assert!(hinted.colors() <= ordinary.colors());
    assert_eq!(hinted.color(Reg(1)), hinted.color(Reg(2)));
    for pointer in [0, 1, 4, 5, u64::MAX] {
        for memory in [&[][..], &[0x5a; 3][..], &[0x81; 8][..]] {
            replay(
                &program,
                &hinted,
                &[pointer, 91, 92, 93, 94],
                memory,
                &[0, 1, 2, 3],
            );
        }
    }
}

#[test]
fn bounded_copy_rich_loop_corpus_matches_poison_bank_for_faults_and_cutoffs() {
    let eligible = [Reg(10), Reg(20), Reg(30), Reg(40), Reg(50), Reg(60)];
    for seed in 0..24u64 {
        let program = Program::new(
            0,
            61,
            vec![
                ins(
                    0,
                    vec![
                        set(10, r(0)),
                        set(20, c(seed + 1)),
                        set(30, c(3)),
                        set(40, c(4)),
                        set(50, c(5)),
                        set(60, c(6)),
                    ],
                    Control::Jump(1),
                ),
                ins(
                    1,
                    vec![
                        set(40, r(10)),
                        set(10, r(20)),
                        set(20, r(40)),
                        set(30, b(BinaryOp::Add, r(10), c(seed + 1))),
                        set(50, r(30)),
                        store(c(seed % 5), Width::U16, b(BinaryOp::Xor, r(20), r(50))),
                        set(
                            60,
                            Expr::select(r(1), r(50), Expr::load(c(seed % 7), Width::U32)),
                        ),
                        set(1, b(BinaryOp::Sub, r(1), c(1))),
                    ],
                    Control::Branch {
                        condition: r(1),
                        target: 1,
                    },
                ),
                ins(2, vec![], Control::Return(b(BinaryOp::Add, r(20), r(60)))),
            ],
        )
        .unwrap();
        let ordinary = allocate_locals(&program, &eligible).unwrap();
        let hints = [
            (Reg(10), Reg(40)),
            (Reg(20), Reg(50)),
            (Reg(30), Reg(60)),
            (Reg(10), Reg(20)),
        ];
        let hinted = allocate_locals_with_hints(&program, &eligible, &hints).unwrap();
        assert!(hinted.colors() <= ordinary.colors());
        for value in [0, 1, u64::MAX] {
            for count in [0, 1, 3] {
                let mut input = vec![0xfeed; 61];
                input[0] = value;
                input[1] = count;
                for memory in [&[][..], &[0x95; 8][..]] {
                    replay(&program, &hinted, &input, memory, &[0, 1, 2, 3, 5, 8]);
                }
            }
        }
    }
}

#[test]
fn exhausted_optional_work_keeps_the_complete_ordinary_allocation() {
    // A legal dense prefix needs 447 colors; the remaining independent
    // lifetimes keep that palette large. This stays below the graph edge
    // limit while exhausting the separately bounded hinted coloring pass.
    fn tree(values: &[Expr]) -> Expr {
        if values.len() == 1 {
            return values[0].clone();
        }
        let middle = values.len() / 2;
        b(
            BinaryOp::Xor,
            tree(&values[..middle]),
            tree(&values[middle..]),
        )
    }
    let mut assignments: Vec<_> = (1..=447).map(|id| set(id, c(id as u64))).collect();
    let terms: Vec<_> = (1..=447).map(r).collect();
    assignments.push(store(c(0), Width::U8, tree(&terms)));
    for id in 448..=4096 {
        assignments.push(set(id, c(id as u64)));
        assignments.push(store(c(0), Width::U8, r(id)));
    }
    let program =
        Program::new(0, 4097, vec![ins(0, assignments, Control::Return(r(4096)))]).unwrap();
    let eligible: Vec<_> = (1..=4096).map(Reg).collect();
    let ordinary = allocate_locals(&program, &eligible).unwrap();
    let hinted = allocate_locals_with_hints(&program, &eligible, &[(Reg(447), Reg(4096))]).unwrap();
    equivalent_allocation(&ordinary, &hinted, &eligible);
    let repeated =
        allocate_locals_with_hints(&program, &eligible, &[(Reg(447), Reg(4096))]).unwrap();
    equivalent_allocation(&hinted, &repeated, &eligible);
}

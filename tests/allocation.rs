use nirvana::allocation::{LocalAllocation, allocate_locals};
use nirvana::ir::{Assignment, BinaryOp, Control, Expr, IrInstruction, Place, Program, Reg, Width};

fn r(index: usize) -> Expr {
    Expr::Register(Reg(index))
}
fn c(value: u64) -> Expr {
    Expr::Const(value)
}
fn b(op: BinaryOp, left: Expr, right: Expr) -> Expr {
    Expr::binary(op, left, right)
}
fn set(register: usize, value: Expr) -> Assignment {
    Assignment {
        destination: Reg(register).into(),
        value,
    }
}
fn store(address: Expr, width: Width, value: Expr) -> Assignment {
    Assignment {
        destination: Place::Memory { address, width },
        value,
    }
}
fn load(address: Expr, width: Width) -> Expr {
    Expr::load(address, width)
}
fn i(address: u64, assignments: Vec<Assignment>, control: Control) -> IrInstruction {
    IrInstruction {
        address,
        size: 1,
        assignments,
        control,
    }
}
fn program(registers: usize, instructions: Vec<IrInstruction>) -> Program {
    Program::new(0, registers, instructions).unwrap()
}
fn locals(first: usize, end: usize) -> Vec<Reg> {
    (first..end).map(Reg).collect()
}

// Independent relabeling into a fresh register bank. Noneligible registers keep
// their indices and input values; the bank starts with unrelated poison values.
fn relabeled(p: &Program, allocation: &LocalAllocation) -> Program {
    fn expression(expr: &Expr, map: &impl Fn(Reg) -> Reg) -> Expr {
        match expr {
            Expr::Const(_) => expr.clone(),
            Expr::Register(reg) => Expr::Register(map(*reg)),
            Expr::Binary(op, left, right) => b(*op, expression(left, map), expression(right, map)),
            Expr::Load { address, width } => load(expression(address, map), *width),
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
    let bank = p.register_count();
    let map = |reg: Reg| {
        allocation
            .color(reg)
            .map(|color| Reg(bank + color))
            .unwrap_or(reg)
    };
    let instructions = p
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
                control => control.clone(),
            };
            IrInstruction {
                assignments,
                control,
                ..instruction.clone()
            }
        })
        .collect();
    Program::new(
        p.cfg().block(p.cfg().entry()).start,
        bank + allocation.colors(),
        instructions,
    )
    .unwrap()
}

fn replay(
    p: &Program,
    allocation: &LocalAllocation,
    input: &[u64],
    memory: &[u8],
    limits: &[usize],
) {
    let mapped = relabeled(p, allocation);
    let mut mapped_input = input.to_vec();
    mapped_input.resize(mapped.register_count(), 0xdead_beef_1234_5678);
    for &limit in limits {
        let expected = p.run_with_memory(input, 0, memory, limit).unwrap();
        let actual = mapped
            .run_with_memory(&mapped_input, 0, memory, limit)
            .unwrap();
        assert_eq!(
            actual.status, expected.status,
            "limit={limit}, input={input:?}"
        );
        assert_eq!(
            actual.state.memory, expected.state.memory,
            "limit={limit}, input={input:?}"
        );
        assert_eq!(
            actual.state.trace, expected.state.trace,
            "limit={limit}, input={input:?}"
        );
        assert_eq!(actual.state.instruction, expected.state.instruction);
        assert_eq!(actual.state.memory_base, expected.state.memory_base);
    }
}

#[test]
fn chains_reuse_one_color_and_order_is_independent_of_argument_order() {
    let p = program(
        4,
        vec![i(
            0,
            vec![
                set(1, b(BinaryOp::Add, r(0), c(1))),
                set(2, b(BinaryOp::Mul, r(1), c(3))),
                set(3, b(BinaryOp::Xor, r(2), c(7))),
            ],
            Control::Return(r(3)),
        )],
    );
    let a = allocate_locals(&p, &locals(1, 4)).unwrap();
    assert_eq!(a.colors(), 1);
    assert_eq!(a.color(Reg(0)), None);
    assert_eq!(a.color(Reg(999)), None);
    let reversed = allocate_locals(&p, &[Reg(3), Reg(2), Reg(1)]).unwrap();
    for register in 1..4 {
        assert_eq!(a.color(Reg(register)), Some(0));
        assert_eq!(a.color(Reg(register)), reversed.color(Reg(register)));
    }
    for input in [0, 1, 255, 1 << 63, u64::MAX] {
        replay(&p, &a, &[input, 91, 92, 93], &[], &[0, 1, 2]);
    }
}

#[test]
fn equal_copies_share_storage_while_both_are_live_in_separate_uses() {
    let p = program(
        3,
        vec![i(
            0,
            vec![
                set(1, b(BinaryOp::Add, r(0), c(1))),
                set(2, r(1)),
                store(c(0), Width::U64, r(1)),
            ],
            Control::Return(r(2)),
        )],
    );
    let a = allocate_locals(&p, &locals(1, 3)).unwrap();
    assert_eq!(
        a.colors(),
        1,
        "copy values need not remain in distinct slots"
    );
    assert_eq!(a.color(Reg(1)), a.color(Reg(2)));
    for input in [0, 1, 255, 1 << 63, u64::MAX] {
        for memory in [&[][..], &[0x55; 8][..]] {
            replay(&p, &a, &[input, 91, 92], memory, &[0, 1, 2]);
        }
    }
}

#[test]
fn simultaneous_operands_form_interference_cycles_and_dead_writes_can_clobber() {
    let p = program(
        3,
        vec![i(
            0,
            vec![set(0, c(7)), set(1, c(11)), set(2, c(17))],
            Control::Return(b(BinaryOp::Add, r(0), b(BinaryOp::Mul, r(1), r(2)))),
        )],
    );
    let a = allocate_locals(&p, &locals(0, 3)).unwrap();
    assert_eq!(a.colors(), 3);
    assert_ne!(a.color(Reg(0)), a.color(Reg(1)));
    assert_ne!(a.color(Reg(1)), a.color(Reg(2)));
    assert_ne!(a.color(Reg(0)), a.color(Reg(2)));
    replay(&p, &a, &[99; 3], &[], &[0, 1]);

    let p = program(
        2,
        vec![i(
            0,
            vec![set(0, c(7)), set(1, c(99))],
            Control::Return(r(0)),
        )],
    );
    let a = allocate_locals(&p, &locals(0, 2)).unwrap();
    assert_ne!(a.color(Reg(0)), a.color(Reg(1)));
    replay(&p, &a, &[1, 2], &[], &[1]);
}

#[test]
fn entry_inputs_invalid_indices_and_duplicate_eligibility_are_rejected() {
    let p = program(2, vec![i(0, vec![set(1, r(0))], Control::Return(r(1)))]);
    assert!(allocate_locals(&p, &[Reg(0)]).is_none());
    assert!(allocate_locals(&p, &[Reg(1), Reg(1)]).is_none());
    assert!(allocate_locals(&p, &[Reg(2)]).is_none());
    let empty = allocate_locals(&p, &[]).unwrap();
    assert_eq!(empty.colors(), 0);
    assert_eq!(empty.color(Reg(0)), None);
    assert!(allocate_locals(&p, &[Reg(1)]).is_some());

    let p = program(
        2,
        vec![
            i(
                0,
                vec![set(1, r(0)), set(0, c(0))],
                Control::Branch {
                    condition: r(1),
                    target: 0,
                },
            ),
            i(1, vec![], Control::Return(c(0))),
        ],
    );
    assert!(allocate_locals(&p, &locals(0, 2)).is_none());
}

#[test]
fn loop_carried_swaps_and_sequential_edge_copies_survive_relabeling() {
    let p = program(
        7,
        vec![
            i(
                0,
                vec![set(3, r(0)), set(4, r(1)), set(5, r(2))],
                Control::Jump(1),
            ),
            i(
                1,
                vec![
                    set(6, r(3)),
                    set(3, r(4)),
                    set(4, r(6)),
                    set(5, b(BinaryOp::Sub, r(5), c(1))),
                ],
                Control::Branch {
                    condition: r(5),
                    target: 1,
                },
            ),
            i(2, vec![], Control::Return(b(BinaryOp::Sub, r(3), r(4)))),
        ],
    );
    let a = allocate_locals(&p, &locals(3, 7)).unwrap();
    assert_ne!(a.color(Reg(3)), a.color(Reg(6)));
    assert_ne!(a.color(Reg(4)), a.color(Reg(6)));
    for count in [1, 2, 3, 4, 9] {
        for (left, right) in [(7, 11), (u64::MAX, 1), (0, 1 << 63)] {
            replay(
                &p,
                &a,
                &[left, right, count, 91, 92, 93, 94],
                &[],
                &[0, 1, 2, 3, 5, 15],
            );
        }
    }
}

#[test]
fn diamond_copies_and_multiple_definitions_preserve_join_operands() {
    let p = program(
        6,
        vec![
            i(
                0,
                vec![set(2, r(1))],
                Control::Branch {
                    condition: r(0),
                    target: 2,
                },
            ),
            i(
                1,
                vec![set(3, b(BinaryOp::Add, r(2), c(3))), set(4, r(3))],
                Control::Jump(3),
            ),
            i(
                2,
                vec![set(4, b(BinaryOp::Mul, r(2), c(7))), set(3, r(4))],
                Control::Jump(3),
            ),
            i(
                3,
                vec![set(5, b(BinaryOp::Add, r(3), r(4)))],
                Control::Return(b(BinaryOp::Xor, r(5), r(2))),
            ),
        ],
    );
    let a = allocate_locals(&p, &locals(2, 6)).unwrap();
    assert_ne!(a.color(Reg(3)), a.color(Reg(4)));
    for condition in [0, 1] {
        for value in [0, 7, 255, u64::MAX] {
            replay(
                &p,
                &a,
                &[condition, value, 91, 92, 93, 94],
                &[],
                &[0, 1, 2, 3, 4],
            );
        }
    }
}

#[test]
fn stores_keep_address_and_rhs_values_distinct_even_with_aliases_and_faults() {
    let p = program(
        6,
        vec![
            i(
                0,
                vec![
                    set(2, r(0)),
                    set(3, load(r(0), Width::U64)),
                    store(r(2), Width::U8, r(3)),
                    set(4, load(r(1), Width::U16)),
                    store(r(1), Width::U64, b(BinaryOp::Add, r(3), r(4))),
                ],
                Control::Next,
            ),
            i(
                1,
                vec![
                    set(
                        5,
                        Expr::select(load(r(0), Width::U8), load(r(1), Width::U32), r(4)),
                    ),
                    store(r(0), Width::U16, b(BinaryOp::Xor, r(4), r(5))),
                ],
                Control::Return(b(BinaryOp::Xor, r(3), r(5))),
            ),
        ],
    );
    let a = allocate_locals(&p, &locals(2, 6)).unwrap();
    assert_ne!(a.color(Reg(2)), a.color(Reg(3)));
    let memory: Vec<_> = (0..16).map(|byte| byte * 17).collect();
    for left in [0, 1, 8, 15, 16, u64::MAX] {
        for right in [0, 1, 8, 15, 16, u64::MAX] {
            replay(
                &p,
                &a,
                &[left, right, 91, 92, 93, 94],
                &memory,
                &[0, 1, 2, 3],
            );
        }
    }
}

#[test]
fn unreachable_uses_do_not_reject_allocations_or_create_interference() {
    let p = program(
        3,
        vec![
            i(0, vec![set(0, c(7)), set(1, r(0))], Control::Return(r(1))),
            i(
                1,
                vec![set(1, r(2))],
                Control::Return(b(BinaryOp::Add, r(0), r(2))),
            ),
        ],
    );
    let a = allocate_locals(&p, &locals(0, 3)).unwrap();
    assert_eq!(a.colors(), 1);
    replay(&p, &a, &[11, 22, 33], &[], &[0, 1, 2]);
}

#[test]
fn conservative_resource_limits_return_no_partial_allocation() {
    let p = program(4097, vec![i(0, vec![], Control::Return(c(0)))]);
    assert!(allocate_locals(&p, &locals(0, 4097)).is_none());
    let mut deep = c(1);
    for _ in 0..260 {
        deep = b(BinaryOp::Add, deep, c(0));
    }
    let p = program(1, vec![i(0, vec![set(0, c(7))], Control::Return(deep))]);
    assert!(allocate_locals(&p, &[Reg(0)]).is_none());

    // 450 simultaneously used values exceed the 100,000-edge bound.
    // Keep expression depth small by grouping into a balanced tree.
    fn sum(registers: std::ops::Range<usize>) -> Expr {
        if registers.len() == 1 {
            return r(registers.start);
        }
        let middle = registers.start + registers.len() / 2;
        b(
            BinaryOp::Add,
            sum(registers.start..middle),
            sum(middle..registers.end),
        )
    }
    let expression = sum(0..450);
    let p = program(
        450,
        vec![i(
            0,
            (0..450).map(|reg| set(reg, c(reg as u64))).collect(),
            Control::Return(expression),
        )],
    );
    assert!(allocate_locals(&p, &locals(0, 450)).is_none());
}

#[test]
fn generated_cfg_relabeling_preserves_every_bounded_observation() {
    let mut seed = 0x7283_9abc_def0_1234u64;
    let mut random = || {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        seed
    };
    let operations = [
        BinaryOp::Add,
        BinaryOp::Sub,
        BinaryOp::Mul,
        BinaryOp::And,
        BinaryOp::Or,
        BinaryOp::Xor,
        BinaryOp::Shl,
        BinaryOp::Shr,
        BinaryOp::UMulHigh,
        BinaryOp::Eq,
        BinaryOp::Ult,
    ];
    let widths = [Width::U8, Width::U16, Width::U32, Width::U64];
    let mut compared = 0;
    for _ in 0..40 {
        let mut instructions = vec![i(
            0,
            (2..10).map(|reg| set(reg, c(random()))).collect(),
            Control::Jump(1),
        )];
        for address in 1..=2 {
            let mut assignments = Vec::new();
            for _ in 0..6 {
                let destination = 2 + random() as usize % 8;
                let left = r(2 + random() as usize % 8);
                let right = if random() & 1 == 0 {
                    r(2 + random() as usize % 8)
                } else {
                    c(random())
                };
                let value = b(
                    operations[random() as usize % operations.len()],
                    left,
                    right,
                );
                let address = b(
                    BinaryOp::Add,
                    r(random() as usize & 1),
                    b(BinaryOp::And, r(2 + random() as usize % 8), c(15)),
                );
                match random() % 5 {
                    0 => assignments.push(store(address, widths[random() as usize % 4], value)),
                    1 => assignments.push(set(
                        destination,
                        load(address, widths[random() as usize % 4]),
                    )),
                    2 => assignments.push(set(
                        destination,
                        Expr::select(
                            r(2 + random() as usize % 8),
                            value,
                            load(address, Width::U8),
                        ),
                    )),
                    _ => assignments.push(set(destination, value)),
                }
            }
            instructions.push(i(
                address,
                assignments,
                Control::Branch {
                    condition: r(2 + random() as usize % 8),
                    target: if random() & 1 == 0 { 1 } else { 3 },
                },
            ));
        }
        instructions.push(i(3, vec![], Control::Return(b(BinaryOp::Xor, r(2), r(3)))));
        let p = program(10, instructions);
        let a = allocate_locals(&p, &locals(2, 10)).unwrap();
        assert!((1..=8).contains(&a.colors()));
        let memory: Vec<u8> = (0..32).map(|index| (index * 17) as u8).collect();
        for (left, right) in [(0, 0), (0, 8), (8, 0), (15, 15), (32, 0), (u64::MAX, 0)] {
            replay(
                &p,
                &a,
                &[left, right, 91, 92, 93, 94, 95, 96, 97, 98],
                &memory,
                &[0, 1, 2, 3, 4, 8, 16],
            );
            compared += 7;
        }
    }
    assert_eq!(compared, 1_680);
}

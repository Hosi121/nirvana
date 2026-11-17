use nirvana::ir::{Assignment, BinaryOp, Control, Expr, IrInstruction, Place, Program, Reg, Width};
use nirvana::observe::{Comparison, Contract};
use nirvana::reduce::reduce;

#[path = "../examples/programs/mod.rs"]
mod programs;

fn r(index: usize) -> Expr {
    Expr::Register(Reg(index))
}
fn c(value: u64) -> Expr {
    Expr::Const(value)
}
fn set(index: usize, value: Expr) -> Assignment {
    Assignment {
        destination: Reg(index).into(),
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
fn compare(program: &Program, input: &[u64], memory: &[u8], limit: usize) {
    let reduced = reduce(program).unwrap();
    let expected = program.run_with_memory(input, 0, memory, limit).unwrap();
    let actual = reduced.run_with_memory(input, 0, memory, limit).unwrap();
    // This reduction preserves original step boundaries as an additional
    // regression invariant, including partial state on faults and cutoffs.
    assert_eq!(
        (&actual.status, &actual.state.memory, &actual.state.trace),
        (
            &expected.status,
            &expected.state.memory,
            &expected.state.trace
        ),
        "input={input:?}, limit={limit}, original={:?}, reduced={:?}",
        program.instructions(),
        reduced.program().instructions()
    );
    let comparison = Contract::return_memory()
        .with_instruction_trace()
        .compare(&expected, &actual);
    if expected.status == nirvana::ir::RunStatus::Suspended {
        assert!(matches!(comparison, Comparison::Inconclusive { .. }));
    } else {
        assert_eq!(comparison, Comparison::MatchForInput);
    }
}

#[test]
fn named_control_shapes_keep_return_memory_and_instruction_trace() {
    for name in programs::NAMES {
        let program = programs::named(name).unwrap();
        for input in [0, 1, 7, 12, 63, 1 << 63, u64::MAX] {
            let mut registers = vec![0; program.register_count()];
            registers[0] = input;
            for limit in [0, 1, 5, 2_000] {
                compare(&program, &registers, &[], limit);
            }
        }
    }
}

#[test]
fn block_exit_copies_keep_snapshots_during_swaps_and_loops() {
    use BinaryOp::*;
    let program = program(
        4,
        vec![
            (vec![], Control::Jump(1)),
            (
                vec![
                    set(3, r(0)),
                    set(0, r(1)),
                    set(1, r(3)),
                    set(2, Expr::binary(Sub, r(2), c(1))),
                ],
                Control::Branch {
                    condition: r(2),
                    target: 1,
                },
            ),
            (vec![], Control::Return(Expr::binary(Sub, r(0), r(1)))),
        ],
    );
    for iterations in 1..8 {
        compare(&program, &[11, 29, iterations, 0], &[], 100);
    }
}

#[test]
fn unused_loads_aliasing_stores_and_lazy_loads_keep_faults() {
    let memory = (0..16).collect::<Vec<u8>>();
    let program = program(
        4,
        vec![(
            vec![
                set(2, Expr::load(r(0), Width::U64)),
                Assignment {
                    destination: Place::Memory {
                        address: r(0),
                        width: Width::U8,
                    },
                    value: c(200),
                },
                set(3, Expr::load(r(0), Width::U8)),
                set(2, Expr::select(r(1), Expr::load(c(99), Width::U64), c(0))),
            ],
            Control::Return(r(3)),
        )],
    );
    for address in [0, 8, 9, u64::MAX] {
        for condition in [0, 1] {
            compare(&program, &[address, condition, 0, 0], &memory, 10);
        }
    }
    let reduced = reduce(&program).unwrap();
    assert_eq!(reduced.parameters(), &[Reg(0), Reg(1)]);
}

#[test]
fn pure_dead_definitions_do_not_make_arguments_live() {
    let program = program(
        4,
        vec![(
            vec![
                set(2, Expr::binary(BinaryOp::Mul, r(0), r(1))),
                set(3, c(9)),
            ],
            Control::Return(r(3)),
        )],
    );
    let reduced = reduce(&program).unwrap();
    assert!(reduced.parameters().is_empty());
    assert_eq!(reduced.stats().reduced_assignments, 0);
    compare(&program, &[u64::MAX, 2, 3, 4], &[], 1);
    assert!(reduced.execute_with_memory(&[], 0, &[], 1).is_err());
}

#[test]
fn shared_differences_keep_old_operands_across_overwrites_edges_and_faults() {
    use BinaryOp::*;
    let program = program(
        5,
        vec![
            (
                vec![
                    set(3, Expr::binary(Sub, r(0), r(1))),
                    set(4, Expr::binary(Shr, r(3), c(63))),
                    Assignment {
                        destination: Place::Memory {
                            address: r(2),
                            width: Width::U8,
                        },
                        value: r(4),
                    },
                    set(0, Expr::binary(Add, r(0), c(1))),
                ],
                Control::Branch {
                    condition: r(4),
                    target: 2,
                },
            ),
            (
                vec![set(1, Expr::binary(Sub, r(1), c(1)))],
                Control::Return(Expr::binary(Add, Expr::binary(Xor, r(3), r(0)), r(1))),
            ),
            (
                vec![Assignment {
                    destination: Place::Memory {
                        address: Expr::binary(Add, r(2), c(1)),
                        width: Width::U64,
                    },
                    value: r(3),
                }],
                Control::Return(Expr::binary(Add, Expr::binary(Xor, r(3), r(0)), r(1))),
            ),
        ],
    );
    let memory: Vec<_> = (1..=16).collect();
    for left in [0, 1, (1 << 63) - 1, 1 << 63, u64::MAX] {
        for right in [0, 1, (1 << 63) - 1, 1 << 63, u64::MAX] {
            for address in [0, 7, 8, 15, u64::MAX] {
                for limit in [0, 1, 2, 3, 10] {
                    compare(
                        &program,
                        &[left, right, address, !left, !right],
                        &memory,
                        limit,
                    );
                }
            }
        }
    }
}

#[test]
fn seeded_arbitrary_cfgs_preserve_observations_including_step_limits() {
    let mut state = 0x1a29_789a_bced_5791u64;
    let mut random = || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    let ops = [
        BinaryOp::Add,
        BinaryOp::Sub,
        BinaryOp::Mul,
        BinaryOp::Xor,
        BinaryOp::And,
        BinaryOp::Or,
        BinaryOp::Shr,
        BinaryOp::Shl,
        BinaryOp::Ult,
        BinaryOp::Ule,
        BinaryOp::Eq,
        BinaryOp::UMulHigh,
    ];
    for _ in 0..256 {
        let mut rows = Vec::new();
        for i in 0..8 {
            let mut assignments = Vec::new();
            for _ in 0..3 {
                let dst = (random() % 4) as usize;
                let left = r((random() % 4) as usize);
                let right = if random() & 1 == 0 {
                    c(random())
                } else {
                    r((random() % 4) as usize)
                };
                assignments.push(set(
                    dst,
                    Expr::binary(ops[(random() % ops.len() as u64) as usize], left, right),
                ));
            }
            let control = if i == 7 {
                Control::Return(r((random() % 4) as usize))
            } else {
                match random() % 3 {
                    0 => Control::Next,
                    1 => Control::Jump(random() % 8),
                    _ => Control::Branch {
                        condition: r((random() % 4) as usize),
                        target: random() % 8,
                    },
                }
            };
            rows.push((assignments, control));
        }
        let program = program(4, rows);
        for input in [
            [0; 4],
            [u64::MAX, 1, 63, 64],
            [random(), random(), random(), random()],
        ] {
            for limit in [0, 1, 7, 50] {
                compare(&program, &input, &[], limit);
            }
        }
    }
}

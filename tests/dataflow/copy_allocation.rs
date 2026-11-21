//! Independent executable checks for storage coalescing. Eligible locals move
//! into a fresh, poisoned bank; we never copy their initial or final values.
//! The complete final register file is not an observation of this transform.

use nirvana::allocation::allocate_locals;
use nirvana::ir::{
    Assignment, BinaryOp, Control, Expr, IrInstruction, Place, Program, Reg, RunReport, RunStatus,
    Width,
};
use std::collections::BTreeSet;

use crate::support::ir::c;
use crate::support::ir::r;
fn b(op: BinaryOp, x: Expr, y: Expr) -> Expr {
    Expr::binary(op, x, y)
}
fn set(n: usize, value: Expr) -> Assignment {
    Assignment {
        destination: Reg(n).into(),
        value,
    }
}
fn store(address: Expr, width: Width, value: Expr) -> Assignment {
    Assignment {
        destination: Place::Memory { address, width },
        value,
    }
}
fn step(address: u64, assignments: Vec<Assignment>, control: Control) -> IrInstruction {
    IrInstruction {
        address,
        size: 1,
        assignments,
        control,
    }
}
fn program(count: usize, steps: Vec<IrInstruction>) -> Program {
    Program::new(0, count, steps).unwrap()
}
fn locals(first: usize, end: usize) -> Vec<Reg> {
    (first..end).map(Reg).collect()
}

fn poison(index: usize) -> u64 {
    0x93a5_7c21_f0de_864b_u64
        .wrapping_mul((index as u64).wrapping_add(1))
        .rotate_left(19)
}
fn inputs(count: usize, prefix: &[u64]) -> Vec<u64> {
    let mut result: Vec<_> = (0..count).map(poison).collect();
    result[..prefix.len()].copy_from_slice(prefix);
    result
}

fn rewrite(expression: &Expr, register: &impl Fn(Reg) -> Reg) -> Expr {
    match expression {
        Expr::Const(_) => expression.clone(),
        Expr::Register(reg) => Expr::Register(register(*reg)),
        Expr::Binary(op, x, y) => b(*op, rewrite(x, register), rewrite(y, register)),
        Expr::Load { address, width } => Expr::load(rewrite(address, register), *width),
        Expr::Select {
            condition,
            taken,
            not_taken,
        } => Expr::select(
            rewrite(condition, register),
            rewrite(taken, register),
            rewrite(not_taken, register),
        ),
    }
}

// This adapter knows only the public color API. It retains every assignment,
// control edge, instruction address, and memory width, including unreachable
// instructions. It can also replay intentionally invalid coloring controls.
fn fresh_bank(p: &Program, colors: usize, color: impl Fn(Reg) -> Option<usize>) -> Program {
    let bank = p.register_count() + 4;
    let register = |reg| match color(reg) {
        Some(color) => {
            assert!(color < colors);
            Reg(bank + color)
        }
        None => reg,
    };
    let steps = p
        .instructions()
        .iter()
        .map(|instruction| {
            let assignments = instruction
                .assignments
                .iter()
                .map(|assignment| Assignment {
                    destination: match &assignment.destination {
                        Place::Register(reg) => Place::Register(register(*reg)),
                        Place::Memory { address, width } => Place::Memory {
                            address: rewrite(address, &register),
                            width: *width,
                        },
                    },
                    value: rewrite(&assignment.value, &register),
                })
                .collect();
            let control = match &instruction.control {
                Control::Branch { condition, target } => Control::Branch {
                    condition: rewrite(condition, &register),
                    target: *target,
                },
                Control::Return(value) => Control::Return(rewrite(value, &register)),
                other => other.clone(),
            };
            IrInstruction {
                assignments,
                control,
                ..instruction.clone()
            }
        })
        .collect();
    Program::new(p.cfg().block(p.cfg().entry()).start, bank + colors, steps).unwrap()
}

#[derive(Debug, Eq, PartialEq)]
struct Observation {
    status: RunStatus,
    memory_base: u64,
    memory: Vec<u8>,
    trace: Vec<u64>,
    instruction: Option<u64>,
    // Noneligible registers have their original storage and remain observable.
    preserved_registers: Vec<(usize, u64)>,
}
fn observe(report: RunReport, eligible: &[Reg], count: usize) -> Observation {
    let preserved_registers = report
        .state
        .registers
        .iter()
        .copied()
        .take(count)
        .enumerate()
        .filter(|(index, _)| !eligible.contains(&Reg(*index)))
        .collect();
    Observation {
        status: report.status,
        memory_base: report.state.memory_base,
        memory: report.state.memory,
        trace: report.state.trace,
        instruction: report.state.instruction,
        preserved_registers,
    }
}

fn replay(
    p: &Program,
    eligible: &[Reg],
    input: &[u64],
    base: u64,
    memory: &[u8],
    limits: &[usize],
) {
    let allocation = allocate_locals(p, eligible).expect("all eligible locals defined before use");
    for register in 0..p.register_count() {
        assert_eq!(
            allocation.color(Reg(register)).is_some(),
            eligible.contains(&Reg(register))
        );
    }
    let mapped = fresh_bank(p, allocation.colors(), |reg| allocation.color(reg));
    let mut mapped_input = input.to_vec();
    mapped_input.extend((input.len()..mapped.register_count()).map(|n| !poison(n)));
    for &limit in limits {
        let expected = observe(
            p.run_with_memory(input, base, memory, limit).unwrap(),
            eligible,
            p.register_count(),
        );
        let actual = observe(
            mapped
                .run_with_memory(&mapped_input, base, memory, limit)
                .unwrap(),
            eligible,
            p.register_count(),
        );
        assert_eq!(
            actual, expected,
            "limit={limit}, input={input:?}, eligible={eligible:?}"
        );
    }
}

#[test]
fn later_overwrites_of_copy_source_and_destination_preserve_the_other_value() {
    for overwrite_source in [false, true] {
        let assignments = if overwrite_source {
            vec![set(2, r(0)), set(3, r(2)), set(2, r(1)), set(4, r(3))]
        } else {
            vec![set(2, r(0)), set(3, r(2)), set(3, r(1)), set(4, r(2))]
        };
        let result = if overwrite_source {
            b(BinaryOp::Sub, r(2), r(4))
        } else {
            b(BinaryOp::Sub, r(4), r(3))
        };
        let p = program(5, vec![step(0, assignments, Control::Return(result))]);
        for x in [0, 7, 1 << 63, u64::MAX] {
            for y in [0, 11, u64::MAX] {
                replay(
                    &p,
                    &locals(2, 5),
                    &inputs(5, &[x, y]),
                    4096,
                    &[],
                    &[0, 1, 2],
                );
            }
        }
    }
}

#[test]
fn copy_rich_join_keeps_path_specific_sources_and_later_definitions_distinct() {
    let p = program(
        10,
        vec![
            step(
                0,
                vec![set(3, r(1)), set(4, r(2)), set(5, r(3))],
                Control::Branch {
                    condition: r(0),
                    target: 2,
                },
            ),
            step(
                1,
                vec![set(6, r(5)), set(3, r(4)), set(7, r(3)), set(4, r(6))],
                Control::Jump(3),
            ),
            step(
                2,
                vec![set(7, r(4)), set(6, r(3)), set(4, r(6)), set(3, r(7))],
                Control::Jump(3),
            ),
            step(
                3,
                vec![
                    set(8, r(6)),
                    set(9, r(7)),
                    set(6, b(BinaryOp::Add, r(6), c(1))),
                    set(7, r(8)),
                ],
                Control::Return(b(
                    BinaryOp::Xor,
                    b(BinaryOp::Sub, r(6), r(7)),
                    b(BinaryOp::Add, r(8), r(9)),
                )),
            ),
        ],
    );
    for condition in [0, 1, u64::MAX] {
        for (left, right) in [(7, 11), (7, 7), (u64::MAX, 1), (0, 1 << 63)] {
            replay(
                &p,
                &locals(3, 10),
                &inputs(10, &[condition, left, right]),
                0,
                &[],
                &[0, 1, 2, 3, 4],
            );
        }
    }
}

#[test]
fn loop_carried_sequential_swap_chains_keep_faults_and_suspension() {
    let p = program(
        10,
        vec![
            step(
                0,
                vec![
                    set(4, r(0)),
                    set(5, r(1)),
                    set(6, b(BinaryOp::And, r(2), c(7))),
                ],
                Control::Jump(1),
            ),
            step(
                1,
                vec![
                    set(7, r(4)),
                    set(8, r(7)),
                    set(4, r(5)),
                    set(5, r(8)),
                    set(9, r(4)),
                    store(r(3), Width::U8, r(9)),
                    set(6, b(BinaryOp::Sub, r(6), c(1))),
                ],
                Control::Branch {
                    condition: r(6),
                    target: 1,
                },
            ),
            step(
                2,
                vec![set(8, r(5))],
                Control::Return(b(BinaryOp::Sub, r(4), r(8))),
            ),
        ],
    );
    for count in [0, 1, 2, 3, 7] {
        for address in [4096, 4099, 4100, u64::MAX] {
            replay(
                &p,
                &locals(4, 10),
                &inputs(10, &[u64::MAX, 11, count, address]),
                4096,
                &[0x17; 4],
                &[0, 1, 2, 3, 4, 8, 12],
            );
        }
    }
}

#[test]
fn copies_of_addresses_and_values_preserve_aliasing_and_first_fault_partial_memory() {
    let p = program(
        11,
        vec![
            step(
                0,
                vec![
                    set(4, r(0)),
                    set(5, r(4)),
                    set(6, Expr::load(r(5), Width::U64)),
                    set(7, r(6)),
                    store(r(1), Width::U8, r(7)),
                    set(4, r(1)),
                    set(8, Expr::load(r(4), Width::U16)),
                    set(9, r(5)),
                    set(10, Expr::select(r(2), Expr::load(r(9), Width::U32), r(8))),
                    store(
                        r(4),
                        Width::U64,
                        b(
                            BinaryOp::Xor,
                            r(7),
                            Expr::load(b(BinaryOp::Add, r(9), c(16)), Width::U8),
                        ),
                    ),
                    set(6, r(10)),
                ],
                Control::Next,
            ),
            step(
                1,
                vec![set(7, r(6)), store(r(9), Width::U16, r(7))],
                Control::Return(b(BinaryOp::Xor, r(8), r(7))),
            ),
        ],
    );
    let memory: Vec<_> = (0..32).map(|n| (n * 17 + 3) as u8).collect();
    for left in [4096, 4097, 4120, 4127, 4128, u64::MAX] {
        for right in [4096, 4097, 4120, 4126, 4127, u64::MAX] {
            for condition in [0, 1] {
                replay(
                    &p,
                    &locals(4, 11),
                    &inputs(11, &[left, right, condition, 0]),
                    4096,
                    &memory,
                    &[0, 1, 2],
                );
            }
        }
    }
}

#[test]
fn subset_eligibility_preserves_unmapped_values_and_ignores_unreachable_input_uses() {
    let p = program(
        10,
        vec![
            step(
                0,
                vec![set(2, r(0)), set(3, r(2))],
                Control::Branch {
                    condition: r(1),
                    target: 2,
                },
            ),
            step(
                1,
                vec![set(4, r(3)), set(5, b(BinaryOp::Add, r(4), c(1)))],
                Control::Jump(3),
            ),
            step(
                2,
                vec![set(5, r(3)), set(4, b(BinaryOp::Add, r(5), c(2)))],
                Control::Jump(3),
            ),
            step(
                3,
                vec![
                    set(6, r(4)),
                    set(7, r(5)),
                    set(2, c(99)),
                    set(8, b(BinaryOp::Xor, r(6), r(7))),
                ],
                Control::Return(b(BinaryOp::Add, r(8), r(3))),
            ),
            step(
                4,
                vec![set(2, r(9)), set(3, r(2))],
                Control::Return(b(BinaryOp::Add, r(3), r(9))),
            ),
        ],
    );
    for eligible in [vec![Reg(2), Reg(4), Reg(6), Reg(8), Reg(9)], locals(2, 10)] {
        for condition in [0, 1] {
            for value in [0, 7, u64::MAX] {
                replay(
                    &p,
                    &eligible,
                    &inputs(10, &[value, condition]),
                    0,
                    &[],
                    &[0, 1, 2, 3, 4],
                );
            }
        }
    }
}

#[test]
fn replay_rejects_the_deliberately_unsafe_all_locals_one_bank_control() {
    let p = program(
        5,
        vec![step(
            0,
            vec![set(2, r(0)), set(3, r(2)), set(2, r(1)), set(4, r(3))],
            Control::Return(b(BinaryOp::Sub, r(2), r(4))),
        )],
    );
    let eligible = locals(2, 5);
    let input = inputs(5, &[5, 11]);
    replay(&p, &eligible, &input, 0, &[], &[0, 1]);
    let mapped = fresh_bank(&p, 1, |reg| eligible.contains(&reg).then_some(0));
    let mut bad_input = input.clone();
    bad_input.extend((input.len()..mapped.register_count()).map(|n| !poison(n)));
    let expected = observe(p.run_with_memory(&input, 0, &[], 1).unwrap(), &eligible, 5);
    let actual = observe(
        mapped.run_with_memory(&bad_input, 0, &[], 1).unwrap(),
        &eligible,
        5,
    );
    assert_eq!(expected.status, RunStatus::Returned(6));
    assert_eq!(actual.status, RunStatus::Returned(0));
    assert_ne!(
        actual, expected,
        "negative control must expose source overwrite clobber"
    );
}

struct Random(u64);
impl Random {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
}

#[test]
fn deterministic_generated_copy_rich_diamonds_and_backedges_preserve_observations() {
    let mut random = Random(0x57ac_13e2_d98b_046f);
    let mut compared = 0;
    let widths = [Width::U8, Width::U16, Width::U32, Width::U64];
    let candidates = [4, 5, 7, 9, 10, 11];
    let eligible = locals(4, 12);
    let memory: Vec<_> = (0..32).map(|n| (n * 23 + 7) as u8).collect();
    for _ in 0..24 {
        let mut steps = vec![step(
            0,
            vec![
                set(4, r(3)),
                set(5, r(4)),
                set(6, b(BinaryOp::Add, b(BinaryOp::And, r(2), c(3)), c(1))),
                set(7, r(0)),
                set(8, r(1)),
                set(9, r(5)),
                set(10, c(random.next())),
                set(11, r(10)),
            ],
            Control::Branch {
                condition: r(0),
                target: 2,
            },
        )];
        for address in [1, 2] {
            let mut assignments = vec![set(10, r(4)), set(11, r(5)), set(4, r(10)), set(5, r(11))];
            for _ in 0..3 {
                let source = candidates[random.next() as usize % candidates.len()];
                let destination = candidates[random.next() as usize % candidates.len()];
                assignments.push(set(destination, r(source)));
            }
            let target = candidates[random.next() as usize % candidates.len()];
            let op = [BinaryOp::Add, BinaryOp::Sub, BinaryOp::Xor, BinaryOp::And]
                [random.next() as usize % 4];
            assignments.push(set(target, b(op, r(target), c(random.next()))));
            let address_expr = b(BinaryOp::Add, r(8), c(random.next() & 3));
            let width = widths[random.next() as usize % widths.len()];
            if address == 1 {
                assignments.push(store(address_expr, width, r(5)));
            } else {
                assignments.push(set(
                    11,
                    Expr::select(
                        b(BinaryOp::And, r(0), c(1)),
                        Expr::load(address_expr, width),
                        r(10),
                    ),
                ));
            }
            steps.push(step(address, assignments, Control::Jump(3)));
        }
        steps.push(step(
            3,
            vec![
                set(9, r(4)),
                set(10, r(9)),
                set(4, r(5)),
                set(5, r(10)),
                set(7, b(BinaryOp::Xor, r(7), r(5))),
                store(
                    b(BinaryOp::Add, r(8), c(random.next() & 3)),
                    Width::U8,
                    r(7),
                ),
                set(6, b(BinaryOp::Sub, r(6), c(1))),
            ],
            Control::Branch {
                condition: r(6),
                target: 1 + (random.next() & 1),
            },
        ));
        steps.push(step(
            4,
            vec![set(10, r(4)), set(11, r(5))],
            Control::Return(b(BinaryOp::Xor, b(BinaryOp::Add, r(10), r(11)), r(7))),
        ));
        steps.push(step(
            5,
            vec![set(9, Expr::load(c(u64::MAX), Width::U64))],
            Control::Return(r(9)),
        ));
        let p = program(12, steps);
        for prefix in [
            [0, 4096, 0, 0],
            [1, 4096, 3, u64::MAX],
            [1, 4097, 1, 7],
            [0, 4120, 2, 11],
            [1, 4127, 3, 1 << 63],
            [0, u64::MAX, 0, 19],
        ] {
            replay(
                &p,
                &eligible,
                &inputs(12, &prefix),
                4096,
                &memory,
                &[0, 1, 2, 3, 5, 8, 13],
            );
            compared += 7;
        }
    }
    assert_eq!(compared, 1008);
    // Sanity: eligibility lists themselves contain no duplicate register.
    assert_eq!(
        eligible.iter().map(|r| r.0).collect::<BTreeSet<_>>().len(),
        eligible.len()
    );
    println!(
        "24 deterministic copy-rich CFGs, 6 poisoned inputs, 7 budgets: {compared} exact replay observations"
    );
}

use nirvana::ir::{
    AccessKind, Assignment, BinaryOp, Control, Expr, IrInstruction, MemoryFault, Place, Program,
    Reg, RunReport, RunStatus, Width,
};
use nirvana::web::{WebStats, split};
use std::collections::BTreeSet;

fn r(n: usize) -> Expr {
    Expr::Register(Reg(n))
}
fn c(n: u64) -> Expr {
    Expr::Const(n)
}
fn b(op: BinaryOp, a: Expr, z: Expr) -> Expr {
    Expr::binary(op, a, z)
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
fn program(count: usize, instructions: Vec<IrInstruction>) -> Program {
    Program::new(0, count, instructions).unwrap()
}

fn expression_shape(a: &Expr, z: &Expr) {
    match (a, z) {
        (Expr::Register(_), Expr::Register(_)) => {}
        (Expr::Const(a), Expr::Const(z)) => assert_eq!(a, z),
        (Expr::Binary(a, al, ar), Expr::Binary(z, zl, zr)) => {
            assert_eq!(a, z);
            expression_shape(al, zl);
            expression_shape(ar, zr);
        }
        (
            Expr::Load {
                address: a,
                width: aw,
            },
            Expr::Load {
                address: z,
                width: zw,
            },
        ) => {
            assert_eq!(aw, zw);
            expression_shape(a, z);
        }
        (
            Expr::Select {
                condition: a,
                taken: at,
                not_taken: an,
            },
            Expr::Select {
                condition: z,
                taken: zt,
                not_taken: zn,
            },
        ) => {
            expression_shape(a, z);
            expression_shape(at, zt);
            expression_shape(an, zn);
        }
        _ => panic!("expression operation/structure changed: {a:?} -> {z:?}"),
    }
}

// Check all non-register syntax independently. Unreachable instructions must
// retain even their exact original register leaves and destinations.
fn shape(original: &Program, candidate: &Program) {
    assert!(candidate.register_count() >= original.register_count());
    assert_eq!(
        original.cfg().instructions(),
        candidate.cfg().instructions()
    );
    let reachable: BTreeSet<_> = original
        .cfg()
        .reachable_blocks()
        .iter()
        .flat_map(|id| original.cfg().block(*id).instructions.clone())
        .collect();
    for (index, (a, z)) in original
        .instructions()
        .iter()
        .zip(candidate.instructions())
        .enumerate()
    {
        if !reachable.contains(&index) {
            assert_eq!(a, z);
            continue;
        }
        assert_eq!(
            (a.address, a.size, a.assignments.len()),
            (z.address, z.size, z.assignments.len())
        );
        for (a, z) in a.assignments.iter().zip(&z.assignments) {
            match (&a.destination, &z.destination) {
                (Place::Register(_), Place::Register(_)) => {}
                (
                    Place::Memory {
                        address: a,
                        width: aw,
                    },
                    Place::Memory {
                        address: z,
                        width: zw,
                    },
                ) => {
                    assert_eq!(aw, zw);
                    expression_shape(a, z);
                }
                _ => panic!("destination kind changed"),
            }
            expression_shape(&a.value, &z.value);
        }
        match (&a.control, &z.control) {
            (Control::Return(a), Control::Return(z)) => expression_shape(a, z),
            (
                Control::Branch {
                    condition: a,
                    target: at,
                },
                Control::Branch {
                    condition: z,
                    target: zt,
                },
            ) => {
                assert_eq!(at, zt);
                expression_shape(a, z);
            }
            _ => assert_eq!(a.control, z.control),
        }
    }
}

#[derive(Debug, Eq, PartialEq)]
struct Observation {
    status: RunStatus,
    memory: Vec<u8>,
    base: u64,
    trace: Vec<u64>,
    instruction: Option<u64>,
}
fn observe(report: RunReport) -> Observation {
    Observation {
        status: report.status,
        memory: report.state.memory,
        base: report.state.memory_base,
        trace: report.state.trace,
        instruction: report.state.instruction,
    }
}
fn replay(original: &Program, candidate: &Program, input: &[u64], memory: &[u8], limits: &[usize]) {
    let mut poisoned = input.to_vec();
    poisoned.extend(
        (input.len()..candidate.register_count())
            .map(|n| 0x93a5_7c21_f0de_864bu64.wrapping_mul(n as u64 + 1)),
    );
    for &limit in limits {
        let expected = observe(
            original
                .run_with_memory(input, 4096, memory, limit)
                .unwrap(),
        );
        let actual = observe(
            candidate
                .run_with_memory(&poisoned, 4096, memory, limit)
                .unwrap(),
        );
        assert_eq!(actual, expected, "limit={limit}, input={input:?}");
    }
}

#[test]
fn multiple_useful_webs_split_minimally_and_preserve_read_entry_abi() {
    let p = program(
        2,
        vec![step(
            0,
            vec![
                set(1, r(0)),
                set(0, c(7)),
                store(c(4096), Width::U8, r(0)),
                set(0, c(11)),
            ],
            Control::Return(r(0)),
        )],
    );
    let result = split(&p).unwrap();
    assert_eq!(
        result.stats(),
        WebStats {
            definitions: 5,
            webs: 3,
            split_registers: 1,
            fresh_registers: 2
        }
    );
    let candidate = result.program();
    shape(&p, candidate);
    assert_eq!(candidate.instructions()[0].assignments[0].value, r(0));
    assert_eq!(
        candidate.instructions()[0].assignments[0].destination,
        Reg(1).into()
    );
    let first = &candidate.instructions()[0].assignments[1].destination;
    let last = &candidate.instructions()[0].assignments[3].destination;
    assert!(matches!(first, Place::Register(Reg(2..))));
    assert!(matches!(last, Place::Register(Reg(2..))));
    assert_ne!(first, last);
    for initial in [0, 1, u64::MAX] {
        replay(&p, candidate, &[initial, 0xdead], &[0x37; 32], &[0, 1, 2]);
    }
    assert_eq!(
        split(&p).unwrap().program().instructions(),
        candidate.instructions()
    );
}

#[test]
fn zero_or_one_useful_web_keeps_exact_ir_and_sparse_original_register_domain() {
    let p = program(
        2,
        vec![
            step(0, vec![set(0, c(1)), set(0, c(7))], Control::Return(r(0))),
            step(1, vec![set(1, r(0))], Control::Return(r(1))),
        ],
    );
    let result = split(&p).unwrap();
    assert_eq!(result.stats().fresh_registers, 0);
    assert_eq!(result.program().instructions(), p.instructions());
    assert_eq!(result.program().register_count(), 2);
    let sparse = program(
        1_000_000,
        vec![step(
            0,
            vec![
                set(999_999, c(7)),
                store(c(4096), Width::U8, r(999_999)),
                set(999_999, c(11)),
            ],
            Control::Return(r(999_999)),
        )],
    );
    let result = split(&sparse).unwrap();
    assert_eq!(result.stats().fresh_registers, 1);
    assert_eq!(result.program().register_count(), 1_000_001);
    shape(&sparse, result.program());
}

#[test]
fn diamonds_union_both_lazy_arm_definitions_and_keep_dead_and_unreachable_writes_safe() {
    let p = program(
        4,
        vec![
            step(
                0,
                vec![set(1, r(0))],
                Control::Branch {
                    condition: r(2),
                    target: 2,
                },
            ),
            step(1, vec![set(0, c(7))], Control::Jump(3)),
            step(2, vec![set(0, c(11))], Control::Jump(3)),
            step(
                3,
                vec![
                    set(3, Expr::select(c(0), r(0), r(1))),
                    set(0, c(99)),
                    set(0, c(13)),
                    store(c(4096), Width::U8, r(0)),
                ],
                Control::Return(b(BinaryOp::Add, r(3), r(0))),
            ),
            step(4, vec![set(0, r(1))], Control::Return(r(0))),
        ],
    );
    let result = split(&p).unwrap();
    let candidate = result.program();
    shape(&p, candidate);
    assert_eq!(
        candidate.instructions()[1].assignments[0].destination,
        candidate.instructions()[2].assignments[0].destination,
        "syntactic reads in a lazy unselected arm must join both predecessors"
    );
    assert_eq!(
        candidate.instructions()[3].assignments[1].destination,
        Reg(0).into(),
        "unread write may retain old slot"
    );
    assert_eq!(candidate.instructions()[4], p.instructions()[4]);
    for condition in [0, 1] {
        for initial in [0, 7, u64::MAX] {
            replay(
                &p,
                candidate,
                &[initial, 0xdead, condition, 0xbad],
                &[0x17; 32],
                &[0, 1, 2, 3, 4, 5],
            );
        }
    }
}

#[test]
fn entry_backedge_meets_the_original_seed_before_every_sequential_read() {
    let p = program(
        2,
        vec![
            step(
                0,
                vec![
                    store(c(4096), Width::U8, r(0)),
                    set(1, r(0)),
                    store(c(4097), Width::U8, r(1)),
                    set(1, c(7)),
                    store(c(4098), Width::U8, r(1)),
                    set(0, b(BinaryOp::Sub, r(0), c(1))),
                ],
                Control::Branch {
                    condition: r(0),
                    target: 0,
                },
            ),
            step(1, vec![], Control::Return(r(0))),
        ],
    );
    let result = split(&p).unwrap();
    let candidate = result.program();
    assert_eq!(
        result.stats().fresh_registers,
        1,
        "only unrelated r1 definitions need splitting"
    );
    assert_eq!(candidate.instructions()[0].assignments[0].value, r(0));
    assert_eq!(
        candidate.instructions()[0].assignments[5].destination,
        Reg(0).into()
    );
    assert_eq!(candidate.instructions()[1].control, Control::Return(r(0)));
    shape(&p, candidate);
    for count in [0, 1, 2, 5] {
        replay(
            &p,
            candidate,
            &[count, 0xfeed],
            &[0x11; 32],
            &[0, 1, 2, 3, 8, 12],
        );
    }
}

#[test]
fn renamed_addresses_rhs_and_lazy_reads_preserve_first_fault_and_partial_memory() {
    let p = program(
        3,
        vec![step(
            0,
            vec![
                store(r(0), Width::U8, c(0xa5)),
                set(0, r(1)),
                store(
                    r(0),
                    Width::U64,
                    Expr::load(b(BinaryOp::Add, r(1), c(16)), Width::U8),
                ),
                set(0, Expr::load(r(1), Width::U16)),
                set(
                    2,
                    Expr::select(r(2), Expr::load(c(u64::MAX), Width::U8), r(0)),
                ),
            ],
            Control::Return(b(BinaryOp::Add, r(0), r(2))),
        )],
    );
    let result = split(&p).unwrap();
    assert!(result.stats().fresh_registers >= 3);
    let candidate = result.program();
    shape(&p, candidate);
    let memory: Vec<_> = (0..32).map(|n| (n * 17 + 3) as u8).collect();
    for left in [4096, 4127, 4128, u64::MAX] {
        for right in [4096, 4104, 4120, 4126, u64::MAX] {
            for condition in [0, 1] {
                replay(
                    &p,
                    candidate,
                    &[left, right, condition],
                    &memory,
                    &[0, 1, 2],
                );
            }
        }
    }
    let report = candidate
        .run_with_memory(&[4096, 4126, 0, 0xdead, 0xbeef, 0xf00d], 4096, &memory, 1)
        .unwrap();
    assert_eq!(
        report.status,
        RunStatus::Fault(MemoryFault {
            access: AccessKind::Write,
            address: 4126,
            width: Width::U64
        })
    );
    assert_eq!(report.state.memory[0], 0xa5);
}

#[test]
fn read_before_write_in_self_address_load_uses_entry_value_then_new_web() {
    let p = program(
        1,
        vec![step(
            0,
            vec![
                set(0, Expr::load(r(0), Width::U64)),
                store(c(4120), Width::U8, r(0)),
                set(0, b(BinaryOp::Add, r(0), c(1))),
            ],
            Control::Return(r(0)),
        )],
    );
    let result = split(&p).unwrap();
    let candidate = result.program();
    shape(&p, candidate);
    assert!(
        matches!(&candidate.instructions()[0].assignments[0].value, Expr::Load { address, .. } if **address == r(0))
    );
    assert_ne!(
        candidate.instructions()[0].assignments[0].destination,
        Reg(0).into()
    );
    for address in [4096, 4104, 4120, 4127, u64::MAX] {
        replay(&p, candidate, &[address], &[0x11; 32], &[0, 1, 2]);
    }
}

#[test]
fn all_input_depth_definition_block_and_fresh_id_bounds_fall_back_whole() {
    let mut deep = r(0);
    for _ in 0..130 {
        deep = b(BinaryOp::Add, deep, c(1));
    }
    let p = program(
        1,
        vec![
            step(0, vec![], Control::Return(c(0))),
            step(
                1,
                vec![store(deep.clone(), Width::U8, c(0))],
                Control::Return(c(0)),
            ),
        ],
    );
    assert!(
        split(&p).is_none(),
        "unreachable memory destinations must validate"
    );
    let p = program(
        1,
        vec![step(
            0,
            vec![set(0, Expr::select(c(0), deep, c(0)))],
            Control::Return(c(0)),
        )],
    );
    assert!(split(&p).is_none());
    let p = program(
        1,
        vec![step(0, vec![set(0, c(0)); 20_001], Control::Return(r(0)))],
    );
    assert!(split(&p).is_none());
    let p = program(
        1,
        (0..4100)
            .map(|n| step(n, vec![], Control::Return(c(0))))
            .collect(),
    );
    assert!(split(&p).is_none());
    let p = program(
        usize::MAX,
        vec![step(
            0,
            vec![set(0, c(7)), store(c(4096), Width::U8, r(0)), set(0, c(11))],
            Control::Return(r(0)),
        )],
    );
    assert!(split(&p).is_none(), "fresh register count must not wrap");
}

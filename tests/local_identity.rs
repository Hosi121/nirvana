use nirvana::allocation::allocate_locals;
use nirvana::ir::{
    Assignment, BinaryOp, Control, Expr, IrInstruction, Place, Program, Reg, RunReport, RunStatus,
    Width,
};
use nirvana::local_identity::{LocalIdentities, refine};
use std::collections::{BTreeMap, BTreeSet};

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
fn program(count: usize, steps: Vec<IrInstruction>) -> Program {
    Program::new(0, count, steps).unwrap()
}

// Check the partition property independently, without using DSU internals or
// relying on one particular coloring/group count for executable cases.
fn partition(ids: &LocalIdentities, storage: &[(Reg, usize)], count: usize) {
    let original: BTreeMap<_, _> = storage.iter().map(|&(reg, color)| (reg.0, color)).collect();
    let mut members: BTreeMap<_, BTreeSet<_>> = BTreeMap::new();
    for reg in 0..count {
        assert_eq!(ids.group(Reg(reg)).is_some(), original.contains_key(&reg));
        if let Some(group) = ids.group(Reg(reg)) {
            members.entry(group).or_default().insert(original[&reg]);
        }
    }
    assert!(
        members.values().all(|colors| colors.len() == 1),
        "a refined group crossed colors"
    );
    assert_eq!(
        members.keys().copied().collect::<Vec<_>>(),
        (0..ids.groups()).collect::<Vec<_>>()
    );
    assert_eq!(ids.group(Reg(count)), None);
}

#[test]
fn copies_updates_and_root_operands_connect_but_load_addresses_and_selects_do_not() {
    let p = program(
        10,
        vec![
            step(
                0,
                vec![
                    set(1, c(7)),
                    set(2, r(1)),
                    set(3, b(BinaryOp::Add, r(2), c(1))),
                    set(4, Expr::load(r(3), Width::U8)),
                    set(5, Expr::select(r(3), r(1), r(2))),
                    set(6, b(BinaryOp::Eq, r(3), r(1))),
                    set(7, b(BinaryOp::Shr, c(8), r(3))),
                    set(8, b(BinaryOp::Sub, c(8), r(3))),
                    set(9, b(BinaryOp::Add, Expr::load(r(4), Width::U16), r(3))),
                    store(r(4), Width::U8, r(1)),
                ],
                Control::Return(b(BinaryOp::Add, r(1), r(4))),
            ),
            step(1, vec![set(5, r(1))], Control::Return(r(5))),
        ],
    );
    let storage: Vec<_> = (1..10).map(|n| (Reg(n), 17)).collect();
    let before = p.instructions().to_vec();
    let ids = refine(&p, &storage).unwrap();
    partition(&ids, &storage, 10);
    for reg in [2, 3, 9] {
        assert_eq!(ids.group(Reg(1)), ids.group(Reg(reg)));
    }
    for reg in [4, 5, 6, 7, 8] {
        assert_ne!(ids.group(Reg(1)), ids.group(Reg(reg)), "non-lineage r{reg}");
    }
    assert_eq!(ids.groups(), 6);
    assert_eq!(p.instructions(), before);
}

#[test]
fn arithmetic_root_policy_is_directional_and_never_crosses_storage_colors() {
    for op in [
        BinaryOp::Add,
        BinaryOp::Mul,
        BinaryOp::And,
        BinaryOp::Or,
        BinaryOp::Xor,
        BinaryOp::Sub,
        BinaryOp::Shl,
        BinaryOp::Shr,
        BinaryOp::Eq,
        BinaryOp::Ne,
        BinaryOp::Ult,
        BinaryOp::Ule,
        BinaryOp::UMulHigh,
    ] {
        let p = program(
            4,
            vec![step(
                0,
                vec![set(3, b(op, r(1), r(2)))],
                Control::Return(r(3)),
            )],
        );
        let storage = [(Reg(1), 0), (Reg(2), 0), (Reg(3), 0)];
        let ids = refine(&p, &storage).unwrap();
        partition(&ids, &storage, 4);
        let left = matches!(
            op,
            BinaryOp::Add
                | BinaryOp::Mul
                | BinaryOp::And
                | BinaryOp::Or
                | BinaryOp::Xor
                | BinaryOp::Sub
                | BinaryOp::Shl
                | BinaryOp::Shr
        );
        let right = matches!(
            op,
            BinaryOp::Add | BinaryOp::Mul | BinaryOp::And | BinaryOp::Or | BinaryOp::Xor
        );
        assert_eq!(ids.group(Reg(3)) == ids.group(Reg(1)), left, "{op:?}");
        assert_eq!(ids.group(Reg(3)) == ids.group(Reg(2)), right, "{op:?}");
        let separate = [(Reg(1), 4), (Reg(2), usize::MAX), (Reg(3), 9)];
        let split = refine(&p, &separate).unwrap();
        partition(&split, &separate, 4);
        assert_eq!(split.groups(), 3);
    }
}

#[test]
fn dense_labels_are_deterministic_for_sparse_colors_subsets_and_input_order() {
    let p = program(
        8,
        vec![step(
            0,
            vec![set(3, r(1)), set(7, b(BinaryOp::Xor, r(5), r(3)))],
            Control::Return(r(7)),
        )],
    );
    let storage = [
        (Reg(7), usize::MAX),
        (Reg(3), usize::MAX),
        (Reg(5), 4),
        (Reg(1), usize::MAX),
    ];
    let ids = refine(&p, &storage).unwrap();
    partition(&ids, &storage, 8);
    let reversed: Vec<_> = storage.iter().copied().rev().collect();
    let other = refine(&p, &reversed).unwrap();
    for reg in 0..8 {
        assert_eq!(ids.group(Reg(reg)), other.group(Reg(reg)));
    }
    assert_eq!(ids.groups(), 2);
    let subset = [(Reg(1), 4), (Reg(7), 4)];
    assert_ne!(
        refine(&p, &subset).unwrap().group(Reg(1)),
        refine(&p, &subset).unwrap().group(Reg(7)),
        "excluded intermediate registers must not bridge connectivity"
    );
}

#[test]
fn invalid_inputs_and_whole_input_limits_never_return_partial_identities() {
    let p = program(2, vec![step(0, vec![set(1, r(0))], Control::Return(r(1)))]);
    assert!(refine(&p, &[(Reg(1), 0), (Reg(1), 1)]).is_none());
    assert!(refine(&p, &[(Reg(2), 0)]).is_none());
    assert_eq!(refine(&p, &[]).unwrap().groups(), 0);
    let mut deep = r(0);
    for _ in 0..130 {
        deep = b(BinaryOp::Add, deep, c(1));
    }
    for assignments in [
        vec![store(deep.clone(), Width::U8, c(0))],
        vec![set(0, Expr::select(c(0), deep.clone(), c(0)))],
    ] {
        let p = program(2, vec![step(0, assignments, Control::Return(c(0)))]);
        assert!(
            refine(&p, &[]).is_none(),
            "empty subset cannot bypass expression validation"
        );
        assert!(refine(&p, &[(Reg(1), 0)]).is_none());
    }
    let p = program(
        2,
        vec![
            step(0, vec![], Control::Return(c(0))),
            step(1, vec![], Control::Return(deep)),
        ],
    );
    assert!(
        refine(&p, &[(Reg(1), 0)]).is_none(),
        "unreachable control still must validate"
    );
    let p = program(4097, vec![step(0, vec![], Control::Return(c(0)))]);
    let storage: Vec<_> = (0..4097).map(|n| (Reg(n), 0)).collect();
    assert!(refine(&p, &storage).is_none());
    let p = program(
        1,
        vec![step(0, vec![set(0, c(1)); 100_000], Control::Return(r(0)))],
    );
    assert!(refine(&p, &[(Reg(0), 0)]).is_none());
}

fn rewrite(expr: &Expr, map: &impl Fn(Reg) -> Reg) -> Expr {
    match expr {
        Expr::Const(_) => expr.clone(),
        Expr::Register(reg) => Expr::Register(map(*reg)),
        Expr::Binary(op, a, z) => b(*op, rewrite(a, map), rewrite(z, map)),
        Expr::Load { address, width } => Expr::load(rewrite(address, map), *width),
        Expr::Select {
            condition,
            taken,
            not_taken,
        } => Expr::select(
            rewrite(condition, map),
            rewrite(taken, map),
            rewrite(not_taken, map),
        ),
    }
}

fn remap(p: &Program, groups: usize, group: impl Fn(Reg) -> Option<usize>) -> Program {
    let bank = p.register_count() + 3;
    let map = |reg| group(reg).map(|group| Reg(bank + group)).unwrap_or(reg);
    let steps = p
        .instructions()
        .iter()
        .map(|instruction| IrInstruction {
            address: instruction.address,
            size: instruction.size,
            assignments: instruction
                .assignments
                .iter()
                .map(|assignment| Assignment {
                    destination: match &assignment.destination {
                        Place::Register(reg) => Place::Register(map(*reg)),
                        Place::Memory { address, width } => Place::Memory {
                            address: rewrite(address, &map),
                            width: *width,
                        },
                    },
                    value: rewrite(&assignment.value, &map),
                })
                .collect(),
            control: match &instruction.control {
                Control::Return(value) => Control::Return(rewrite(value, &map)),
                Control::Branch { condition, target } => Control::Branch {
                    condition: rewrite(condition, &map),
                    target: *target,
                },
                other => other.clone(),
            },
        })
        .collect();
    Program::new(p.cfg().block(p.cfg().entry()).start, bank + groups, steps).unwrap()
}

#[derive(Debug, Eq, PartialEq)]
struct Observation {
    status: RunStatus,
    memory: Vec<u8>,
    base: u64,
    trace: Vec<u64>,
    instruction: Option<u64>,
    unchanged: Vec<(usize, u64)>,
}
fn observe(report: RunReport, eligible: &[Reg], count: usize) -> Observation {
    let unchanged = report
        .state
        .registers
        .iter()
        .copied()
        .take(count)
        .enumerate()
        .filter(|(n, _)| !eligible.contains(&Reg(*n)))
        .collect();
    Observation {
        status: report.status,
        memory: report.state.memory,
        base: report.state.memory_base,
        trace: report.state.trace,
        instruction: report.state.instruction,
        unchanged,
    }
}

#[test]
fn refined_and_original_storage_banks_preserve_loops_aliases_faults_and_cutoffs() {
    let p = program(
        11,
        vec![
            step(
                0,
                vec![
                    set(4, r(0)),
                    set(5, Expr::load(r(4), Width::U64)),
                    set(6, r(5)),
                    set(7, b(BinaryOp::And, r(3), c(3))),
                    set(8, r(1)),
                    set(9, c(0)),
                    set(10, r(2)),
                ],
                Control::Jump(1),
            ),
            step(
                1,
                vec![
                    store(r(8), Width::U8, r(6)),
                    set(4, r(5)),
                    set(6, b(BinaryOp::Add, r(6), Expr::load(r(8), Width::U16))),
                    set(9, b(BinaryOp::Xor, r(9), r(6))),
                    set(7, b(BinaryOp::Sub, r(7), c(1))),
                ],
                Control::Branch {
                    condition: r(7),
                    target: 1,
                },
            ),
            step(
                2,
                vec![
                    set(10, Expr::select(r(2), Expr::load(r(8), Width::U32), r(9))),
                    store(r(0), Width::U64, b(BinaryOp::Add, r(6), r(10))),
                ],
                Control::Return(b(BinaryOp::Xor, r(9), r(10))),
            ),
        ],
    );
    let memory: Vec<_> = (0..32).map(|n| (n * 29 + 3) as u8).collect();
    let mut comparisons = 0;
    for eligible in [
        (4..11).map(Reg).collect::<Vec<_>>(),
        vec![Reg(5), Reg(6), Reg(7), Reg(9), Reg(10)],
        vec![Reg(8)],
    ] {
        let allocation = allocate_locals(&p, &eligible).unwrap();
        let storage: Vec<_> = eligible
            .iter()
            .map(|&reg| (reg, allocation.color(reg).unwrap()))
            .collect();
        let ids = refine(&p, &storage).unwrap();
        partition(&ids, &storage, 11);
        let before = remap(&p, allocation.colors(), |reg| allocation.color(reg));
        let after = remap(&p, ids.groups(), |reg| ids.group(reg));
        for left in [4096, 4097, 4120, 4127, u64::MAX] {
            for right in [4096, 4097, 4126, 4127, u64::MAX] {
                for count in [0, 1, 3] {
                    for condition in [0, 1] {
                        let mut input: Vec<_> = (0..11)
                            .map(|n| 0x93a5_7c21_f0de_864bu64.wrapping_mul(n + 1))
                            .collect();
                        input[..4].copy_from_slice(&[left, right, condition, count]);
                        for limit in [0, 1, 2, 3, 5, 12] {
                            let expected = observe(
                                p.run_with_memory(&input, 4096, &memory, limit).unwrap(),
                                &eligible,
                                11,
                            );
                            for (version, salt) in [(&before, 0x1357_u64), (&after, 0x2468_u64)] {
                                let mut poisoned = input.clone();
                                poisoned.extend(
                                    (input.len()..version.register_count())
                                        .map(|n| salt.wrapping_mul(n as u64 + 1)),
                                );
                                let actual = observe(
                                    version
                                        .run_with_memory(&poisoned, 4096, &memory, limit)
                                        .unwrap(),
                                    &eligible,
                                    11,
                                );
                                assert_eq!(
                                    actual, expected,
                                    "input={input:?}, limit={limit}, eligible={eligible:?}"
                                );
                                comparisons += 1;
                            }
                        }
                    }
                }
            }
        }
    }
    assert_eq!(comparisons, 5400);
}

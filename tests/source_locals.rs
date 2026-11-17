use nirvana::{allocation_verify, ir, source_locals};

use allocation_verify::{AllocationError, validate};
use ir::{Assignment, BinaryOp, Control, Expr, IrInstruction, Place, Program, Reg, Width};
use source_locals::{SourceAllocation, SourceScore, recover};
use std::collections::{BTreeMap, BTreeSet};

fn r(id: usize) -> Expr {
    Expr::Register(Reg(id))
}
fn c(value: u64) -> Expr {
    Expr::Const(value)
}
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
fn make_program(count: usize, assignments: Vec<Assignment>, result: Expr) -> Program {
    Program::new(0, count, vec![ins(0, assignments, Control::Return(result))]).unwrap()
}
fn mapping(allocation: &SourceAllocation, initial: &[(Reg, usize)]) -> Vec<(Reg, usize)> {
    initial
        .iter()
        .map(|&(reg, _)| (reg, allocation.color(reg).unwrap()))
        .collect()
}
fn checked(
    program: &Program,
    initial: &[(Reg, usize)],
    lineages: &[(Reg, usize)],
) -> SourceAllocation {
    let result = recover(program, initial, lineages).expect("an improving validated candidate");
    let proposed = mapping(&result, initial);
    assert_eq!(result.evidence(), validate(program, &proposed).unwrap());
    assert!(result.stats().after < result.stats().before);
    let used: BTreeSet<_> = proposed.iter().map(|(_, color)| *color).collect();
    assert_eq!(used, (0..used.len()).collect());
    assert_eq!(result.stats().after.locals, used.len());
    result
}

// Independent concrete relabeling. Initial colors are never used as vector
// indices; an entirely fresh compact bank starts with unrelated poison values.
fn remap(program: &Program, mapping: &[(Reg, usize)]) -> Program {
    let groups: BTreeSet<_> = mapping.iter().map(|(_, color)| *color).collect();
    let groups: BTreeMap<_, _> = groups
        .into_iter()
        .enumerate()
        .map(|(index, color)| (color, program.register_count() + index))
        .collect();
    let names: BTreeMap<_, _> = mapping
        .iter()
        .map(|(reg, color)| (reg.0, groups[color]))
        .collect();
    let name = |reg: Reg| Reg(names.get(&reg.0).copied().unwrap_or(reg.0));
    fn expression(value: &Expr, name: &impl Fn(Reg) -> Reg) -> Expr {
        match value {
            Expr::Const(_) => value.clone(),
            Expr::Register(reg) => Expr::Register(name(*reg)),
            Expr::Binary(op, a, z) => b(*op, expression(a, name), expression(z, name)),
            Expr::Load { address, width } => Expr::load(expression(address, name), *width),
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => Expr::select(
                expression(condition, name),
                expression(taken, name),
                expression(not_taken, name),
            ),
        }
    }
    let instructions = program
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
                        Place::Register(reg) => Place::Register(name(*reg)),
                        Place::Memory { address, width } => Place::Memory {
                            address: expression(address, &name),
                            width: *width,
                        },
                    },
                    value: expression(&assignment.value, &name),
                })
                .collect(),
            control: match &instruction.control {
                Control::Branch { condition, target } => Control::Branch {
                    condition: expression(condition, &name),
                    target: *target,
                },
                Control::Return(value) => Control::Return(expression(value, &name)),
                other => other.clone(),
            },
        })
        .collect();
    Program::new(
        program.cfg().block(program.cfg().entry()).start,
        program.register_count() + groups.len(),
        instructions,
    )
    .unwrap()
}
fn replay(
    program: &Program,
    mapping: &[(Reg, usize)],
    input: &[u64],
    memory: &[u8],
    limits: &[usize],
) {
    let renamed = remap(program, mapping);
    for poison in [0, u64::MAX, 0x8123_4567_dead_beef] {
        let mut registers = input.to_vec();
        registers.extend(
            (input.len()..renamed.register_count())
                .map(|index| poison ^ (index as u64).wrapping_mul(0x9e37_79b9)),
        );
        for &limit in limits {
            let expected = program.run_with_memory(input, 0, memory, limit).unwrap();
            let actual = renamed
                .run_with_memory(&registers, 0, memory, limit)
                .unwrap();
            assert_eq!(
                actual.status, expected.status,
                "input={input:?},limit={limit},poison={poison}"
            );
            assert_eq!(actual.state.memory, expected.state.memory);
            assert_eq!(actual.state.memory_base, expected.state.memory_base);
            assert_eq!(actual.state.trace, expected.state.trace);
            assert_eq!(actual.state.instruction, expected.state.instruction);
        }
    }
}

#[test]
fn distinct_known_lineages_split_a_reused_slot_even_with_more_locals() {
    let program = make_program(
        3,
        vec![
            set(1, r(0)),
            store(c(0), Width::U8, r(1)),
            set(2, b(BinaryOp::Add, r(0), c(7))),
        ],
        r(2),
    );
    let initial = [(Reg(1), 91), (Reg(2), 91)];
    let before = program.instructions().to_vec();
    let result = checked(&program, &initial, &[(Reg(1), 3), (Reg(2), 4)]);
    assert_eq!(
        result.stats().before,
        SourceScore {
            mixed: 1,
            fragments: 0,
            locals: 1
        }
    );
    assert_eq!(
        result.stats().after,
        SourceScore {
            mixed: 0,
            fragments: 0,
            locals: 2
        }
    );
    assert_ne!(result.color(Reg(1)), result.color(Reg(2)));
    assert_eq!(result.color(Reg(0)), None);
    assert_eq!(result.color(Reg(999)), None);
    assert_eq!(program.instructions(), before);
    for value in [0, 1, u64::MAX] {
        replay(
            &program,
            &mapping(&result, &initial),
            &[value, 71, 72],
            &[0xa5; 8],
            &[0, 1, 2],
        );
    }
}

#[test]
fn fragmented_nonoverlapping_versions_merge_across_initial_colors() {
    let program = make_program(
        3,
        vec![
            set(1, b(BinaryOp::Add, r(0), c(1))),
            store(c(0), Width::U16, r(1)),
            set(2, b(BinaryOp::Xor, r(0), c(7))),
        ],
        r(2),
    );
    let initial = [(Reg(1), 7), (Reg(2), 900)];
    let result = checked(
        &program,
        &initial,
        &[(Reg(1), usize::MAX), (Reg(2), usize::MAX)],
    );
    assert_eq!(result.color(Reg(1)), result.color(Reg(2)));
    assert_eq!(result.stats().before.fragments, 1);
    assert_eq!(result.stats().after.fragments, 0);
    assert_eq!(result.stats().rollbacks, 0);
    for value in [0, 1, 255, 1 << 63, u64::MAX] {
        for memory in [&[][..], &[0xa5; 8][..]] {
            replay(
                &program,
                &mapping(&result, &initial),
                &[value, 91, 92],
                memory,
                &[0, 1, 2],
            );
        }
    }
}

#[test]
fn conflicting_lineage_rolls_back_while_an_independent_merge_survives() {
    let program = make_program(
        5,
        vec![
            set(1, c(7)),
            set(2, c(9)),
            store(c(0), Width::U16, b(BinaryOp::Add, r(1), r(2))),
            set(3, b(BinaryOp::Add, r(0), c(3))),
            store(c(2), Width::U8, r(3)),
            set(4, b(BinaryOp::Xor, r(0), c(5))),
        ],
        r(4),
    );
    let initial = [(Reg(1), 0), (Reg(2), 1), (Reg(3), 2), (Reg(4), 3)];
    let invalid = [(Reg(1), 0), (Reg(2), 0), (Reg(3), 1), (Reg(4), 1)];
    assert!(matches!(
        validate(&program, &invalid),
        Err(AllocationError::ReadCorrespondence { .. })
    ));
    let result = checked(
        &program,
        &initial,
        &[(Reg(1), 7), (Reg(2), 7), (Reg(3), 8), (Reg(4), 8)],
    );
    assert_eq!(result.stats().rollbacks, 1);
    assert_ne!(result.color(Reg(1)), result.color(Reg(2)));
    assert_eq!(result.color(Reg(3)), result.color(Reg(4)));
    assert_eq!(result.stats().before.fragments, 2);
    assert_eq!(result.stats().after.fragments, 1);
    for memory in [&[][..], &[0xa5; 2][..], &[0x91; 8][..]] {
        replay(
            &program,
            &mapping(&result, &initial),
            &[u64::MAX, 91, 92, 93, 94],
            memory,
            &[0, 1, 2],
        );
    }
}

#[test]
fn direct_equal_copy_can_share_but_lineage_never_asserts_value_equality() {
    let equal = make_program(
        3,
        vec![set(1, r(0)), set(2, r(1))],
        b(BinaryOp::Add, r(1), r(2)),
    );
    let initial = [(Reg(1), 1), (Reg(2), 2)];
    let lineages = [(Reg(1), 5), (Reg(2), 5)];
    let result = checked(&equal, &initial, &lineages);
    assert_eq!(result.color(Reg(1)), result.color(Reg(2)));
    for value in [0, 1, 1 << 63, u64::MAX] {
        replay(
            &equal,
            &mapping(&result, &initial),
            &[value, 91, 92],
            &[],
            &[0, 1, 2],
        );
    }
    let distinct = make_program(
        3,
        vec![set(1, r(0)), set(2, b(BinaryOp::Add, r(0), c(1)))],
        b(BinaryOp::Add, r(1), r(2)),
    );
    assert!(recover(&distinct, &initial, &lineages).is_none());
}

#[test]
fn unknown_is_not_a_source_identity_and_cannot_reward_gratuitous_splitting() {
    let program = make_program(
        4,
        vec![
            set(1, r(0)),
            store(c(0), Width::U8, r(1)),
            set(2, c(7)),
            store(c(1), Width::U8, r(2)),
            set(3, c(9)),
        ],
        r(3),
    );
    let initial = [(Reg(1), 3), (Reg(2), 3), (Reg(3), 3)];
    assert!(recover(&program, &initial, &[(Reg(1), 99)]).is_none());
    assert!(recover(&program, &initial, &[]).is_none());
    // Known mixing justifies a split, while anonymous original sharing stays
    // together in a namespace separate from both known lineage classes.
    let result = checked(&program, &initial, &[(Reg(1), 7), (Reg(2), 8)]);
    assert_eq!(result.stats().before.mixed, 1);
    assert_eq!(result.stats().after.locals, 3);
    assert_ne!(result.color(Reg(3)), result.color(Reg(1)));
    assert_ne!(result.color(Reg(3)), result.color(Reg(2)));
}

#[test]
fn input_order_and_sparse_opaque_labels_do_not_change_dense_output() {
    let program = make_program(
        3,
        vec![set(1, r(0)), store(c(0), Width::U8, r(1)), set(2, c(9))],
        r(2),
    );
    let initial = [(Reg(2), usize::MAX), (Reg(1), 55)];
    let known = [(Reg(2), 9999), (Reg(1), 9999)];
    let a = checked(&program, &initial, &known);
    let z = checked(
        &program,
        &[(Reg(1), 0), (Reg(2), 123)],
        &[(Reg(1), 17), (Reg(2), 17)],
    );
    assert_eq!(mapping(&a, &initial), mapping(&z, &initial));
    assert_eq!(a.stats().after, z.stats().after);
}

#[test]
fn malformed_and_oversized_inputs_or_invalid_initial_maps_return_none() {
    let program = make_program(
        3,
        vec![set(1, c(7)), set(2, c(9))],
        b(BinaryOp::Add, r(1), r(2)),
    );
    let initial = [(Reg(1), 0), (Reg(2), 1)];
    for known in [
        vec![(Reg(1), 7), (Reg(1), 7)],
        vec![(Reg(0), 7)],
        vec![(Reg(99), 7)],
        vec![(Reg(1), 7); 4097],
    ] {
        assert!(recover(&program, &initial, &known).is_none());
    }
    for initial in [
        vec![(Reg(1), 0), (Reg(1), 1)],
        vec![(Reg(1), 0), (Reg(2), 0)],
        vec![(Reg(99), 0)],
        vec![(Reg(1), 0); 4097],
    ] {
        assert!(recover(&program, &initial, &[]).is_none());
    }
    let entry = make_program(1, vec![], r(0));
    assert!(recover(&entry, &[(Reg(0), 0)], &[(Reg(0), 5)]).is_none());
    assert!(recover(&entry, &[], &[]).is_none());
}

#[test]
fn repeated_conflicts_are_bounded_and_do_not_return_a_partial_candidate() {
    let mut assignments = Vec::new();
    let mut initial = Vec::new();
    let mut lineages = Vec::new();
    for group in 0..16 {
        let a = group * 2 + 1;
        let z = a + 1;
        assignments.extend([
            set(a, c(7)),
            set(z, c(9)),
            store(c(0), Width::U8, b(BinaryOp::Add, r(a), r(z))),
        ]);
        initial.extend([(Reg(a), a), (Reg(z), z)]);
        lineages.extend([(Reg(a), group), (Reg(z), group)]);
    }
    assignments.extend([set(33, c(1)), store(c(0), Width::U8, r(33)), set(34, c(2))]);
    initial.extend([(Reg(33), 33), (Reg(34), 34)]);
    lineages.extend([(Reg(33), 99), (Reg(34), 99)]);
    let program = make_program(35, assignments, r(34));
    validate(&program, &initial).unwrap();
    assert!(recover(&program, &initial, &lineages).is_none());
}

#[test]
fn rolled_back_address_and_counter_with_a_safe_accumulator_merge_replay_exactly() {
    let program = Program::new(
        0,
        8,
        vec![
            ins(
                0,
                vec![set(2, c(0)), set(4, c(0)), set(6, r(0))],
                Control::Jump(1),
            ),
            ins(
                1,
                vec![
                    set(3, b(BinaryOp::Add, r(2), c(1))),
                    store(
                        b(BinaryOp::Add, r(0), b(BinaryOp::And, r(2), c(7))),
                        Width::U8,
                        r(4),
                    ),
                    set(2, r(3)),
                    set(7, r(6)),
                    set(6, b(BinaryOp::Add, r(6), c(1))),
                    store(r(7), Width::U16, r(2)),
                    set(
                        5,
                        b(
                            BinaryOp::Add,
                            r(4),
                            Expr::select(
                                r(1),
                                Expr::load(c(0), Width::U8),
                                Expr::load(c(u64::MAX), Width::U8),
                            ),
                        ),
                    ),
                    set(4, r(5)),
                    set(1, b(BinaryOp::Sub, r(1), c(1))),
                ],
                Control::Branch {
                    condition: r(1),
                    target: 1,
                },
            ),
            ins(2, vec![], Control::Return(b(BinaryOp::Add, r(2), r(4)))),
        ],
    )
    .unwrap();
    let initial: Vec<_> = (2..8).map(|id| (Reg(id), id * 31)).collect();
    let lineages = [
        (Reg(2), 11),
        (Reg(3), 11),
        (Reg(4), 22),
        (Reg(5), 22),
        (Reg(6), 33),
        (Reg(7), 33),
    ];
    let original = program.instructions().to_vec();
    let result = checked(&program, &initial, &lineages);
    assert_eq!(result.stats().rollbacks, 2);
    assert_ne!(result.color(Reg(2)), result.color(Reg(3)));
    assert_ne!(result.color(Reg(6)), result.color(Reg(7)));
    assert_eq!(result.color(Reg(4)), result.color(Reg(5)));
    for pointer in [0, 1, 7, u64::MAX] {
        for count in [0, 1, 3] {
            for memory in [&[][..], &[0x31; 3][..], &[0x95; 8][..]] {
                replay(
                    &program,
                    &mapping(&result, &initial),
                    &[pointer, count, 91, 92, 93, 94, 95, 96],
                    memory,
                    &[0, 1, 2, 3, 5, 8],
                );
            }
        }
    }
    assert_eq!(program.instructions(), original);
}

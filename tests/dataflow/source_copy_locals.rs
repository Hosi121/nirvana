use crate::support::ir::c;
use crate::support::ir::r;
use ir::{Assignment, BinaryOp, Control, Expr, IrInstruction, Place, Program, Reg, Width};
use nirvana::{allocation_verify, ir, source_locals, value_role::ValueRole};
use std::collections::{BTreeMap, BTreeSet};
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

fn proposed(
    program: &Program,
    initial: &[(Reg, usize)],
    widths: &[(Reg, Width)],
    roles: &[(Reg, ValueRole)],
    lineages: &[(Reg, usize)],
) -> Option<Vec<(Reg, usize)>> {
    let result = source_locals::recover_copies(program, initial, widths, roles, lineages)?;
    let map = initial
        .iter()
        .map(|&(r, _)| (r, result.color(r).unwrap()))
        .collect::<Vec<_>>();
    assert_eq!(
        allocation_verify::validate(program, &map).unwrap(),
        result.evidence()
    );
    Some(map)
}
fn widths(initial: &[(Reg, usize)]) -> Vec<(Reg, Width)> {
    initial.iter().map(|&(r, _)| (r, Width::U64)).collect()
}
fn palette(map: &[(Reg, usize)], id: usize) -> usize {
    map.iter().find(|(r, _)| r.0 == id).unwrap().1
}

#[test]
fn copy_chain_shares_with_arbitrary_poison_and_exact_fault_memory_trace() {
    let program = make_program(
        4,
        vec![
            set(1, Expr::load(c(0), Width::U64)),
            set(2, r(1)),
            set(3, r(2)),
            store(r(0), Width::U16, r(3)),
        ],
        b(BinaryOp::Add, r(1), r(2)),
    );
    let original = program.instructions().to_vec();
    let initial = [(Reg(1), usize::MAX), (Reg(2), 7), (Reg(3), 99)];
    let map = proposed(&program, &initial, &widths(&initial), &[], &[]).unwrap();
    assert_eq!(palette(&map, 1), palette(&map, 2));
    assert_eq!(palette(&map, 2), palette(&map, 3));
    for pointer in [0, 1, 7, u64::MAX] {
        for memory in [&[][..], &[0xa5; 8][..]] {
            replay(&program, &map, &[pointer, 91, 92, 93], memory, &[0, 1, 2]);
        }
    }
    assert_eq!(program.instructions(), original);
}

#[test]
fn old_source_or_copy_destination_overwrite_cannot_destroy_a_live_snapshot() {
    let initial = [(Reg(1), 1), (Reg(2), 2)];
    for dest in [1, 2] {
        let p = make_program(
            3,
            vec![set(1, r(0)), set(2, r(1)), set(dest, c(99))],
            b(BinaryOp::Add, r(1), r(2)),
        );
        assert!(proposed(&p, &initial, &widths(&initial), &[], &[]).is_none());
    }
    let p = make_program(
        3,
        vec![set(1, c(1)), store(c(0), Width::U8, r(2)), set(2, r(1))],
        r(2),
    );
    assert!(proposed(&p, &initial, &widths(&initial), &[], &[]).is_none());
}

#[test]
fn whole_color_interference_rolls_back_while_an_independent_copy_survives() {
    let p = make_program(
        6,
        vec![
            set(1, r(0)),
            set(2, r(1)),
            set(3, c(99)),
            store(c(0), Width::U8, r(2)),
            set(4, r(0)),
            set(5, r(4)),
        ],
        b(BinaryOp::Add, r(3), r(5)),
    );
    let initial = [
        (Reg(1), 10),
        (Reg(3), 10),
        (Reg(2), 20),
        (Reg(4), 30),
        (Reg(5), 40),
    ];
    let map = proposed(&p, &initial, &widths(&initial), &[], &[]).unwrap();
    assert_eq!(palette(&map, 1), palette(&map, 3));
    assert_ne!(palette(&map, 1), palette(&map, 2));
    assert_eq!(palette(&map, 4), palette(&map, 5));
    replay(
        &p,
        &map,
        &[u64::MAX, 91, 92, 93, 94, 95],
        &[0xa5; 8],
        &[0, 1, 2],
    );
}

#[test]
fn width_conflicts_decline_and_existing_group_max_width_is_preserved() {
    let p = make_program(
        3,
        vec![set(1, r(0)), set(2, r(1))],
        b(BinaryOp::Add, r(1), r(2)),
    );
    let initial = [(Reg(1), 1), (Reg(2), 2)];
    assert!(
        proposed(
            &p,
            &initial,
            &[(Reg(1), Width::U8), (Reg(2), Width::U64)],
            &[],
            &[]
        )
        .is_none()
    );
    let p = make_program(
        4,
        vec![set(1, r(0)), set(2, r(1)), set(3, r(2))],
        b(BinaryOp::Add, r(2), r(3)),
    );
    let initial = [(Reg(1), 1), (Reg(3), 1), (Reg(2), 2)];
    let map = proposed(
        &p,
        &initial,
        &[
            (Reg(1), Width::U8),
            (Reg(2), Width::U64),
            (Reg(3), Width::U64),
        ],
        &[],
        &[],
    )
    .unwrap();
    assert!(map.iter().all(|(_, c)| *c == map[0].1));
    replay(&p, &map, &[u64::MAX, 91, 92, 93], &[], &[0, 1]);
}

#[test]
fn known_roles_and_known_source_lineages_remain_separate_through_unknown_copies() {
    let p = make_program(
        4,
        vec![set(1, r(0)), set(2, r(1)), set(3, r(2))],
        b(BinaryOp::Add, r(1), r(3)),
    );
    let initial = [(Reg(1), 1), (Reg(2), 2), (Reg(3), 3)];
    for (roles, lineages) in [
        (
            vec![(Reg(1), ValueRole::Counter), (Reg(3), ValueRole::Limit)],
            vec![],
        ),
        (vec![], vec![(Reg(1), 10), (Reg(3), 20)]),
    ] {
        let map = proposed(&p, &initial, &widths(&initial), &roles, &lineages).unwrap();
        assert_eq!(palette(&map, 1), palette(&map, 2));
        assert_ne!(palette(&map, 1), palette(&map, 3));
        replay(&p, &map, &[u64::MAX, 91, 92, 93], &[], &[0, 1]);
    }
}

#[test]
fn a_new_pure_self_comparison_is_rejected_by_the_existing_c_quality_gate() {
    let initial = [(Reg(1), 1), (Reg(2), 2)];
    for op in [BinaryOp::Eq, BinaryOp::Ne, BinaryOp::Ult, BinaryOp::Ule] {
        let p = make_program(3, vec![set(1, r(0)), set(2, r(1))], b(op, r(1), r(2)));
        allocation_verify::validate(&p, &[(Reg(1), 0), (Reg(2), 0)]).unwrap();
        assert!(proposed(&p, &initial, &widths(&initial), &[], &[]).is_none());
    }
}

#[test]
fn copy_budget_failure_discards_every_partial_merge() {
    let mut assignments = vec![set(1, r(0)), set(2, r(1))];
    assignments.extend((0..4096).map(|_| set(2, r(1))));
    let p = make_program(3, assignments, r(2));
    let initial = [(Reg(1), 1), (Reg(2), 2)];
    allocation_verify::validate(&p, &initial).unwrap();
    assert!(proposed(&p, &initial, &widths(&initial), &[], &[]).is_none());
}

#[test]
fn malformed_metadata_and_arbitrary_entry_reads_decline_without_dense_ids() {
    let p = make_program(3, vec![set(1, r(0)), set(2, r(1))], r(2));
    let initial = [(Reg(1), usize::MAX), (Reg(2), 7)];
    for widths in [
        vec![],
        vec![(Reg(1), Width::U64), (Reg(1), Width::U64)],
        vec![(Reg(1), Width::U64), (Reg(99), Width::U64)],
    ] {
        assert!(proposed(&p, &initial, &widths, &[], &[]).is_none());
    }
    assert!(
        proposed(
            &p,
            &initial,
            &widths(&initial),
            &[(Reg(1), ValueRole::Limit), (Reg(1), ValueRole::Limit)],
            &[]
        )
        .is_none()
    );
    assert!(proposed(&p, &initial, &widths(&initial), &[], &[(Reg(99), 0)]).is_none());
    let p = make_program(3, vec![set(2, r(1))], r(2));
    assert!(proposed(&p, &initial, &widths(&initial), &[], &[]).is_none());
}

#[test]
fn unreachable_copies_are_not_preferences_for_reachable_storage() {
    let p = Program::new(
        0,
        3,
        vec![
            ins(
                0,
                vec![set(1, c(1)), set(2, c(2))],
                Control::Return(b(BinaryOp::Add, r(1), r(2))),
            ),
            ins(1, vec![set(2, r(1))], Control::Return(r(2))),
        ],
    )
    .unwrap();
    let initial = [(Reg(1), 1), (Reg(2), 2)];
    assert!(proposed(&p, &initial, &widths(&initial), &[], &[]).is_none());
}

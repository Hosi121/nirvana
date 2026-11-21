use std::collections::BTreeMap;

use nirvana::allocation_verify::{
    AllocationError, MAX_EXPRESSION_DEPTH, MAX_MAPPED_REGISTERS, validate,
};
use nirvana::ir::{Assignment, BinaryOp, Control, Expr, IrInstruction, Place, Program, Reg, Width};

use crate::support::ir::c;
use crate::support::ir::r;
fn binary(op: BinaryOp, left: Expr, right: Expr) -> Expr {
    Expr::binary(op, left, right)
}
fn add(left: Expr, right: Expr) -> Expr {
    binary(BinaryOp::Add, left, right)
}
fn set(index: usize, value: Expr) -> Assignment {
    Assignment {
        destination: Reg(index).into(),
        value,
    }
}
fn store(address: Expr, width: Width, value: Expr) -> Assignment {
    Assignment {
        destination: Place::Memory { address, width },
        value,
    }
}
fn i(address: u64, assignments: Vec<Assignment>, control: Control) -> IrInstruction {
    IrInstruction {
        address,
        size: 1,
        assignments,
        control,
    }
}
fn p(registers: usize, instructions: Vec<IrInstruction>) -> Program {
    Program::new(0, registers, instructions).unwrap()
}

// Independent concrete storage renaming: colors get a fresh compact register
// bank, every unmapped original register stays separate. No allocator or
// validator fact/transfer code is used, and sparse color labels are never used
// as vector indices. The new bank starts with unrelated arbitrary poison.
fn remap(program: &Program, mapping: &[(Reg, usize)]) -> Program {
    let colors: BTreeMap<_, _> = mapping.iter().map(|(_, color)| (*color, 0usize)).collect();
    let colors: BTreeMap<_, _> = colors
        .into_keys()
        .enumerate()
        .map(|(index, color)| (color, program.register_count() + index))
        .collect();
    let names: BTreeMap<_, _> = mapping
        .iter()
        .map(|(reg, color)| (reg.0, colors[color]))
        .collect();
    let name = |reg: Reg| Reg(names.get(&reg.0).copied().unwrap_or(reg.0));
    fn expression(value: &Expr, name: &impl Fn(Reg) -> Reg) -> Expr {
        match value {
            Expr::Const(value) => c(*value),
            Expr::Unary(op, value) => Expr::unary(*op, expression(value, name)),
            Expr::Register(reg) => Expr::Register(name(*reg)),
            Expr::Binary(op, left, right) => {
                binary(*op, expression(left, name), expression(right, name))
            }
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
                Control::Next => Control::Next,
                Control::Jump(target) => Control::Jump(*target),
                Control::Branch { condition, target } => Control::Branch {
                    condition: expression(condition, &name),
                    target: *target,
                },
                Control::Return(value) => Control::Return(expression(value, &name)),
            },
        })
        .collect();
    Program::new(
        program.cfg().block(program.cfg().entry()).start,
        program.register_count() + colors.len(),
        instructions,
    )
    .unwrap()
}
fn replay(program: &Program, mapping: &[(Reg, usize)], input: &[u64], memory: &[u8]) {
    validate(program, mapping).unwrap();
    let renamed = remap(program, mapping);
    for poison in [0, u64::MAX, 0xdead_beef_1234_5678] {
        let mut registers = input.to_vec();
        registers.extend(
            (input.len()..renamed.register_count())
                .map(|index| poison ^ (index as u64).wrapping_mul(0x9e37_79b9)),
        );
        for limit in 0..32 {
            let expected = program.run_with_memory(input, 0, memory, limit).unwrap();
            let actual = renamed
                .run_with_memory(&registers, 0, memory, limit)
                .unwrap();
            assert_eq!(
                actual.status, expected.status,
                "limit={limit}, poison={poison}"
            );
            assert_eq!(actual.state.memory, expected.state.memory);
            assert_eq!(actual.state.memory_base, expected.state.memory_base);
            assert_eq!(actual.state.trace, expected.state.trace);
            assert_eq!(actual.state.instruction, expected.state.instruction);
        }
    }
}
fn rejects(program: &Program, mapping: &[(Reg, usize)]) -> AllocationError {
    let error = validate(program, mapping).unwrap_err();
    assert!(
        matches!(error, AllocationError::ReadCorrespondence { .. }),
        "{error:?}"
    );
    assert!(!error.is_resource_limit());
    error
}

#[test]
fn sequential_dead_values_share_one_color_without_entry_assumptions() {
    let program = p(
        4,
        vec![i(
            0,
            vec![
                set(1, add(r(0), c(1))),
                set(2, binary(BinaryOp::Mul, r(1), c(3))),
                set(3, binary(BinaryOp::Xor, r(2), c(7))),
            ],
            Control::Return(r(3)),
        )],
    );
    let mapping = [
        (Reg(1), usize::MAX),
        (Reg(2), usize::MAX),
        (Reg(3), usize::MAX),
    ];
    let evidence = validate(&program, &mapping).unwrap();
    assert_eq!(
        (
            evidence.blocks,
            evidence.register_reads,
            evidence.mapped_registers
        ),
        (1, 3, 3)
    );
    for input in [0, 1, 255, 1 << 63, u64::MAX] {
        replay(&program, &mapping, &[input, 11, 13, 17], &[]);
    }
}

#[test]
fn a_direct_same_slot_copy_keeps_both_live_values_available() {
    let program = p(
        3,
        vec![i(
            0,
            vec![
                set(1, c(7)),
                set(2, r(1)),
                store(c(0), Width::U8, r(1)),
                store(c(1), Width::U8, r(2)),
            ],
            Control::Return(add(r(1), r(2))),
        )],
    );
    let mapping = [(Reg(1), 900), (Reg(2), 900)];
    replay(&program, &mapping, &[0, 11, 13], &[0x5a; 8]);
    let mut reverse = mapping;
    reverse.reverse();
    assert_eq!(validate(&program, &mapping), validate(&program, &reverse));
}

#[test]
fn overwriting_either_copy_alias_loses_the_other_value() {
    for (overwritten, returned) in [(1, 2), (2, 1)] {
        let program = p(
            3,
            vec![i(
                0,
                vec![set(1, c(7)), set(2, r(1)), set(overwritten, c(9))],
                Control::Return(r(returned)),
            )],
        );
        rejects(&program, &[(Reg(1), 0), (Reg(2), 0)]);
    }
}

#[test]
fn invalid_copy_source_cannot_bootstrap_a_same_slot_fact() {
    let program = p(
        3,
        vec![i(
            0,
            vec![set(1, c(7)), set(2, c(9)), set(2, r(1))],
            Control::Return(r(2)),
        )],
    );
    assert!(matches!(
        rejects(&program, &[(Reg(1), 0), (Reg(2), 0)]),
        AllocationError::ReadCorrespondence {
            assignment: Some(2),
            register: Reg(1),
            ..
        }
    ));
}

#[test]
fn eligible_entry_reads_and_self_updates_are_rejected_before_their_write() {
    let program = p(2, vec![i(0, vec![], Control::Return(r(1)))]);
    rejects(&program, &[(Reg(1), 0)]);
    let program = p(
        2,
        vec![i(0, vec![set(1, add(r(1), c(1)))], Control::Return(r(1)))],
    );
    assert!(matches!(
        rejects(&program, &[(Reg(1), 0)]),
        AllocationError::ReadCorrespondence {
            assignment: Some(0),
            ..
        }
    ));
    let program = p(2, vec![i(0, vec![set(1, r(1))], Control::Return(r(1)))]);
    rejects(&program, &[(Reg(1), 0)]);
}

#[test]
fn unmapped_writes_keep_separate_storage_but_their_rhs_still_checks_reads() {
    let program = p(
        3,
        vec![i(
            0,
            vec![set(1, c(7)), set(0, r(1)), set(2, c(9))],
            Control::Return(r(0)),
        )],
    );
    replay(&program, &[(Reg(1), 0), (Reg(2), 0)], &[0, 11, 13], &[]);
    let bad = p(
        3,
        vec![i(
            0,
            vec![set(1, c(7)), set(2, c(9)), set(0, r(1))],
            Control::Return(r(0)),
        )],
    );
    rejects(&bad, &[(Reg(1), 0), (Reg(2), 0)]);
}

#[test]
fn simultaneous_operands_and_control_reads_cannot_observe_a_lost_live_value() {
    let program = p(
        3,
        vec![i(
            0,
            vec![set(1, c(7)), set(2, c(11))],
            Control::Return(add(r(1), r(2))),
        )],
    );
    rejects(&program, &[(Reg(1), 0), (Reg(2), 0)]);
    replay(
        &program,
        &[(Reg(1), usize::MAX), (Reg(2), usize::MAX - 3)],
        &[0, 11, 13],
        &[],
    );
    let program = p(
        3,
        vec![
            i(
                0,
                vec![set(1, c(7)), set(2, c(11))],
                Control::Branch {
                    condition: r(1),
                    target: 1,
                },
            ),
            i(1, vec![], Control::Return(c(0))),
        ],
    );
    assert!(matches!(
        rejects(&program, &[(Reg(1), 0), (Reg(2), 0)]),
        AllocationError::ReadCorrespondence {
            assignment: None,
            register: Reg(1),
            ..
        }
    ));
}

#[test]
fn diamond_join_keeps_only_definitely_available_values() {
    let program = p(
        3,
        vec![
            i(
                0,
                vec![],
                Control::Branch {
                    condition: r(0),
                    target: 2,
                },
            ),
            i(1, vec![set(1, c(7))], Control::Jump(3)),
            i(2, vec![set(1, c(9))], Control::Jump(3)),
            i(3, vec![], Control::Return(r(1))),
        ],
    );
    for condition in [0, 1, u64::MAX] {
        replay(&program, &[(Reg(1), 0)], &[condition, 11, 13], &[]);
    }
    let missing = p(
        3,
        vec![
            i(
                0,
                vec![],
                Control::Branch {
                    condition: r(0),
                    target: 2,
                },
            ),
            i(1, vec![set(1, c(7))], Control::Jump(3)),
            i(2, vec![], Control::Jump(3)),
            i(3, vec![], Control::Return(r(1))),
        ],
    );
    rejects(&missing, &[(Reg(1), 0)]);
    let clobbered = p(
        3,
        vec![
            i(
                0,
                vec![set(1, c(7))],
                Control::Branch {
                    condition: r(0),
                    target: 2,
                },
            ),
            i(1, vec![], Control::Jump(3)),
            i(2, vec![set(2, c(9))], Control::Jump(3)),
            i(3, vec![], Control::Return(r(1))),
        ],
    );
    rejects(&clobbered, &[(Reg(1), 0), (Reg(2), 0)]);
}

#[test]
fn equal_copy_relations_survive_a_nonentry_loop_started_at_top() {
    let program = p(
        3,
        vec![
            i(0, vec![set(1, c(3)), set(2, r(1))], Control::Jump(1)),
            i(
                1,
                vec![set(0, add(r(0), c(1)))],
                Control::Branch {
                    condition: binary(BinaryOp::Ult, r(0), r(1)),
                    target: 1,
                },
            ),
            i(2, vec![], Control::Return(add(r(1), r(2)))),
        ],
    );
    for start in [0, 1, u64::MAX] {
        replay(&program, &[(Reg(1), 0), (Reg(2), 0)], &[start, 11, 13], &[]);
    }
}

#[test]
fn entry_backedge_cannot_supply_a_definition_for_the_initial_entry() {
    let program = p(
        2,
        vec![
            i(
                0,
                vec![set(0, add(r(0), r(1))), set(1, c(1))],
                Control::Branch {
                    condition: binary(BinaryOp::Ult, r(0), c(3)),
                    target: 0,
                },
            ),
            i(1, vec![], Control::Return(r(0))),
        ],
    );
    rejects(&program, &[(Reg(1), 0)]);
    let defined_first = p(
        2,
        vec![
            i(
                0,
                vec![set(1, c(1)), set(0, add(r(0), r(1)))],
                Control::Branch {
                    condition: binary(BinaryOp::Ult, r(0), c(3)),
                    target: 0,
                },
            ),
            i(1, vec![], Control::Return(r(0))),
        ],
    );
    for start in [0, 1, u64::MAX] {
        replay(&defined_first, &[(Reg(1), 0)], &[start, 11], &[]);
    }
}

#[test]
fn store_addresses_rhs_nested_loads_and_partial_fault_state_match() {
    let program = p(
        4,
        vec![
            i(
                0,
                vec![set(1, c(0x11)), store(c(0), Width::U8, r(1))],
                Control::Next,
            ),
            i(
                1,
                vec![set(2, r(0)), set(3, Expr::load(r(2), Width::U64))],
                Control::Next,
            ),
            i(
                2,
                vec![store(c(1), Width::U8, c(0x22))],
                Control::Return(r(3)),
            ),
        ],
    );
    let mapping = [(Reg(1), 7), (Reg(2), 7), (Reg(3), 7)];
    for pointer in [0, 1, 7, u64::MAX] {
        replay(&program, &mapping, &[pointer, 11, 13, 17], &[0x5a; 8]);
    }
    let source = p(
        3,
        vec![i(
            0,
            vec![
                set(1, r(0)),
                store(r(1), Width::U16, Expr::load(r(2), Width::U8)),
            ],
            Control::Return(c(0)),
        )],
    );
    replay(&source, &[(Reg(1), usize::MAX)], &[100, 11, 200], &[0; 8]);
    replay(&source, &[(Reg(1), usize::MAX)], &[0, 11, 200], &[0; 8]);
    let nested = p(
        3,
        vec![i(
            0,
            vec![
                set(1, c(0)),
                set(2, Expr::load(Expr::load(r(1), Width::U64), Width::U8)),
            ],
            Control::Return(r(2)),
        )],
    );
    let mut memory = [0; 16];
    memory[..8].copy_from_slice(&8u64.to_le_bytes());
    memory[8] = 99;
    replay(&nested, &[(Reg(1), 0), (Reg(2), 0)], &[0, 11, 13], &memory);
}

#[test]
fn store_address_and_rhs_require_all_reads_before_any_slot_overwrite() {
    let program = p(
        3,
        vec![i(
            0,
            vec![set(1, c(0)), set(2, c(7)), store(r(1), Width::U8, r(2))],
            Control::Return(c(0)),
        )],
    );
    rejects(&program, &[(Reg(1), 0), (Reg(2), 0)]);
    let rhs = p(
        3,
        vec![i(
            0,
            vec![set(1, c(7)), set(2, c(0)), store(r(2), Width::U8, r(1))],
            Control::Return(c(0)),
        )],
    );
    rejects(&rhs, &[(Reg(1), 0), (Reg(2), 0)]);
}

#[test]
fn unevaluated_lazy_arms_are_conservatively_checked() {
    let program = p(
        2,
        vec![i(
            0,
            vec![],
            Control::Return(Expr::select(c(1), c(7), r(1))),
        )],
    );
    rejects(&program, &[(Reg(1), 0)]);
    let program = p(
        3,
        vec![i(
            0,
            vec![set(1, c(7)), set(2, c(9))],
            Control::Return(Expr::select(c(1), r(2), r(1))),
        )],
    );
    rejects(&program, &[(Reg(1), 0), (Reg(2), 0)]);
    let valid = p(
        2,
        vec![i(
            0,
            vec![set(1, r(0))],
            Control::Return(Expr::select(r(1), c(7), Expr::load(r(1), Width::U64))),
        )],
    );
    for value in [0, 1, u64::MAX] {
        replay(&valid, &[(Reg(1), 0)], &[value, 11], &[0x5a; 8]);
    }
}

#[test]
fn sparse_register_ids_and_color_labels_never_require_max_label_allocation() {
    let program = p(
        1_000_000,
        vec![i(0, vec![set(999_999, c(7))], Control::Return(r(999_999)))],
    );
    let evidence = validate(&program, &[(Reg(999_999), usize::MAX)]).unwrap();
    assert_eq!(
        (
            evidence.blocks,
            evidence.register_reads,
            evidence.mapped_registers
        ),
        (1, 1, 1)
    );
    assert!(validate(&program, &[]).is_ok());
}

#[test]
fn malformed_maps_are_distinct_from_unavailable_or_read_correspondence() {
    let program = p(2, vec![i(0, vec![], Control::Return(c(7)))]);
    for mapping in [
        vec![(Reg(1), 0), (Reg(1), 0)],
        vec![(Reg(1), 0), (Reg(1), 1)],
        vec![(Reg(2), 0)],
        vec![(Reg(usize::MAX), 0)],
    ] {
        let error = validate(&program, &mapping).unwrap_err();
        assert!(matches!(error, AllocationError::Malformed { .. }));
        assert!(!error.is_resource_limit());
    }
}

#[test]
fn unreachable_reads_do_not_need_facts_but_the_whole_tree_is_bounded() {
    let program = p(
        2,
        vec![
            i(0, vec![], Control::Return(c(7))),
            i(10, vec![], Control::Return(r(1))),
        ],
    );
    let evidence = validate(&program, &[(Reg(1), 0)]).unwrap();
    assert_eq!(evidence.register_reads, 0);
    let mut deep = c(0);
    for _ in 0..MAX_EXPRESSION_DEPTH {
        deep = add(deep, c(0));
    }
    let deep_program = p(
        2,
        vec![
            i(0, vec![], Control::Return(c(7))),
            i(
                10,
                vec![store(deep, Width::U8, c(1))],
                Control::Return(c(0)),
            ),
        ],
    );
    assert!(
        validate(&deep_program, &[(Reg(1), 0)])
            .unwrap_err()
            .is_resource_limit()
    );
    let huge = p(
        MAX_MAPPED_REGISTERS + 1,
        vec![i(0, vec![], Control::Return(c(7)))],
    );
    let mapping: Vec<_> = (0..=MAX_MAPPED_REGISTERS)
        .map(|reg| (Reg(reg), usize::MAX))
        .collect();
    assert!(validate(&huge, &mapping).unwrap_err().is_resource_limit());
}

#[test]
fn state_and_work_limits_return_unavailable_without_partial_evidence() {
    let mut instructions = Vec::new();
    for address in 0..511 {
        instructions.push(i(address, vec![], Control::Jump(address + 1)));
    }
    instructions.push(i(511, vec![], Control::Return(c(7))));
    let program = p(1024, instructions);
    let mapping: Vec<_> = (0..1024).map(|reg| (Reg(reg), reg)).collect();
    assert!(matches!(
        validate(&program, &mapping),
        Err(AllocationError::Unavailable {
            resource: "state cells"
        })
    ));
    let program = p(
        MAX_MAPPED_REGISTERS,
        vec![i(0, vec![set(0, c(7)); 1000], Control::Return(c(0)))],
    );
    let mapping: Vec<_> = (0..MAX_MAPPED_REGISTERS)
        .map(|reg| (Reg(reg), usize::MAX))
        .collect();
    assert!(matches!(
        validate(&program, &mapping),
        Err(AllocationError::Unavailable { resource: "work" })
    ));
}

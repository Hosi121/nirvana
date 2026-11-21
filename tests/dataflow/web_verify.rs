use nirvana::ir::{
    Assignment, BinaryOp, Control, Expr, IrInstruction, Place, Program, Reg, RunStatus, Width,
};
use nirvana::web_verify::{MAX_ACTIVE_REGISTERS, MAX_DEPTH, MAX_PAIRS, WebError, validate};

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

// Candidates here are hand-written, independent of the separate web builder.
// Fresh registers start with different arbitrary poison values on every run.
// The intentionally unobserved final register files may differ after renaming.
fn replay(original: &Program, candidate: &Program, input: &[u64], memory: &[u8]) {
    validate(original, candidate).unwrap();
    for poison in [0, 0xdead_beef_1234_5678, u64::MAX] {
        let mut fresh = input.to_vec();
        fresh.extend(
            (input.len()..candidate.register_count())
                .map(|index| poison ^ (index as u64).wrapping_mul(0x9e37_79b9)),
        );
        for limit in 0..40 {
            let expected = original.run_with_memory(input, 0, memory, limit).unwrap();
            let actual = candidate.run_with_memory(&fresh, 0, memory, limit).unwrap();
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
fn rejects_read(original: &Program, candidate: &Program) -> WebError {
    let error = validate(original, candidate).unwrap_err();
    assert!(
        matches!(error, WebError::Correspondence { .. }),
        "{error:?}"
    );
    assert!(!error.is_resource_limit());
    error
}

#[test]
fn fresh_sequential_definitions_certify_without_observing_old_register_storage() {
    let original = p(
        3,
        vec![i(
            0,
            vec![
                set(1, r(0)),
                set(1, add(r(1), r(2))),
                set(1, c(9)),
                set(1, binary(BinaryOp::Mul, r(1), r(2))),
            ],
            Control::Return(r(1)),
        )],
    );
    let candidate = p(
        7,
        vec![i(
            0,
            vec![
                set(3, r(0)),
                set(4, add(r(3), r(2))),
                set(5, c(9)),
                set(6, binary(BinaryOp::Mul, r(5), r(2))),
            ],
            Control::Return(r(6)),
        )],
    );
    let evidence = validate(&original, &candidate).unwrap();
    assert_eq!(evidence.instructions, 1);
    assert_eq!(evidence.assignments, 4);
    assert_eq!(evidence.register_reads, 6);
    assert_eq!(evidence.blocks, 1);
    assert_eq!(evidence.relation_pairs, 6);
    for value in [0, 1, 255, 1 << 63, u64::MAX] {
        replay(&original, &candidate, &[value, 77, value], &[0; 8]);
    }
    let old = original.execute(&[2, 77, 3], 1).unwrap();
    let new = candidate
        .execute(&[2, 77, 3, 101, 102, 103, 104], 1)
        .unwrap();
    assert_ne!(old.registers[1], new.registers[1]);
}

#[test]
fn arbitrary_fresh_inputs_and_wrong_original_registers_are_not_assumed_equal() {
    let original = p(2, vec![i(0, vec![], Control::Return(r(0)))]);
    for wrong in [1, 2] {
        let candidate = p(3, vec![i(0, vec![], Control::Return(r(wrong)))]);
        assert!(
            matches!(rejects_read(&original, &candidate), WebError::Correspondence { original: Reg(0), renamed: Reg(reg), assignment: None, .. } if reg == wrong)
        );
    }
}

#[test]
fn reads_are_checked_before_the_write_that_could_generate_their_relation() {
    let original = p(
        1,
        vec![i(0, vec![set(0, add(r(0), c(1)))], Control::Return(r(0)))],
    );
    let bad = p(
        2,
        vec![i(0, vec![set(1, add(r(1), c(1)))], Control::Return(r(1)))],
    );
    assert!(matches!(
        rejects_read(&original, &bad),
        WebError::Correspondence {
            assignment: Some(0),
            ..
        }
    ));
    let valid = p(
        2,
        vec![i(0, vec![set(1, add(r(0), c(1)))], Control::Return(r(1)))],
    );
    replay(&original, &valid, &[u64::MAX], &[]);
}

#[test]
fn candidate_writes_cannot_clobber_a_future_original_input() {
    let original = p(2, vec![i(0, vec![set(0, c(7))], Control::Return(r(1)))]);
    let bad = p(2, vec![i(0, vec![set(1, c(7))], Control::Return(r(1)))]);
    rejects_read(&original, &bad);
    let valid = p(3, vec![i(0, vec![set(2, c(7))], Control::Return(r(1)))]);
    replay(&original, &valid, &[11, 13], &[]);
}

#[test]
fn source_overwrites_kill_previous_pairs_even_when_candidate_storage_survives() {
    let original = p(
        2,
        vec![i(
            0,
            vec![set(0, c(7)), set(0, c(9))],
            Control::Return(r(0)),
        )],
    );
    let bad = p(
        4,
        vec![i(
            0,
            vec![set(2, c(7)), set(3, c(9))],
            Control::Return(r(2)),
        )],
    );
    rejects_read(&original, &bad);
    let valid = p(
        4,
        vec![i(
            0,
            vec![set(2, c(7)), set(3, c(9))],
            Control::Return(r(3)),
        )],
    );
    replay(&original, &valid, &[11, 13], &[]);
}

#[test]
fn diamond_correspondence_is_intersection_of_both_incoming_paths() {
    let original = p(
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
    let candidate = p(
        4,
        vec![
            i(
                0,
                vec![],
                Control::Branch {
                    condition: r(0),
                    target: 2,
                },
            ),
            i(1, vec![set(3, c(7))], Control::Jump(3)),
            i(2, vec![set(3, c(9))], Control::Jump(3)),
            i(3, vec![], Control::Return(r(3))),
        ],
    );
    for condition in [0, 1, u64::MAX] {
        replay(&original, &candidate, &[condition, 11, 13], &[]);
    }
    let mut bad = candidate.instructions().to_vec();
    bad[2].assignments[0].destination = Reg(2).into();
    rejects_read(&original, &p(4, bad));
}

#[test]
fn nonentry_loops_start_at_top_and_preserve_unwritten_relations() {
    let original = p(
        2,
        vec![
            i(0, vec![set(1, c(3))], Control::Jump(1)),
            i(
                1,
                vec![set(0, add(r(0), c(1)))],
                Control::Branch {
                    condition: binary(BinaryOp::Ult, r(0), r(1)),
                    target: 1,
                },
            ),
            i(2, vec![], Control::Return(r(1))),
        ],
    );
    let candidate = p(
        3,
        vec![
            i(0, vec![set(2, c(3))], Control::Jump(1)),
            i(
                1,
                vec![set(0, add(r(0), c(1)))],
                Control::Branch {
                    condition: binary(BinaryOp::Ult, r(0), r(2)),
                    target: 1,
                },
            ),
            i(2, vec![], Control::Return(r(2))),
        ],
    );
    for start in [0, 1, u64::MAX] {
        replay(&original, &candidate, &[start, 77], &[]);
    }
}

#[test]
fn entry_backedges_intersect_the_original_initial_seed_on_every_visit() {
    let original = p(
        1,
        vec![
            i(
                0,
                vec![set(0, add(r(0), c(1)))],
                Control::Branch {
                    condition: binary(BinaryOp::Ult, r(0), c(3)),
                    target: 0,
                },
            ),
            i(1, vec![], Control::Return(r(0))),
        ],
    );
    // Without entry seed intersection this loop can bootstrap a false (0,1)
    // relation entirely from its own backedge, assuming fresh poison is input.
    let bad = p(
        2,
        vec![
            i(
                0,
                vec![set(1, add(r(1), c(1)))],
                Control::Branch {
                    condition: binary(BinaryOp::Ult, r(1), c(3)),
                    target: 0,
                },
            ),
            i(1, vec![], Control::Return(r(1))),
        ],
    );
    rejects_read(&original, &bad);
    // This version is right on its first iteration but loses input storage on
    // later visits. The backedge must constrain a diagonal pair too.
    let mut first_only = bad.instructions().to_vec();
    first_only[0].assignments[0].value = add(r(0), c(1));
    rejects_read(&original, &p(2, first_only));
}

#[test]
fn entry_loop_can_define_a_fresh_value_before_its_first_read_each_iteration() {
    let original = p(
        2,
        vec![
            i(
                0,
                vec![set(1, c(7)), set(0, add(r(0), c(1)))],
                Control::Branch {
                    condition: binary(BinaryOp::Ult, r(0), c(3)),
                    target: 0,
                },
            ),
            i(1, vec![], Control::Return(r(1))),
        ],
    );
    let candidate = p(
        3,
        vec![
            i(
                0,
                vec![set(2, c(7)), set(0, add(r(0), c(1)))],
                Control::Branch {
                    condition: binary(BinaryOp::Ult, r(0), c(3)),
                    target: 0,
                },
            ),
            i(1, vec![], Control::Return(r(2))),
        ],
    );
    for input in [0, 1, u64::MAX] {
        replay(&original, &candidate, &[input, 17], &[]);
    }
}

#[test]
fn partial_memory_and_first_load_store_faults_match_with_poisoned_fresh_bank() {
    let original = p(
        3,
        vec![
            i(
                0,
                vec![set(1, c(0x11)), store(c(0), Width::U8, r(1))],
                Control::Next,
            ),
            i(1, vec![set(1, Expr::load(r(0), Width::U64))], Control::Next),
            i(
                2,
                vec![store(c(1), Width::U8, c(0x22))],
                Control::Return(r(1)),
            ),
        ],
    );
    let candidate = p(
        5,
        vec![
            i(
                0,
                vec![set(3, c(0x11)), store(c(0), Width::U8, r(3))],
                Control::Next,
            ),
            i(1, vec![set(4, Expr::load(r(0), Width::U64))], Control::Next),
            i(
                2,
                vec![store(c(1), Width::U8, c(0x22))],
                Control::Return(r(4)),
            ),
        ],
    );
    for address in [0, 1, 7, u64::MAX] {
        replay(&original, &candidate, &[address, 77, 99], &[0x5a; 8]);
    }
    let report = original
        .run_with_memory(&[7, 77, 99], 0, &[0; 8], 4)
        .unwrap();
    assert!(matches!(report.status, RunStatus::Fault(_)));
    assert_eq!(report.state.memory[0], 0x11);
    let original = p(
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
    let candidate = p(
        4,
        vec![i(
            0,
            vec![
                set(3, r(0)),
                store(r(3), Width::U16, Expr::load(r(2), Width::U8)),
            ],
            Control::Return(c(0)),
        )],
    );
    replay(&original, &candidate, &[100, 77, 200], &[0; 8]);
    replay(&original, &candidate, &[0, 77, 200], &[0; 8]);
}

#[test]
fn lazy_arms_are_conservative_read_obligations_without_erasing_memory_order() {
    let original = p(
        1,
        vec![i(
            0,
            vec![],
            Control::Return(Expr::select(c(1), c(7), r(0))),
        )],
    );
    let candidate = p(
        2,
        vec![i(
            0,
            vec![],
            Control::Return(Expr::select(c(1), c(7), r(1))),
        )],
    );
    rejects_read(&original, &candidate);
    let original = p(
        2,
        vec![i(
            0,
            vec![set(1, r(0))],
            Control::Return(Expr::select(r(1), c(7), Expr::load(r(1), Width::U64))),
        )],
    );
    let candidate = p(
        3,
        vec![i(
            0,
            vec![set(2, r(0))],
            Control::Return(Expr::select(r(2), c(7), Expr::load(r(2), Width::U64))),
        )],
    );
    for input in [0, 1, u64::MAX] {
        replay(&original, &candidate, &[input, 77], &[0x5a; 8]);
    }
}

#[test]
fn unreachable_instructions_remain_exact_even_if_their_renaming_would_be_valid() {
    let original = p(
        2,
        vec![
            i(0, vec![], Control::Return(r(0))),
            i(10, vec![set(1, c(7))], Control::Return(r(1))),
        ],
    );
    let exact = p(3, original.instructions().to_vec());
    let evidence = validate(&original, &exact).unwrap();
    assert_eq!(
        (evidence.instructions, evidence.assignments, evidence.blocks),
        (2, 1, 1)
    );
    let mut changed = exact.instructions().to_vec();
    changed[1].assignments[0].destination = Reg(2).into();
    assert!(matches!(
        validate(&original, &p(3, changed)),
        Err(WebError::UnreachableChanged { instruction: 10 })
    ));
}

#[test]
fn all_nonregister_syntax_widths_targets_layout_and_counts_are_checked() {
    let original = p(
        2,
        vec![i(0, vec![set(1, add(r(0), c(1)))], Control::Return(r(1)))],
    );
    for value in [
        add(r(0), c(2)),
        binary(BinaryOp::Sub, r(0), c(1)),
        Expr::load(r(0), Width::U8),
    ] {
        let candidate = p(2, vec![i(0, vec![set(1, value)], Control::Return(r(1)))]);
        assert!(matches!(
            validate(&original, &candidate),
            Err(WebError::Shape { .. })
        ));
    }
    let original = p(
        2,
        vec![i(
            0,
            vec![
                store(r(0), Width::U8, c(1)),
                set(1, Expr::load(r(0), Width::U8)),
            ],
            Control::Return(r(1)),
        )],
    );
    for change_store in [false, true] {
        let mut changed = original.instructions().to_vec();
        if change_store {
            changed[0].assignments[0] = store(r(0), Width::U16, c(1));
        } else {
            changed[0].assignments[1].value = Expr::load(r(0), Width::U16);
        }
        assert!(matches!(
            validate(&original, &p(2, changed)),
            Err(WebError::Shape { .. })
        ));
    }
    let original = p(
        1,
        vec![
            i(
                0,
                vec![],
                Control::Branch {
                    condition: r(0),
                    target: 2,
                },
            ),
            i(1, vec![], Control::Return(c(7))),
            i(2, vec![], Control::Return(c(8))),
        ],
    );
    let mut changed = original.instructions().to_vec();
    changed[0].control = Control::Branch {
        condition: r(0),
        target: 1,
    };
    assert!(matches!(
        validate(&original, &p(1, changed)),
        Err(WebError::Shape { .. })
    ));
    let original = p(
        1,
        vec![
            i(0, vec![], Control::Jump(10)),
            i(10, vec![], Control::Return(c(7))),
        ],
    );
    let mut changed = original.instructions().to_vec();
    changed[0].size = 2;
    assert!(matches!(
        validate(&original, &p(1, changed)),
        Err(WebError::Shape { .. })
    ));
    let changed = Program::new(10, 1, original.instructions().to_vec()).unwrap();
    assert!(matches!(
        validate(&original, &changed),
        Err(WebError::Shape { .. })
    ));
    let original = p(2, vec![i(0, vec![], Control::Return(c(7)))]);
    assert!(matches!(
        validate(&original, &p(1, original.instructions().to_vec())),
        Err(WebError::Shape { .. })
    ));
}

#[test]
fn sparse_huge_register_indices_do_not_allocate_a_register_count_sized_domain() {
    let original = p(1_000_000, vec![i(0, vec![], Control::Return(r(999_999)))]);
    let candidate = p(2_000_000, original.instructions().to_vec());
    assert_eq!(validate(&original, &candidate).unwrap().relation_pairs, 1);
}

#[test]
fn store_address_and_rhs_reads_use_current_sequential_correspondence() {
    let original = p(
        2,
        vec![i(
            0,
            vec![store(r(0), Width::U8, r(1))],
            Control::Return(c(0)),
        )],
    );
    let wrong_address = p(
        3,
        vec![i(
            0,
            vec![store(r(2), Width::U8, r(1))],
            Control::Return(c(0)),
        )],
    );
    let wrong_rhs = p(
        3,
        vec![i(
            0,
            vec![store(r(0), Width::U8, r(2))],
            Control::Return(c(0)),
        )],
    );
    for candidate in [&wrong_address, &wrong_rhs] {
        assert!(matches!(
            rejects_read(&original, candidate),
            WebError::Correspondence {
                assignment: Some(0),
                ..
            }
        ));
    }
}

#[test]
fn relation_state_cell_limit_precedes_top_state_allocation() {
    let mut old = vec![i(
        0,
        (0..1024).map(|index| set(index % 32, c(0))).collect(),
        Control::Jump(1),
    )];
    let mut new = vec![i(
        0,
        (0..1024).map(|index| set(index / 32, c(0))).collect(),
        Control::Jump(1),
    )];
    for address in 1..511 {
        old.push(i(address, vec![], Control::Jump(address + 1)));
        new.push(i(address, vec![], Control::Jump(address + 1)));
    }
    old.push(i(511, vec![], Control::Return(c(0))));
    new.push(i(511, vec![], Control::Return(c(0))));
    assert!(matches!(
        validate(&p(32, old), &p(32, new)),
        Err(WebError::Unavailable {
            resource: "relation state cells"
        })
    ));
}

#[test]
fn unreachable_memory_destination_depth_is_checked_before_structural_equality() {
    let mut deep_address = c(0);
    for _ in 0..MAX_DEPTH {
        deep_address = add(deep_address, c(1));
    }
    let original = p(
        1,
        vec![
            i(0, vec![], Control::Return(c(7))),
            i(
                10,
                vec![store(c(0), Width::U8, c(1))],
                Control::Return(c(0)),
            ),
        ],
    );
    let candidate = p(
        1,
        vec![
            i(0, vec![], Control::Return(c(7))),
            i(
                10,
                vec![store(deep_address, Width::U8, c(1))],
                Control::Return(c(0)),
            ),
        ],
    );
    assert!(
        validate(&original, &candidate)
            .unwrap_err()
            .is_resource_limit()
    );
}

#[test]
fn whole_input_and_relation_limits_are_unavailable_not_invalid_renaming() {
    let original = p(
        1,
        vec![
            i(0, vec![], Control::Return(c(7))),
            i(10, vec![], Control::Return(c(0))),
        ],
    );
    let mut deep = c(0);
    for _ in 0..MAX_DEPTH {
        deep = add(deep, c(1));
    }
    let candidate = p(
        1,
        vec![
            i(0, vec![], Control::Return(c(7))),
            i(10, vec![], Control::Return(deep)),
        ],
    );
    assert!(
        validate(&original, &candidate)
            .unwrap_err()
            .is_resource_limit()
    );
    let original = p(
        MAX_ACTIVE_REGISTERS + 1,
        vec![i(
            0,
            (0..=MAX_ACTIVE_REGISTERS)
                .map(|index| set(index, c(0)))
                .collect(),
            Control::Return(c(0)),
        )],
    );
    assert!(
        validate(&original, &original)
            .unwrap_err()
            .is_resource_limit()
    );
    let old_assignments = (0..=MAX_PAIRS)
        .map(|index| set(index % 128, c(0)))
        .collect();
    let new_assignments = (0..=MAX_PAIRS)
        .map(|index| set(index / 128, c(0)))
        .collect();
    let original = p(128, vec![i(0, old_assignments, Control::Return(c(0)))]);
    let candidate = p(128, vec![i(0, new_assignments, Control::Return(c(0)))]);
    assert!(matches!(
        validate(&original, &candidate),
        Err(WebError::Unavailable { resource: "pairs" })
    ));
}

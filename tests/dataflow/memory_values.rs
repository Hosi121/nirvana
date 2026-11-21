use crate::support::ir::{c, r};
use nirvana::ir::{Assignment, Control, Expr, IrInstruction, Place, Program, Reg, Width};
use nirvana::memory_values::{self, MemoryValuePlan};
fn ins(address: u64, assignments: Vec<Assignment>, control: Control) -> IrInstruction {
    IrInstruction {
        address,
        size: 1,
        assignments,
        control,
    }
}
fn set(n: usize, value: Expr) -> Assignment {
    Assignment {
        destination: Reg(n).into(),
        value,
    }
}
fn store(value: Expr) -> Assignment {
    Assignment {
        destination: Place::Memory {
            address: r(7),
            width: Width::U64,
        },
        value,
    }
}
fn b(op: nirvana::ir::BinaryOp, a: Expr, z: Expr) -> Expr {
    Expr::binary(op, a, z)
}
fn compare(source: &Program, candidate: &Program) -> usize {
    compare_at(source, candidate, 7)
}
fn compare_at(source: &Program, candidate: &Program, pointer_register: usize) -> usize {
    let mut count = 0;
    for value in [0, 1, 2, 3, 127, 128, 255, 256, 1 << 31, 1 << 63, u64::MAX] {
        for branch in [0, 1] {
            for pointer in [4096, 4097, 4104, 4112, 4120, 4127, u64::MAX] {
                let mut initial = vec![0x7890_cafe_1234_5678; source.register_count()];
                initial[0] = value;
                initial[1] = branch;
                initial[pointer_register] = pointer;
                let mut extended = initial.clone();
                extended.resize(candidate.register_count(), 0xdead_beef_1234_5678);
                for memory in [[0; 64], [0xa5; 64]] {
                    for limit in [0, 1, 2, 3, 4, 8, 16, 32] {
                        let expected = source
                            .run_with_memory(&initial, 4096, &memory, limit)
                            .unwrap();
                        let mut actual = candidate
                            .run_with_memory(&extended, 4096, &memory, limit)
                            .unwrap();
                        actual.state.registers.truncate(source.register_count());
                        assert_eq!(actual, expected, "{value}/{branch}/{pointer}/{limit}");
                        count += 1;
                    }
                }
            }
        }
    }
    count
}
fn source(width: Width) -> Program {
    Program::new(
        0,
        4,
        vec![IrInstruction {
            address: 0,
            size: 1,
            assignments: vec![
                Assignment {
                    destination: Place::Memory {
                        address: r(3),
                        width,
                    },
                    value: r(0),
                },
                Assignment {
                    destination: Reg(0).into(),
                    value: c(0),
                },
                Assignment {
                    destination: Reg(1).into(),
                    value: Expr::load(r(3), width),
                },
            ],
            control: Control::Return(r(1)),
        }],
    )
    .unwrap()
}
#[test]
fn exact_reload_uses_captured_input_word_after_register_overwrite_and_keeps_effects() {
    for width in [Width::U8, Width::U16, Width::U32, Width::U64] {
        let source = source(width);
        let plan = MemoryValuePlan::analyze(&source).expect("exact stable input has a value proof");
        let candidate = plan.lower(&source).unwrap();
        assert_eq!(
            memory_values::validate(&source, &plan, &candidate).unwrap(),
            plan.evidence()
        );
        assert_eq!(plan.evidence().snapshot_values, 1);
        assert_eq!(plan.evidence().proved_loads, 1);
        assert_eq!(plan.evidence().replaced_reads, 1);
        for value in [
            0,
            1,
            127,
            128,
            255,
            256,
            65535,
            65536,
            1 << 31,
            1 << 32,
            1 << 63,
            u64::MAX,
        ] {
            for pointer in [4096, 4097, 4104, 4112, 4120, 4127, u64::MAX] {
                let initial = [value, 0x7890, 0x9234, pointer];
                let mut extended = initial.to_vec();
                extended.push(0xdead_beef_1234_5678);
                for limit in [0, 1, 2] {
                    let expected = source
                        .run_with_memory(&initial, 4096, &[0xa5; 32], limit)
                        .unwrap();
                    let mut actual = candidate
                        .run_with_memory(&extended, 4096, &[0xa5; 32], limit)
                        .unwrap();
                    if limit > 0 {
                        assert_eq!(
                            actual.state.registers[source.register_count()],
                            value,
                            "full source bits stay in the snapshot"
                        );
                    }
                    actual.state.registers.truncate(source.register_count());
                    assert_eq!(actual, expected, "{width:?}/{value}/{pointer}/{limit}");
                }
            }
        }
        let mut changed = candidate.instructions().to_vec();
        let load = changed[0]
            .assignments
            .iter_mut()
            .find(|a| matches!(a.value, Expr::Load { .. }))
            .unwrap();
        load.value = c(0);
        assert!(
            memory_values::validate(
                &source,
                &plan,
                &Program::new(0, candidate.register_count(), changed).unwrap()
            )
            .is_err()
        );
        let mut changed = source.instructions().to_vec();
        changed[0].assignments[0].destination = Place::Memory {
            address: Expr::binary(nirvana::ir::BinaryOp::Add, r(3), c(8)),
            width,
        };
        let changed = Program::new(0, 4, changed).unwrap();
        assert!(plan.lower(&changed).is_none());
    }
}

#[test]
fn stable_input_identity_crosses_memory_phis_clobbers_and_loop_reloads() {
    use nirvana::ir::BinaryOp as B;
    let diamond = vec![
        ins(
            0,
            vec![],
            Control::Branch {
                condition: r(1),
                target: 2,
            },
        ),
        ins(1, vec![store(r(0)), set(0, c(0))], Control::Jump(3)),
        ins(2, vec![store(r(0)), set(0, c(0))], Control::Jump(3)),
        ins(
            3,
            vec![set(2, Expr::load(r(7), Width::U64))],
            Control::Return(r(2)),
        ),
    ];
    let looped = vec![
        ins(
            0,
            vec![
                set(6, r(0)),
                set(3, b(B::And, r(0), c(3))),
                store(r(6)),
                set(0, c(0)),
            ],
            Control::Jump(1),
        ),
        ins(
            1,
            vec![set(2, Expr::load(r(7), Width::U64))],
            Control::Branch {
                condition: r(3),
                target: 3,
            },
        ),
        ins(2, vec![], Control::Return(r(2))),
        ins(
            3,
            vec![store(r(6)), set(3, b(B::Sub, r(3), c(1)))],
            Control::Jump(1),
        ),
    ];
    let mut comparisons = 0;
    for instructions in [diamond, looped] {
        let source = Program::new(0, 8, instructions).unwrap();
        let plan = MemoryValuePlan::analyze(&source).unwrap();
        assert_eq!(plan.evidence().proved_loads, 1);
        assert_eq!(plan.evidence().snapshot_values, 1);
        let candidate = plan.lower(&source).unwrap();
        comparisons += compare(&source, &candidate);
    }
    let phi = Program::new(
        0,
        8,
        vec![
            ins(
                0,
                vec![],
                Control::Branch {
                    condition: r(1),
                    target: 2,
                },
            ),
            ins(1, vec![set(6, b(B::Add, r(0), c(1)))], Control::Jump(3)),
            ins(
                2,
                vec![set(6, b(B::Xor, r(0), c(u64::MAX)))],
                Control::Jump(3),
            ),
            ins(
                3,
                vec![
                    store(r(6)),
                    set(6, c(0)),
                    set(2, Expr::load(r(7), Width::U64)),
                ],
                Control::Return(r(2)),
            ),
        ],
    )
    .unwrap();
    let plan = MemoryValuePlan::analyze(&phi).unwrap();
    comparisons += compare(&phi, &plan.lower(&phi).unwrap());
    println!(
        "{comparisons} stable input memory-phi/loop full-register-prefix/RAM/PC/budget observations"
    );
}

#[test]
fn cyclic_producers_decline_and_pure_wrappers_capture_their_actual_value() {
    use nirvana::ir::{BinaryOp as B, UnaryOp as U};
    let changing = Program::new(
        0,
        8,
        vec![
            ins(0, vec![set(3, c(3))], Control::Jump(1)),
            ins(
                1,
                vec![
                    store(r(3)),
                    set(3, b(B::Sub, r(3), c(1))),
                    set(2, Expr::load(r(7), Width::U64)),
                ],
                Control::Branch {
                    condition: r(3),
                    target: 1,
                },
            ),
            ins(2, vec![], Control::Return(r(2))),
        ],
    )
    .unwrap();
    assert!(MemoryValuePlan::analyze(&changing).is_none());
    let mut entry = source(Width::U64).instructions().to_vec();
    entry[0].control = Control::Branch {
        condition: r(2),
        target: 0,
    };
    entry.push(ins(1, vec![], Control::Return(r(1))));
    assert!(MemoryValuePlan::analyze(&Program::new(0, 4, entry).unwrap()).is_none());
    for value in [
        b(B::And, r(0), c(0xfffe)),
        Expr::unary(U::SignExtend(Width::U8), r(0)),
        Expr::unary(
            U::Extract {
                start: 0,
                width: Width::U8,
            },
            r(0),
        ),
    ] {
        let source = source(Width::U16);
        let old = MemoryValuePlan::analyze(&source).unwrap();
        let mut changed = source.instructions().to_vec();
        changed[0].assignments[0].value = value;
        let changed = Program::new(0, 4, changed).unwrap();
        assert!(old.lower(&changed).is_none());
        let plan = MemoryValuePlan::analyze(&changed).expect("capture the changed pure expression");
        assert_eq!(plan.evidence().snapshot_values, 1);
        compare_at(&changed, &plan.lower(&changed).unwrap(), 3);
    }
}

#[test]
fn changed_shift_gets_a_fresh_projection_and_rejects_the_old_word_claim() {
    use nirvana::ir::BinaryOp as B;
    let source = source(Width::U16);
    let old = MemoryValuePlan::analyze(&source).unwrap();
    let mut rows = source.instructions().to_vec();
    rows[0].assignments[0].value = b(B::Shr, r(0), c(8));
    let shifted = Program::new(0, 4, rows).unwrap();
    assert!(old.lower(&shifted).is_none());
    let plan = MemoryValuePlan::analyze(&shifted).unwrap();
    let lowered = plan.lower(&shifted).unwrap();
    println!(
        "{} shifted-word full-state observations",
        compare_at(&shifted, &lowered, 3)
    );
}
#[test]
fn every_contained_width_offset_projects_the_saved_word_and_keeps_load_faults() {
    let widths = [Width::U8, Width::U16, Width::U32, Width::U64];
    let mut cases = 0;
    let mut checked = 0;
    for write in widths {
        for read in widths {
            for offset in 0..=8usize {
                let source = Program::new(
                    0,
                    8,
                    vec![
                        ins(
                            0,
                            vec![
                                Assignment {
                                    destination: Place::Memory {
                                        address: r(7),
                                        width: write,
                                    },
                                    value: r(0),
                                },
                                set(0, c(0)),
                            ],
                            Control::Next,
                        ),
                        ins(
                            1,
                            vec![set(
                                2,
                                Expr::load(
                                    b(nirvana::ir::BinaryOp::Add, r(7), c(offset as u64)),
                                    read,
                                ),
                            )],
                            Control::Return(r(2)),
                        ),
                    ],
                )
                .unwrap();
                if offset + read.bytes() > write.bytes() {
                    assert!(MemoryValuePlan::analyze(&source).is_none());
                    continue;
                }
                let plan = MemoryValuePlan::analyze(&source)
                    .expect("every observed byte has a stable origin");
                let candidate = plan.lower(&source).unwrap();
                assert!(memory_values::validate(&source, &plan, &candidate).is_ok());
                checked += compare(&source, &candidate);
                cases += 1;
                for value in [0u64, 0x1234_5678_9abc_def0, 1 << 63, u64::MAX] {
                    let mut expected = [0; 8];
                    expected[..read.bytes()]
                        .copy_from_slice(&value.to_le_bytes()[offset..offset + read.bytes()]);
                    let mut regs = vec![0; candidate.register_count()];
                    regs[0] = value;
                    regs[7] = 4096;
                    assert_eq!(
                        candidate
                            .execute_with_memory(&regs, 4096, &[0xa5; 32], 3)
                            .unwrap()
                            .value,
                        u64::from_le_bytes(expected)
                    );
                }
            }
        }
    }
    println!(
        "{cases} contained word/byte slices, {checked} full-prefix/RAM/PC/fault/budget observations"
    );
}
#[test]
fn split_stores_and_phi_widths_reassemble_one_original_value() {
    use nirvana::ir::{BinaryOp as B, UnaryOp as U};
    let at = |offset| b(B::Add, r(7), c(offset));
    let store = |offset, width, value| Assignment {
        destination: Place::Memory {
            address: at(offset),
            width,
        },
        value,
    };
    let split = vec![
        ins(
            0,
            vec![store(
                0,
                Width::U16,
                Expr::unary(
                    U::Extract {
                        start: 0,
                        width: Width::U16,
                    },
                    r(0),
                ),
            )],
            Control::Next,
        ),
        ins(
            1,
            vec![
                store(
                    2,
                    Width::U16,
                    Expr::unary(
                        U::Extract {
                            start: 16,
                            width: Width::U16,
                        },
                        r(0),
                    ),
                ),
                set(0, c(0)),
            ],
            Control::Next,
        ),
        ins(
            2,
            vec![set(2, Expr::load(r(7), Width::U32))],
            Control::Return(r(2)),
        ),
    ];
    let phi = vec![
        ins(
            0,
            vec![],
            Control::Branch {
                condition: r(1),
                target: 2,
            },
        ),
        ins(
            1,
            vec![store(0, Width::U32, r(0)), set(0, c(0))],
            Control::Jump(3),
        ),
        ins(
            2,
            vec![store(0, Width::U64, r(0)), set(0, c(0))],
            Control::Jump(3),
        ),
        ins(
            3,
            vec![set(2, Expr::load(at(1), Width::U16))],
            Control::Return(r(2)),
        ),
    ];
    let mut checked = 0;
    for rows in [split, phi] {
        let source = Program::new(0, 8, rows).unwrap();
        let plan = MemoryValuePlan::analyze(&source).unwrap();
        let candidate = plan.lower(&source).unwrap();
        checked += compare(&source, &candidate);
        let mut stale = source.instructions().to_vec();
        let assignment = stale
            .iter_mut()
            .flat_map(|i| &mut i.assignments)
            .find(|a| matches!(a.destination, Place::Memory { .. }))
            .unwrap();
        assignment.value = r(6);
        let stale = Program::new(0, 8, stale).unwrap();
        assert!(plan.lower(&stale).is_none());
    }
    println!("{checked} split-store and unequal-width phi projection observations");
}

#[test]
fn may_alias_byte_writers_keep_one_value_and_different_values_decline() {
    use nirvana::ir::BinaryOp as B;
    let q = b(B::Add, r(7), b(B::Mul, b(B::And, r(1), c(3)), c(8)));
    let rows = vec![
        ins(
            0,
            vec![Assignment {
                destination: Place::Memory {
                    address: r(7),
                    width: Width::U8,
                },
                value: r(0),
            }],
            Control::Next,
        ),
        ins(
            1,
            vec![
                Assignment {
                    destination: Place::Memory {
                        address: q,
                        width: Width::U8,
                    },
                    value: r(0),
                },
                set(0, c(0)),
            ],
            Control::Next,
        ),
        ins(
            2,
            vec![set(2, Expr::load(r(7), Width::U8))],
            Control::Return(r(2)),
        ),
    ];
    let source = Program::new(0, 8, rows.clone()).unwrap();
    let plan = MemoryValuePlan::analyze(&source).unwrap();
    let candidate = plan.lower(&source).unwrap();
    println!(
        "{} may-alias byte-identity observations",
        compare(&source, &candidate)
    );
    let mut other = rows;
    other[1].assignments[0].value = r(6);
    let other = Program::new(0, 8, other).unwrap();
    assert!(MemoryValuePlan::analyze(&other).is_none());
    assert!(plan.lower(&other).is_none());
}
#[test]
fn insert_store_bytes_and_mixed_whole_words_keep_their_actual_source_values() {
    use nirvana::ir::BinaryOp as B;
    let mut checked = 0;
    for start in [0, 8] {
        for byte in [0, 1] {
            let source = Program::new(
                0,
                8,
                vec![
                    ins(
                        0,
                        vec![
                            Assignment {
                                destination: Place::Memory {
                                    address: r(7),
                                    width: Width::U16,
                                },
                                value: b(
                                    B::Insert {
                                        start,
                                        width: Width::U8,
                                    },
                                    r(0),
                                    r(6),
                                ),
                            },
                            set(0, c(0)),
                            set(6, c(0)),
                        ],
                        Control::Next,
                    ),
                    ins(
                        1,
                        vec![set(2, Expr::load(b(B::Add, r(7), c(byte)), Width::U8))],
                        Control::Return(r(2)),
                    ),
                ],
            )
            .unwrap();
            let plan = MemoryValuePlan::analyze(&source).unwrap();
            let candidate = plan.lower(&source).unwrap();
            checked += compare(&source, &candidate);
            let mut mixed = source.instructions().to_vec();
            mixed[1].assignments[0].value = Expr::load(r(7), Width::U16);
            let mixed = Program::new(0, 8, mixed).unwrap();
            let plan =
                MemoryValuePlan::analyze(&mixed).expect("capture the whole pure Insert expression");
            assert_eq!(plan.evidence().snapshot_values, 1);
            checked += compare(&mixed, &plan.lower(&mixed).unwrap());
        }
    }
    println!(
        "{checked} partial-insert byte observations with distinct base/value register identities"
    );
}

#[test]
fn saved_word_origins_remain_available_across_shared_compound_memory_programs() {
    let mut checked = 0;
    for (index, source) in crate::support::byte_values::programs()
        .into_iter()
        .enumerate()
    {
        let plan = MemoryValuePlan::analyze(&source)
            .unwrap_or_else(|| panic!("byte origin family {index}"));
        if index == 0 {
            assert_eq!(
                plan.evidence().snapshot_values,
                1,
                "both disjoint slices share their original full word"
            );
        }
        let candidate = plan.lower(&source).unwrap();
        checked += compare(&source, &candidate);
    }
    println!("{checked} compound saved-byte full-prefix/memory/PC/fault/budget observations");
}

#[test]
fn shifted_masked_and_extended_stored_bytes_keep_their_actual_bit_positions() {
    use nirvana::ir::{BinaryOp as B, UnaryOp as U};
    let mut checked = 0;
    for (value, offset, width) in [
        (
            Expr::unary(
                U::Extract {
                    start: 5,
                    width: Width::U32,
                },
                r(0),
            ),
            0,
            Width::U8,
        ),
        (b(B::Shr, r(0), c(65)), 0, Width::U16),
        (b(B::Shl, r(0), c(8)), 1, Width::U16),
        (b(B::And, r(0), c(0xff0000)), 2, Width::U8),
        (b(B::Or, r(0), c(0x8000_0000_0000_0001)), 3, Width::U16),
        (b(B::Xor, r(0), c(1)), 2, Width::U16),
        (Expr::unary(U::SignExtend(Width::U16), r(0)), 0, Width::U16),
    ] {
        let source = Program::new(
            0,
            8,
            vec![
                ins(
                    0,
                    vec![
                        Assignment {
                            destination: Place::Memory {
                                address: r(7),
                                width: Width::U64,
                            },
                            value,
                        },
                        set(0, c(0)),
                    ],
                    Control::Next,
                ),
                ins(
                    1,
                    vec![set(2, Expr::load(b(B::Add, r(7), c(offset)), width))],
                    Control::Return(r(2)),
                ),
            ],
        )
        .unwrap();
        let plan = MemoryValuePlan::analyze(&source).unwrap();
        let candidate = plan.lower(&source).unwrap();
        checked += compare(&source, &candidate);
    }
    println!("{checked} stored expression/bit-window full-state observations");
}

#[test]
fn split_words_follow_actual_ssa_producers_without_erasing_first_faults() {
    let mut checked = 0;
    for source in crate::support::byte_values::producer_programs() {
        let plan = MemoryValuePlan::analyze(&source).expect("split producer source word");
        assert_eq!(plan.evidence().snapshot_values, 1);
        assert_eq!(plan.evidence().proved_loads, 1);
        let candidate = plan.lower(&source).unwrap();
        checked += compare(&source, &candidate);
        let mut rows = source.instructions().to_vec();
        rows[0].assignments[0].value = b(nirvana::ir::BinaryOp::Shr, r(0), c(17));
        let incompatible = Program::new(0, 8, rows).unwrap();
        assert!(MemoryValuePlan::analyze(&incompatible).is_none());
        assert!(plan.lower(&incompatible).is_none());
    }
    println!("{checked} SSA-producer split-word full-register/RAM/PC/fault/budget observations");
}

#[test]
fn values_created_after_loops_and_invariant_reentry_keep_their_actual_value() {
    let mut checked = 0;
    for source in crate::support::byte_values::after_loop_programs() {
        let plan = MemoryValuePlan::analyze(&source).expect("single-visit loop exit producer");
        assert_eq!(plan.evidence().snapshot_values, 1);
        assert_eq!(plan.evidence().proved_loads, 1);
        checked += compare(&source, &plan.lower(&source).unwrap());
        let mut rows = source.instructions().to_vec();
        rows[2].control = Control::Branch {
            condition: r(2),
            target: 1,
        };
        let cyclic = Program::new(0, 8, rows).unwrap();
        assert!(plan.lower(&cyclic).is_none());
        if matches!(
            source.instructions()[2].assignments[0].value,
            Expr::Load { .. }
        ) {
            assert!(MemoryValuePlan::analyze(&cyclic).is_none());
        } else {
            let repeated = MemoryValuePlan::analyze(&cyclic)
                .expect("pure invariant producer remains stable on reentry");
            checked += compare(&cyclic, &repeated.lower(&cyclic).unwrap());
        }
    }
    println!("{checked} post-loop capture full-state/fault/budget observations");
}

#[test]
fn a_pure_store_expression_is_saved_once_after_success_and_faulting_rhs_declines() {
    let mut checked = 0;
    for source in crate::support::byte_values::stored_expression_programs() {
        let plan = MemoryValuePlan::analyze(&source).expect("pure saved expression");
        assert_eq!(plan.evidence().snapshot_values, 1);
        assert_eq!(plan.evidence().proved_loads, 2);
        let candidate = plan.lower(&source).unwrap();
        checked += compare(&source, &candidate);
        let mut rows = source.instructions().to_vec();
        rows[1].assignments[0].value = b(
            nirvana::ir::BinaryOp::Add,
            Expr::load(r(7), Width::U64),
            r(0),
        );
        let effectful = Program::new(0, 8, rows).unwrap();
        assert!(MemoryValuePlan::analyze(&effectful).is_none());
        assert!(plan.lower(&effectful).is_none());
    }
    println!("{checked} pure-Store capture full-register/RAM/PC/fault/budget observations");
}

#[test]
fn repeated_invariant_captures_keep_every_prefix_and_loop_carried_inputs_decline() {
    let mut checked = 0;
    for (index, source) in crate::support::byte_values::invariant_loop_programs()
        .into_iter()
        .enumerate()
    {
        let plan = MemoryValuePlan::analyze(&source).expect("stable inputs on every dynamic visit");
        assert_eq!(plan.evidence().snapshot_values, 1);
        let candidate = plan.lower(&source).unwrap();
        checked += compare(&source, &candidate);
        if index == 2 {
            let mut rows = source.instructions().to_vec();
            rows[1].assignments[2].value =
                Expr::load(b(nirvana::ir::BinaryOp::Add, r(7), c(33)), Width::U8);
            let changing_byte = Program::new(0, 8, rows).unwrap();
            assert!(
                MemoryValuePlan::analyze(&changing_byte).is_none(),
                "the inserted byte changes across iterations"
            );
            assert!(plan.lower(&changing_byte).is_none());
        }
        let mut rows = source.instructions().to_vec();
        rows[1].assignments[0].value = b(nirvana::ir::BinaryOp::Add, r(0), r(3));
        let changing = Program::new(0, 8, rows).unwrap();
        assert!(
            MemoryValuePlan::analyze(&changing).is_none(),
            "family {index} mutable loop input"
        );
        assert!(plan.lower(&changing).is_none());
    }
    println!("{checked} repeated invariant captures with full registers/RAM/PC/faults/budgets");
}

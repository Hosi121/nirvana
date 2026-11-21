use ir::{
    AccessKind, Assignment, BinaryOp, Control, Expr, IrInstruction, Place, Program, Reg, RunStatus,
    Width,
};
use nirvana::{ir, stack_cells::CellBindings, stack_values};
use stack_values::{StackLocation, StackValues};

use crate::support::ir::c;
use crate::support::ir::r;
fn add(left: Expr, right: Expr) -> Expr {
    Expr::binary(BinaryOp::Add, left, right)
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
fn p(count: usize, instructions: Vec<IrInstruction>) -> Program {
    Program::new(0, count, instructions).unwrap()
}
fn location(offset: i64, width: Width) -> Option<StackLocation> {
    Some(StackLocation { offset, width })
}
fn analyze(program: &Program, eligible: &[usize]) -> Option<CellBindings> {
    CellBindings::analyze(
        program,
        Reg(0),
        &eligible.iter().copied().map(Reg).collect::<Vec<_>>(),
    )
}

#[test]
fn direct_loads_use_ordered_frame_and_stack_points_for_all_widths() {
    let program = p(
        6,
        vec![i(
            0,
            vec![
                set(1, r(0)),
                set(0, add(r(0), c(u64::MAX - 7))),
                set(2, Expr::load(r(0), Width::U8)),
                set(3, Expr::load(add(r(1), c(8)), Width::U16)),
                set(4, Expr::load(add(r(0), c(4)), Width::U32)),
                set(5, Expr::load(add(r(1), c(u64::MAX - 15)), Width::U64)),
            ],
            Control::Return(r(5)),
        )],
    );
    let result = analyze(&program, &[5, 3, 2, 4]).unwrap();
    assert_eq!(result.location(Reg(2)), location(-8, Width::U8));
    assert_eq!(result.location(Reg(3)), location(8, Width::U16));
    assert_eq!(result.location(Reg(4)), location(-4, Width::U32));
    assert_eq!(result.location(Reg(5)), location(-16, Width::U64));
    assert_eq!(result.location(Reg(1)), None);
    assert_eq!(result.location(Reg(usize::MAX)), None);
}

#[test]
fn unknown_and_partial_stores_do_not_invalidate_load_locations() {
    let program = p(
        4,
        vec![i(
            0,
            vec![
                store(add(r(0), c(8)), Width::U64, c(1)),
                store(r(1), Width::U64, c(2)),
                set(2, Expr::load(add(r(0), c(8)), Width::U64)),
                store(add(r(0), c(10)), Width::U8, c(3)),
                set(3, Expr::load(add(r(0), c(8)), Width::U64)),
            ],
            Control::Return(r(3)),
        )],
    );
    let values = StackValues::analyze(&program, Reg(0)).unwrap();
    assert_eq!(values.reads().len(), 2);
    assert!(values.reads().iter().all(|read| read.has_unknown));
    let result = analyze(&program, &[2, 3]).unwrap();
    assert_eq!(result.location(Reg(2)), location(8, Width::U64));
    assert_eq!(result.location(Reg(3)), location(8, Width::U64));
}

#[test]
fn initial_memory_need_not_have_a_reaching_definition() {
    let program = p(
        2,
        vec![i(
            0,
            vec![set(1, Expr::load(r(0), Width::U64))],
            Control::Return(r(1)),
        )],
    );
    assert!(StackValues::analyze(&program, Reg(0)).unwrap().reads()[0].has_unknown);
    assert_eq!(
        analyze(&program, &[1]).unwrap().location(Reg(1)),
        location(0, Width::U64)
    );
}

#[test]
fn propagation_is_forward_exact_copy_only_and_stores_never_seed() {
    let program = p(
        10,
        vec![i(
            0,
            vec![
                set(1, Expr::load(add(r(0), c(12)), Width::U16)),
                set(2, r(1)),
                set(3, r(2)),
                set(4, add(r(3), c(0))),
                set(5, Expr::select(c(1), r(1), r(1))),
                set(6, c(7)),
                store(r(0), Width::U64, r(6)),
                set(7, r(6)),
                set(8, Expr::load(r(0), Width::U64)),
                set(9, r(8)),
            ],
            Control::Return(r(9)),
        )],
    );
    let result = analyze(&program, &[1, 2, 3, 4, 5, 6, 7, 9]).unwrap();
    for reg in [1, 2, 3] {
        assert_eq!(result.location(Reg(reg)), location(12, Width::U16));
    }
    for reg in [4, 5, 6, 7, 8, 9] {
        assert_eq!(result.location(Reg(reg)), None);
    }
}

#[test]
fn copies_resolve_by_cfg_dependency_instead_of_instruction_address_order() {
    let program = Program::new(
        2,
        4,
        vec![
            i(0, vec![set(2, r(1))], Control::Jump(1)),
            i(1, vec![set(3, r(2))], Control::Return(r(3))),
            i(
                2,
                vec![set(1, Expr::load(r(0), Width::U8))],
                Control::Jump(0),
            ),
        ],
    )
    .unwrap();
    let result = analyze(&program, &[1, 2, 3]).unwrap();
    for reg in [1, 2, 3] {
        assert_eq!(result.location(Reg(reg)), location(0, Width::U8));
    }
}

#[test]
fn repeated_static_definitions_reject_that_binding_and_its_copy() {
    let program = p(
        3,
        vec![i(
            0,
            vec![
                set(1, Expr::load(r(0), Width::U64)),
                set(1, Expr::load(r(0), Width::U64)),
                set(2, r(1)),
            ],
            Control::Return(r(2)),
        )],
    );
    let result = analyze(&program, &[1, 2]).unwrap();
    assert_eq!(result.location(Reg(1)), None);
    assert_eq!(result.location(Reg(2)), None);
}

#[test]
fn joins_with_ambiguous_addresses_are_unbound_and_pure_agreeing_arms_are_allowed() {
    let program = p(
        5,
        vec![
            i(
                0,
                vec![],
                Control::Branch {
                    condition: r(4),
                    target: 2,
                },
            ),
            i(1, vec![set(1, r(0))], Control::Jump(3)),
            i(2, vec![set(1, add(r(0), c(8)))], Control::Jump(3)),
            i(
                3,
                vec![
                    set(2, Expr::load(r(1), Width::U64)),
                    set(3, Expr::load(Expr::select(r(4), r(0), r(0)), Width::U32)),
                ],
                Control::Return(r(3)),
            ),
        ],
    );
    let result = analyze(&program, &[2, 3]).unwrap();
    assert_eq!(result.location(Reg(2)), None);
    assert_eq!(result.location(Reg(3)), location(0, Width::U32));
}

#[test]
fn load_bearing_addresses_and_load_bearing_rhs_selects_are_not_bound() {
    let address = Expr::select(Expr::load(c(u64::MAX), Width::U8), r(0), r(0));
    let program = p(
        3,
        vec![i(
            0,
            vec![
                set(1, Expr::load(address, Width::U64)),
                set(
                    2,
                    Expr::select(
                        c(1),
                        Expr::load(r(0), Width::U64),
                        Expr::load(r(0), Width::U64),
                    ),
                ),
            ],
            Control::Return(r(2)),
        )],
    );
    let result = analyze(&program, &[1, 2]).unwrap();
    assert_eq!(result.location(Reg(1)), None);
    assert_eq!(result.location(Reg(2)), None);
}

#[test]
fn unreachable_writes_do_not_turn_a_reachable_single_write_into_multiple() {
    let program = p(
        2,
        vec![
            i(
                0,
                vec![set(1, Expr::load(r(0), Width::U64))],
                Control::Return(r(1)),
            ),
            i(
                1,
                vec![set(1, Expr::load(add(r(0), c(8)), Width::U8))],
                Control::Return(r(1)),
            ),
        ],
    );
    assert_eq!(
        analyze(&program, &[1]).unwrap().location(Reg(1)),
        location(0, Width::U64)
    );
}

#[test]
fn entry_reads_in_rhs_addresses_controls_and_backedges_reject_the_whole_analysis() {
    let programs = [
        p(
            2,
            vec![i(
                0,
                vec![set(1, Expr::load(r(1), Width::U64))],
                Control::Return(r(1)),
            )],
        ),
        p(
            2,
            vec![i(
                0,
                vec![
                    store(r(1), Width::U8, c(1)),
                    set(1, Expr::load(r(0), Width::U64)),
                ],
                Control::Return(r(1)),
            )],
        ),
        p(2, vec![i(0, vec![], Control::Return(r(1)))]),
        p(
            3,
            vec![i(
                0,
                vec![set(2, r(1)), set(1, Expr::load(r(0), Width::U64))],
                Control::Jump(0),
            )],
        ),
    ];
    for program in programs {
        assert!(analyze(&program, &[1]).is_none());
    }
}

#[test]
fn invalid_eligible_registers_and_sparse_register_counts_are_bounded() {
    let program = p(
        2,
        vec![i(
            0,
            vec![set(1, Expr::load(r(0), Width::U64))],
            Control::Return(r(1)),
        )],
    );
    assert!(analyze(&program, &[1, 1]).is_none());
    assert!(analyze(&program, &[2]).is_none());
    assert!(CellBindings::analyze(&program, Reg(2), &[Reg(1)]).is_none());
    assert!(analyze(&program, &[]).unwrap().location(Reg(1)).is_none());
    let sparse = p(
        65_536,
        vec![i(
            0,
            vec![
                set(65_535, Expr::load(r(0), Width::U64)),
                set(65_000, r(65_535)),
            ],
            Control::Return(r(65_000)),
        )],
    );
    let result = analyze(&sparse, &[65_000, 65_535]).unwrap();
    assert_eq!(result.location(Reg(65_000)), location(0, Width::U64));
    let extreme = p(
        usize::MAX,
        vec![i(
            0,
            vec![set(usize::MAX - 1, Expr::load(r(0), Width::U64))],
            Control::Return(r(usize::MAX - 1)),
        )],
    );
    assert!(analyze(&extreme, &[usize::MAX - 1]).is_none());
    let many = p(4098, vec![i(0, vec![], Control::Return(c(0)))]);
    assert!(analyze(&many, &(1..4098).collect::<Vec<_>>()).is_none());
}

#[test]
fn full_input_depth_active_and_upstream_bounds_discard_all_results() {
    let mut deep = r(0);
    for _ in 0..150 {
        deep = add(deep, c(0));
    }
    let program = p(
        2,
        vec![
            i(
                0,
                vec![set(1, Expr::load(r(0), Width::U64))],
                Control::Return(r(1)),
            ),
            i(1, vec![store(deep, Width::U8, c(1))], Control::Return(c(0))),
        ],
    );
    assert!(analyze(&program, &[1]).is_none());
    let active = p(
        9000,
        vec![i(
            0,
            (1..8194).map(|index| set(index, c(0))).collect(),
            Control::Return(c(0)),
        )],
    );
    assert!(analyze(&active, &[]).is_none());
    let mut instructions = vec![i(
        0,
        vec![set(1, Expr::load(r(0), Width::U64))],
        Control::Return(r(1)),
    )];
    instructions.extend((1..502).map(|address| i(address, vec![], Control::Return(c(0)))));
    let upstream = p(1000, instructions);
    assert!(analyze(&upstream, &[1]).is_none());
}

#[test]
fn wrapped_offsets_are_bit_patterns_and_input_ir_is_immutable() {
    let program = p(
        3,
        vec![i(
            0,
            vec![
                set(1, Expr::load(add(r(0), c(1u64 << 63)), Width::U64)),
                set(2, r(1)),
            ],
            Control::Return(r(2)),
        )],
    );
    let original = program.instructions().to_vec();
    for eligible in [[1, 2], [2, 1]] {
        let result = analyze(&program, &eligible).unwrap();
        assert_eq!(result.location(Reg(1)), location(i64::MIN, Width::U64));
        assert_eq!(result.location(Reg(2)), location(i64::MIN, Width::U64));
    }
    assert_eq!(program.instructions(), original);
    assert_eq!(program.register_count(), 3);
}

#[test]
fn concrete_replay_reads_current_bytes_after_unknown_and_partial_writes() {
    let memory: Vec<_> = (0..192)
        .map(|i| (i as u8).wrapping_mul(29).wrapping_add(7))
        .collect();
    for width in [Width::U8, Width::U16, Width::U32, Width::U64] {
        for displacement in -24i64..=24 {
            let address = add(r(0), c(displacement as u64));
            let program = p(
                4,
                vec![i(
                    0,
                    vec![
                        store(address.clone(), Width::U64, c(0x0123_4567_89ab_cdef)),
                        store(r(1), Width::U64, r(3)),
                        store(add(address.clone(), c(3)), Width::U8, c(0x5a)),
                        set(2, Expr::load(address, width)),
                    ],
                    Control::Return(r(2)),
                )],
            );
            assert_eq!(
                analyze(&program, &[2]).unwrap().location(Reg(2)),
                location(displacement, width)
            );
            for stack in [48u64, 64, 80] {
                let actual = stack.wrapping_add(displacement as u64);
                let data = (actual.wrapping_mul(0x9e37_79b9)).rotate_left(13);
                let mut expected = memory.clone();
                expected[actual as usize..actual as usize + 8].copy_from_slice(&data.to_le_bytes());
                expected[actual as usize + 3] = 0x5a;
                let mut value = 0u64;
                for byte in 0..width.bytes() {
                    value |= u64::from(expected[actual as usize + byte]) << (byte * 8);
                }
                let report = program
                    .run_with_memory(&[stack, actual, 0xdead_beef, data], 0, &memory, 4)
                    .unwrap();
                assert_eq!(report.status, RunStatus::Returned(value));
                assert_eq!(report.state.memory, expected);
                assert_eq!(report.state.trace, vec![0]);
            }
        }
    }
}

#[test]
fn location_candidates_do_not_assert_success_or_erase_the_first_fault() {
    let program = p(
        2,
        vec![i(
            0,
            vec![set(1, Expr::load(add(r(0), c(1)), Width::U64))],
            Control::Return(r(1)),
        )],
    );
    let before = program.instructions().to_vec();
    assert_eq!(
        analyze(&program, &[1]).unwrap().location(Reg(1)),
        location(1, Width::U64)
    );
    for stack in [0, u64::MAX - 1, u64::MAX] {
        let expected_address = stack.wrapping_add(1);
        let report = program
            .run_with_memory(&[stack, 0xdead_beef], 0, &[0; 4], 4)
            .unwrap();
        let RunStatus::Fault(fault) = report.status else {
            panic!("expected fault")
        };
        assert_eq!(fault.access, AccessKind::Read);
        assert_eq!(fault.address, expected_address);
        assert_eq!(fault.width, Width::U64);
        assert_eq!(report.state.registers[1], 0xdead_beef);
        assert_eq!(report.state.memory, vec![0; 4]);
        assert_eq!(report.state.trace, vec![0]);
    }
    assert_eq!(program.instructions(), before);
}

#[test]
fn a_copy_keeps_the_original_load_location_when_memory_has_changed() {
    let program = p(
        4,
        vec![i(
            0,
            vec![
                store(r(0), Width::U64, c(1)),
                set(1, Expr::load(r(0), Width::U64)),
                store(r(3), Width::U64, c(2)),
                set(2, r(1)),
            ],
            Control::Return(r(2)),
        )],
    );
    let result = analyze(&program, &[1, 2]).unwrap();
    assert_eq!(result.location(Reg(1)), location(0, Width::U64));
    assert_eq!(result.location(Reg(2)), location(0, Width::U64));
    let report = program
        .run_with_memory(&[16, 99, 77, 16], 0, &[0; 32], 4)
        .unwrap();
    assert_eq!(report.status, RunStatus::Returned(1));
    assert_eq!(&report.state.memory[16..24], &2u64.to_le_bytes());
}

#[test]
fn a_single_static_copy_can_execute_on_a_loop_without_becoming_multiple_definitions() {
    let program = p(
        4,
        vec![
            i(0, vec![set(1, Expr::load(r(0), Width::U32))], Control::Next),
            i(
                1,
                vec![set(2, r(1))],
                Control::Branch {
                    condition: r(3),
                    target: 1,
                },
            ),
            i(2, vec![], Control::Return(r(2))),
        ],
    );
    let result = analyze(&program, &[1, 2]).unwrap();
    assert_eq!(result.location(Reg(1)), location(0, Width::U32));
    assert_eq!(result.location(Reg(2)), location(0, Width::U32));
}

#[test]
fn a_copy_cycle_cannot_manufacture_a_binding_from_arbitrary_entry_values() {
    let program = p(
        3,
        vec![i(
            0,
            vec![set(1, r(2)), set(2, r(1))],
            Control::Return(r(2)),
        )],
    );
    assert!(analyze(&program, &[1, 2]).is_none());
}

use nirvana::ir::{
    AccessKind, Assignment, BinaryOp, Control, Expr, IrInstruction, Place, Program, Reg, Width,
};
use nirvana::provenance::{AddressAccess, AddressAnalysis, AddressOrigin};
use nirvana::reduce::reduce;

use crate::support::ir::c;
use crate::support::ir::r;
fn add(left: Expr, right: Expr) -> Expr {
    Expr::binary(BinaryOp::Add, left, right)
}
fn at(register: usize, offset: u64) -> Expr {
    add(r(register), c(offset))
}
fn set(register: usize, value: Expr) -> Assignment {
    Assignment {
        destination: Reg(register).into(),
        value,
    }
}
fn store(address: Expr, width: Width, value: Expr) -> Assignment {
    Assignment {
        destination: Place::Memory { address, width },
        value,
    }
}
fn load(address: Expr) -> Expr {
    Expr::load(address, Width::U64)
}
fn i(address: u64, assignments: Vec<Assignment>, control: Control) -> IrInstruction {
    IrInstruction {
        address,
        size: 1,
        assignments,
        control,
    }
}
fn program(registers: usize, instructions: Vec<IrInstruction>) -> Program {
    Program::new(0, registers, instructions).unwrap()
}
fn straight(registers: usize, assignments: Vec<Assignment>) -> Program {
    program(registers, vec![i(0, assignments, Control::Return(c(0)))])
}
fn expected(register: usize, offset: i64) -> Option<AddressOrigin> {
    Some(AddressOrigin {
        register: Reg(register),
        offset,
    })
}

#[test]
fn only_explicit_inputs_start_symbolic_and_points_are_sequential() {
    let p = straight(4, vec![set(2, r(0)), set(0, at(0, 8)), set(2, r(0))]);
    let a = AddressAnalysis::analyze(&p, &[Reg(0), Reg(1)]);
    assert_eq!(a.origin_before(0, 0, &r(0)), expected(0, 0));
    assert_eq!(a.origin_before(0, 0, &r(1)), expected(1, 0));
    assert_eq!(a.origin_before(0, 0, &r(2)), None);
    assert_eq!(a.origin_before(0, 1, &r(2)), expected(0, 0));
    assert_eq!(a.origin_before(0, 2, &r(0)), expected(0, 8));
    assert_eq!(a.origin_before(0, 2, &r(2)), expected(0, 0));
    assert_eq!(a.origin_before(0, 3, &r(2)), expected(0, 8));
    for expression in [r(3), r(99), c(0), add(r(0), r(1))] {
        assert_eq!(a.origin_before(0, 3, &expression), None);
    }
    assert_eq!(a.origin_before(0, 4, &r(0)), None);
    assert_eq!(a.origin_before(1, 0, &r(0)), None);
    assert!(
        AddressAnalysis::analyze(&p, &[Reg(4)])
            .accesses()
            .is_empty()
    );
    assert_eq!(
        AddressAnalysis::analyze(&p, &[]).origin_before(0, 0, &r(0)),
        None
    );
}

#[test]
fn exact_u64_spills_restore_origins_without_replacing_loads() {
    let p = straight(
        5,
        vec![
            set(2, at(0, u64::MAX - 15)),
            store(r(2), Width::U64, at(1, 4)),
            set(3, load(r(2))),
            set(4, Expr::load(r(2), Width::U32)),
            set(3, add(r(3), c(8))),
        ],
    );
    let a = AddressAnalysis::analyze(&p, &[Reg(0), Reg(1)]);
    assert_eq!(a.origin_before(0, 2, &r(3)), None);
    assert_eq!(a.origin_before(0, 3, &r(3)), expected(1, 4));
    assert_eq!(a.origin_before(0, 4, &r(4)), None);
    assert_eq!(a.origin_before(0, 5, &r(3)), expected(1, 12));
    assert_eq!(a.origin_before(0, 2, &load(r(2))), None);
    assert_eq!(
        a.accesses()[0],
        AddressAccess {
            instruction: 0,
            assignment: 1,
            origin: expected(0, -16).unwrap(),
            width: Width::U64,
            kind: AccessKind::Write,
        }
    );
    assert_eq!(a.accesses()[1].kind, AccessKind::Read);
    assert_eq!(a.accesses()[2].width, Width::U32);
}

#[test]
fn same_base_disjoint_stores_survive_and_partial_overlaps_invalidate() {
    for (offset, width, survives) in [
        (8, Width::U8, true),
        (16, Width::U64, true),
        (u64::MAX, Width::U8, true),
        (u64::MAX, Width::U16, false),
        (0, Width::U8, false),
        (7, Width::U8, false),
        (4, Width::U32, false),
        (0, Width::U64, false),
    ] {
        let p = straight(
            4,
            vec![
                store(r(0), Width::U64, r(1)),
                store(at(0, offset), width, r(3)),
                set(2, load(r(0))),
            ],
        );
        let a = AddressAnalysis::analyze(&p, &[Reg(0), Reg(1)]);
        assert_eq!(
            a.origin_before(0, 3, &r(2)),
            survives.then(|| expected(1, 0).unwrap()),
            "offset={offset:#x}, width={width:?}"
        );
    }
}

#[test]
fn different_input_bases_absolute_addresses_and_unknown_stores_may_alias() {
    for target in [r(2), at(2, 1024), c(64), r(4)] {
        let p = straight(
            5,
            vec![
                store(r(0), Width::U64, r(1)),
                store(target, Width::U8, c(7)),
                set(3, load(r(0))),
            ],
        );
        let a = AddressAnalysis::analyze(&p, &[Reg(0), Reg(1), Reg(2)]);
        assert_eq!(a.origin_before(0, 3, &r(3)), None);
    }
    let p = straight(
        4,
        vec![
            store(c(64), Width::U64, r(1)),
            store(r(0), Width::U8, c(7)),
            set(3, load(c(64))),
        ],
    );
    let a = AddressAnalysis::analyze(&p, &[Reg(0), Reg(1)]);
    assert_eq!(a.origin_before(0, 3, &r(3)), None);
}

#[test]
fn absolute_spill_addresses_and_constants_can_be_forwarded_exactly() {
    let p = straight(
        4,
        vec![
            store(c(64), Width::U64, r(1)),
            store(c(72), Width::U64, c(u64::MAX)),
            set(2, load(c(64))),
            set(3, load(c(72))),
            set(2, add(r(2), r(3))),
        ],
    );
    let a = AddressAnalysis::analyze(&p, &[Reg(1)]);
    assert_eq!(a.origin_before(0, 5, &r(2)), expected(1, -1));
}

#[test]
fn modular_byte_ranges_handle_wrapping_offsets() {
    for (offset, survives) in [(0, false), (1, false), (3, false), (4, true), (8, true)] {
        let p = straight(
            3,
            vec![
                store(at(0, u64::MAX - 3), Width::U64, r(1)),
                store(at(0, offset), Width::U8, c(0)),
                set(2, load(at(0, u64::MAX - 3))),
            ],
        );
        let a = AddressAnalysis::analyze(&p, &[Reg(0), Reg(1)]);
        assert_eq!(
            a.origin_before(0, 3, &r(2)),
            survives.then(|| expected(1, 0).unwrap())
        );
    }
}

fn spill_diamond(right: Vec<Assignment>) -> Program {
    program(
        4,
        vec![
            i(
                0,
                vec![],
                Control::Branch {
                    condition: r(2),
                    target: 2,
                },
            ),
            i(1, vec![store(r(0), Width::U64, at(1, 8))], Control::Jump(3)),
            i(2, right, Control::Jump(3)),
            i(3, vec![set(3, load(r(0)))], Control::Return(r(3))),
            i(4, vec![store(r(0), Width::U8, c(0))], Control::Jump(3)),
        ],
    )
}

#[test]
fn branch_meets_require_identical_spill_facts_on_every_reachable_path() {
    for (right, result) in [
        (vec![store(r(0), Width::U64, at(1, 8))], expected(1, 8)),
        (vec![store(r(0), Width::U64, at(1, 16))], None),
        (vec![], None),
        (vec![store(r(0), Width::U8, c(0))], None),
    ] {
        let p = spill_diamond(right);
        let a = AddressAnalysis::analyze(&p, &[Reg(0), Reg(1), Reg(2)]);
        assert_eq!(a.origin_before(3, 1, &r(3)), result);
        assert_eq!(a.origin_before(4, 0, &r(0)), None);
    }
}

#[test]
fn loop_fixed_points_preserve_invariants_and_drop_changed_spills() {
    for (offset, survives) in [(16, true), (0, false)] {
        let p = program(
            4,
            vec![
                i(0, vec![store(r(0), Width::U64, r(1))], Control::Jump(1)),
                i(
                    1,
                    vec![set(3, load(r(0))), store(at(0, offset), Width::U8, c(0))],
                    Control::Branch {
                        condition: r(2),
                        target: 1,
                    },
                ),
                i(2, vec![], Control::Return(r(3))),
            ],
        );
        let a = AddressAnalysis::analyze(&p, &[Reg(0), Reg(1), Reg(2)]);
        assert_eq!(
            a.origin_before(1, 1, &r(3)),
            survives.then(|| expected(1, 0).unwrap())
        );
    }
    let p = program(
        4,
        vec![
            i(
                0,
                vec![set(3, load(r(0))), store(r(0), Width::U64, r(1))],
                Control::Branch {
                    condition: r(2),
                    target: 0,
                },
            ),
            i(1, vec![], Control::Return(r(3))),
        ],
    );
    let a = AddressAnalysis::analyze(&p, &[Reg(0), Reg(1), Reg(2)]);
    assert_eq!(a.origin_before(0, 0, &r(3)), None);
    assert_eq!(a.origin_before(0, 1, &r(3)), None);
}

#[test]
fn nested_reloads_and_store_rhs_use_the_pre_store_memory() {
    let p = straight(
        3,
        vec![
            store(r(0), Width::U64, at(0, 16)),
            store(at(0, 16), Width::U64, at(1, 4)),
            set(2, load(load(r(0)))),
            store(r(0), Width::U64, load(at(0, 16))),
            set(2, load(r(0))),
        ],
    );
    let a = AddressAnalysis::analyze(&p, &[Reg(0), Reg(1)]);
    assert_eq!(a.origin_before(0, 3, &r(2)), expected(1, 4));
    assert_eq!(a.origin_before(0, 5, &r(2)), expected(1, 4));
    assert_eq!(a.origin_before(0, 2, &load(load(r(0)))), None);
    assert!(
        a.accesses()
            .iter()
            .any(|a| a.assignment == 2 && a.origin == expected(0, 16).unwrap())
    );
}

#[test]
fn load_bearing_select_queries_are_rejected_even_when_values_agree() {
    let p = straight(
        3,
        vec![
            store(r(0), Width::U64, r(1)),
            set(2, Expr::select(load(r(0)), r(1), r(1))),
        ],
    );
    let a = AddressAnalysis::analyze(&p, &[Reg(0), Reg(1)]);
    assert_eq!(a.origin_before(0, 2, &r(2)), expected(1, 0));
    for address in [
        Expr::select(load(c(u64::MAX)), r(1), r(1)),
        Expr::select(c(1), r(1), load(r(0))),
        Expr::select(load(r(0)), r(1), r(1)),
        Expr::select(Expr::binary(BinaryOp::Mul, load(r(0)), c(0)), r(1), r(1)),
    ] {
        assert_eq!(a.origin_before(0, 1, &address), None);
    }
    assert_eq!(
        a.origin_before(0, 1, &Expr::select(r(2), r(1), r(1))),
        expected(1, 0)
    );
}

#[test]
fn reduced_fresh_registers_do_not_become_implicit_inputs() {
    let p = straight(
        3,
        vec![
            store(at(0, 8), Width::U64, at(1, 12)),
            set(2, load(at(0, 8))),
            store(at(2, 4), Width::U32, c(9)),
        ],
    );
    let reduced = reduce(&p).unwrap();
    let a = AddressAnalysis::analyze(reduced.program(), reduced.parameters());
    assert!(reduced.program().register_count() > p.register_count());
    for register in p.register_count()..reduced.program().register_count() {
        assert_eq!(a.origin_before(0, 0, &r(register)), None);
    }
    assert!(
        a.accesses()
            .iter()
            .any(|a| a.origin == expected(1, 16).unwrap() && a.kind == AccessKind::Write)
    );
}

#[test]
fn exhaustion_discards_all_results_instead_of_exposing_partial_facts() {
    let assignments = (0..257)
        .map(|index| store(at(0, index * 8), Width::U64, r(1)))
        .collect();
    let p = straight(2, assignments);
    let a = AddressAnalysis::analyze(&p, &[Reg(0), Reg(1)]);
    assert_eq!(a.origin_before(0, 0, &r(0)), None);
    assert!(a.accesses().is_empty());

    let mut deep = r(0);
    for _ in 0..260 {
        deep = add(deep, c(0));
    }
    let p = program(
        1,
        vec![
            i(0, vec![store(r(0), Width::U64, r(0))], Control::Next),
            i(1, vec![], Control::Return(deep)),
        ],
    );
    let a = AddressAnalysis::analyze(&p, &[Reg(0)]);
    assert_eq!(a.origin_before(0, 0, &r(0)), None);
    assert!(a.accesses().is_empty());
}

#[test]
fn inferred_values_match_concrete_ir_prefix_replays_with_aliasing_and_wraps() {
    let assignments = vec![
        set(4, at(0, u64::MAX - 15)),
        store(r(4), Width::U64, at(1, 7)),
        store(at(4, 16), Width::U64, at(0, 32)),
        set(5, load(r(4))),
        set(6, Expr::select(r(3), load(r(4)), at(1, 7))),
        store(r(4), Width::U64, add(load(r(4)), c(1))),
        set(5, load(r(4))),
        // Input 2 takes concrete addresses equal to, partially overlapping,
        // adjacent to, and far from the spill. It is never assumed separate.
        store(r(2), Width::U8, c(3)),
        set(7, load(r(4))),
        store(at(0, 64), Width::U64, at(1, u64::MAX)),
        set(7, load(at(0, 64))),
    ];
    let p = straight(8, assignments.clone());
    let a = AddressAnalysis::analyze(&p, &[Reg(0), Reg(1), Reg(2), Reg(3)]);
    let mut memory = vec![0; 512];
    for (index, byte) in memory.iter_mut().enumerate() {
        *byte = (index as u8).wrapping_mul(17);
    }
    let mut checked = 0;
    for base in [0u64, 8, 32, 128, 440, 504, u64::MAX - 3] {
        for pointer in [0u64, 0x1234, 1 << 63, u64::MAX] {
            for alias_offset in [u64::MAX - 16, u64::MAX - 15, u64::MAX - 8, 0, 128] {
                for condition in [0, 1] {
                    let input = [
                        base,
                        pointer,
                        base.wrapping_add(alias_offset),
                        condition,
                        99,
                        99,
                        99,
                        99,
                    ];
                    for point in 0..=assignments.len() {
                        for register in 0..8 {
                            let expression = at(register, u64::MAX);
                            let Some(origin) = a.origin_before(0, point, &expression) else {
                                continue;
                            };
                            // The existing interpreter is the independent
                            // oracle. A faulting prefix establishes no later
                            // value; every successful prefix must agree.
                            let prefix = program(
                                8,
                                vec![i(
                                    0,
                                    assignments[..point].to_vec(),
                                    Control::Return(expression),
                                )],
                            );
                            if let Ok(execution) = prefix.execute_with_memory(&input, 0, &memory, 1)
                            {
                                assert_eq!(
                                    execution.value,
                                    input[origin.register.0].wrapping_add(origin.offset as u64),
                                    "point={point} register={register} input={input:?}"
                                );
                                checked += 1;
                            }
                        }
                    }
                }
            }
        }
    }
    assert!(checked > 10_000, "non-vacuous concrete checks: {checked}");
}

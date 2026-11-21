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
    let mut count = 0;
    for value in [0, 1, 2, 3, 127, 128, 255, 256, 1 << 31, 1 << 63, u64::MAX] {
        for branch in [0, 1] {
            for pointer in [4096, 4097, 4104, 4112, 4120, 4127, u64::MAX] {
                let mut initial = vec![0x7890_cafe_1234_5678; source.register_count()];
                initial[0] = value;
                initial[1] = branch;
                initial[7] = pointer;
                let mut extended = initial.clone();
                extended.resize(candidate.register_count(), 0xdead_beef_1234_5678);
                for memory in [[0; 32], [0xa5; 32]] {
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
fn cyclic_producers_entry_backedges_and_non_preserving_word_wrappers_decline() {
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
        b(B::Shr, r(0), c(8)),
    ] {
        let source = source(Width::U16);
        let old = MemoryValuePlan::analyze(&source).unwrap();
        let mut changed = source.instructions().to_vec();
        changed[0].assignments[0].value = value;
        let changed = Program::new(0, 4, changed).unwrap();
        assert!(MemoryValuePlan::analyze(&changed).is_none());
        assert!(old.lower(&changed).is_none());
    }
}

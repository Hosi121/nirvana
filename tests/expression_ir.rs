use nirvana::expression_ir::{ArithmeticExpression, ExpressionPlan, validate};
use nirvana::ir::{
    Assignment, BinaryOp as B, Control, Expr, IrInstruction, Place, Program, Reg, RunStatus, Width,
};
use nirvana::{display_dce, readable, x86};
use std::fmt::Write as _;
#[path = "support/checked_c.rs"]
#[allow(dead_code)]
mod checked_c;
#[path = "support/native.rs"]
#[allow(dead_code)]
mod native;
fn r(n: usize) -> Expr {
    Expr::Register(Reg(n))
}
fn c(n: u64) -> Expr {
    Expr::Const(n)
}
fn b(op: B, a: Expr, z: Expr) -> Expr {
    Expr::binary(op, a, z)
}
fn set(n: usize, value: Expr) -> Assignment {
    Assignment {
        destination: Reg(n).into(),
        value,
    }
}
fn address(offset: u64) -> Expr {
    b(B::Add, r(x86::RDI), c(offset))
}
fn store(offset: u64, value: Expr) -> Assignment {
    Assignment {
        destination: Place::Memory {
            address: address(offset),
            width: Width::U64,
        },
        value,
    }
}
fn make(assignments: Vec<Assignment>) -> Program {
    Program::new(
        0,
        x86::REGISTER_COUNT,
        vec![IrInstruction {
            address: 0,
            size: 1,
            assignments,
            control: Control::Return(b(B::Xor, b(B::Xor, r(2), r(3)), r(0))),
        }],
    )
    .unwrap()
}
fn source() -> Program {
    make(vec![
        set(0, Expr::load(r(x86::RDI), Width::U64)),
        set(6, r(0)),
        set(1, b(B::UMulHigh, c(0xaaaaaaaaaaaaaaab), r(0))),
        set(0, c(99)),
        store(8, r(0)),
        set(4, Expr::load(address(24), Width::U64)),
        set(2, b(B::Shr, r(1), c(1))),
        set(5, b(B::And, r(1), c(u64::MAX << 1))),
        set(8, b(B::Add, r(5), r(2))),
        set(3, b(B::Sub, r(6), r(8))),
        store(16, r(3)),
    ])
}
fn loop_source() -> Program {
    let instructions = vec![
        IrInstruction {
            address: 0,
            size: 1,
            assignments: vec![
                set(0, Expr::load(r(x86::RDI), Width::U64)),
                set(9, b(B::And, Expr::load(address(24), Width::U64), c(3))),
                set(10, c(0)),
            ],
            control: Control::Jump(1),
        },
        IrInstruction {
            address: 1,
            size: 1,
            assignments: vec![],
            control: Control::Branch {
                condition: b(B::Eq, r(9), c(0)),
                target: 3,
            },
        },
        IrInstruction {
            address: 2,
            size: 1,
            assignments: vec![
                set(6, r(0)),
                set(1, b(B::UMulHigh, c(0xaaaaaaaaaaaaaaab), r(0))),
                set(0, c(99)),
                set(2, b(B::Shr, r(1), c(1))),
                set(
                    3,
                    b(
                        B::Sub,
                        r(6),
                        b(B::Add, b(B::And, r(1), c(u64::MAX << 1)), r(2)),
                    ),
                ),
                store(16, r(3)),
                set(10, b(B::Add, r(10), b(B::Xor, r(2), r(3)))),
                set(0, b(B::Add, r(6), c(1))),
                set(9, b(B::Sub, r(9), c(1))),
            ],
            control: Control::Jump(1),
        },
        IrInstruction {
            address: 3,
            size: 1,
            assignments: vec![store(8, r(10))],
            control: Control::Return(r(10)),
        },
    ];
    Program::new(0, 32, instructions).unwrap()
}
#[test]
fn repeated_block_captures_preserve_loop_carried_values_and_cutoffs() {
    let source = loop_source();
    let plan = ExpressionPlan::analyze(&source).unwrap();
    let lowered = plan.lower(&source).unwrap();
    let compact = display_dce::propose(&lowered).unwrap();
    for x in [0, 1, 2, 3, u64::MAX - 2, u64::MAX] {
        for count in 0..4u64 {
            let mut input = [0; 32];
            input[x86::RDI] = 4096;
            let mut memory = [0; 32];
            memory[..8].copy_from_slice(&x.to_le_bytes());
            memory[24..].copy_from_slice(&count.to_le_bytes());
            compare(&source, &lowered, &input, 4096, &memory);
            compare(&source, &compact, &input, 4096, &memory);
            let expected = (0..count)
                .map(|i| x.wrapping_add(i))
                .fold(0u64, |a, x| a.wrapping_add((x / 3) ^ (x % 3)));
            assert_eq!(
                compact
                    .execute_with_memory(
                        &[input.to_vec(), vec![0; compact.register_count() - 32]].concat(),
                        4096,
                        &memory,
                        32
                    )
                    .unwrap()
                    .value,
                expected
            );
        }
    }
}

fn compare(source: &Program, target: &Program, input: &[u64], base: u64, memory: &[u8]) {
    let mut extended = vec![0; target.register_count()];
    extended[..input.len()].copy_from_slice(input);
    for limit in [0, 1, 2, 8] {
        let a = source.run_with_memory(input, base, memory, limit).unwrap();
        let z = target
            .run_with_memory(&extended, base, memory, limit)
            .unwrap();
        assert_eq!(a.status, z.status);
        assert_eq!(a.state.memory, z.state.memory);
        assert_eq!(a.state.trace, z.state.trace);
    }
}
#[test]
fn snapshot_survives_overwritten_input_and_extended_lifetime() {
    let source = source();
    let unchanged = source.instructions().to_vec();
    let plan = ExpressionPlan::analyze(&source).unwrap();
    assert_eq!(
        (
            plan.evidence().snapshots,
            plan.evidence().divisions,
            plan.evidence().remainders
        ),
        (1, 1, 1)
    );
    let selected = plan.selections();
    let ArithmeticExpression::UnsignedDivide {
        value: qid,
        divisor: 3,
    } = selected[0].expression
    else {
        panic!()
    };
    let ArithmeticExpression::UnsignedRemainder {
        value: rid,
        divisor: 3,
    } = selected[1].expression
    else {
        panic!()
    };
    assert_eq!(qid, rid);
    assert_eq!(plan.values()[0].point().assignment, 2);
    assert_eq!(plan.values()[0].expression(), &r(0));
    let snapshot = plan.values()[0].storage().unwrap();
    assert_eq!(snapshot, Reg(source.register_count()));
    let expanded = plan.lower(&source).unwrap();
    assert!(validate(&source, &plan, &expanded));
    let compact = display_dce::propose(&expanded).unwrap();
    assert!(display_dce::validate(&expanded, &compact));
    assert!(
        compact.instructions()[0]
            .assignments
            .iter()
            .all(|a| !matches!(a.destination, Place::Register(Reg(1 | 5 | 8))))
    );
    assert_eq!(source.instructions(), unchanged);
    for x in [0, 1, 2, 3, 4, 5, 1 << 63, u64::MAX - 1, u64::MAX] {
        for pointer in [4096, 4097, 4104, 4320, 4328, 4336, 4344, 4351, u64::MAX] {
            let mut input = vec![0; source.register_count()];
            input[x86::RDI] = pointer;
            let mut memory = vec![0; 256];
            if let Some(offset) = pointer.checked_sub(4096).filter(|&n| n <= 248) {
                memory[offset as usize..offset as usize + 8].copy_from_slice(&x.to_le_bytes());
            }
            compare(&source, &expanded, &input, 4096, &memory);
            compare(&source, &compact, &input, 4096, &memory);
        }
    }
}
#[test]
fn lowered_checker_rejects_changed_capture_rewrite_effect_order_and_source() {
    let source = source();
    let plan = ExpressionPlan::analyze(&source).unwrap();
    let good = plan.lower(&source).unwrap();
    let rebuild = |instructions| Program::new(0, good.register_count(), instructions).unwrap();
    let mut bad = good.instructions().to_vec();
    bad[0].assignments[2].value = c(99);
    assert!(!validate(&source, &plan, &rebuild(bad)));
    let mut bad = good.instructions().to_vec();
    bad[0].assignments[7].value = r(0);
    assert!(!validate(&source, &plan, &rebuild(bad)));
    let mut bad = good.instructions().to_vec();
    bad[0].assignments.swap(4, 5);
    assert!(!validate(&source, &plan, &rebuild(bad)));
    let mut bad = good.instructions().to_vec();
    bad[0].assignments.remove(6);
    assert!(!validate(&source, &plan, &rebuild(bad)));
    let mut bad = good.instructions().to_vec();
    bad[0].control = Control::Return(c(0));
    assert!(!validate(&source, &plan, &rebuild(bad)));
    let mut other = source.instructions()[0].assignments.clone();
    other[2].value = b(B::UMulHigh, c(1), r(0));
    assert!(!validate(&make(other), &plan, &good));
}
#[test]
fn independent_arithmetic_captures_share_one_high_product_snapshot() {
    let source = make(vec![
        set(0, c(97)),
        set(1, b(B::UMulHigh, c(0xaaaaaaaaaaaaaaab), r(0))),
        set(2, b(B::Shr, r(1), c(1))),
        set(3, b(B::Shr, r(1), c(2))),
    ]);
    let plan = ExpressionPlan::analyze(&source).unwrap();
    assert_eq!(plan.evidence().snapshots, 1);
    assert_eq!(plan.evidence().divisions, 2);
    let lowered = plan.lower(&source).unwrap();
    compare(&source, &lowered, &[0; 32], 4096, &[]);
}
#[test]
fn plain_context_remainders_are_selected_before_allocation() {
    let q = b(B::Shr, b(B::UMulHigh, c(0xcccccccccccccccd), r(0)), c(3));
    let source = make(vec![
        set(0, c(u64::MAX)),
        set(2, q),
        store(8, r(2)),
        set(3, b(B::Sub, r(0), b(B::Mul, r(2), c(10)))),
    ]);
    let plan = ExpressionPlan::analyze(&source).unwrap();
    assert_eq!(
        (plan.evidence().snapshots, plan.evidence().remainders),
        (0, 1)
    );
    let lowered = plan.lower(&source).unwrap();
    let mut input = [0; 32];
    input[x86::RDI] = 4096;
    compare(&source, &lowered, &input, 4096, &[0; 32]);
}
#[test]
fn malformed_or_oversized_inputs_decline_without_partial_selection() {
    let p = Program::new(0, 4097, source().instructions().to_vec()).unwrap();
    assert!(ExpressionPlan::analyze(&p).is_none());
    let p = make(vec![set(0, c(1)), set(2, r(0)), set(3, r(0))]);
    assert!(ExpressionPlan::analyze(&p).is_none());
    let mut a = source().instructions()[0].assignments.clone();
    a[2].value = b(
        B::UMulHigh,
        c(0xaaaaaaaaaaaaaaab),
        Expr::load(r(x86::RDI), Width::U64),
    );
    assert!(ExpressionPlan::analyze(&make(a)).is_none());
}
#[test]
fn native_c_uses_captured_values_after_writes_and_preserves_full_memory_faults() {
    const BASE: u64 = 4096;
    const SIZE: usize = 256;
    const FIELDS: usize = 5 + SIZE / 8;
    for (name, source) in [("overwritten", source()), ("loop", loop_source())] {
        let scratch = native::Scratch::new();
        let mut inputs = String::new();
        let mut expected = Vec::new();
        let mut kinds = [0; 3];
        for pointer in [
            BASE,
            BASE + 1,
            BASE + 8,
            BASE + 224,
            BASE + 232,
            BASE + 240,
            BASE + 248,
            BASE + 255,
            0xffff,
            u64::MAX,
        ] {
            for x in [
                0,
                1,
                2,
                3,
                4,
                5,
                (1 << 63) - 1,
                1 << 63,
                u64::MAX - 2,
                u64::MAX - 1,
                u64::MAX,
            ] {
                let words = [x, 17, 19, 23];
                writeln!(
                    inputs,
                    "{pointer} {} {} {} {}",
                    words[0], words[1], words[2], words[3]
                )
                .unwrap();
                let mut memory: Vec<_> = (0..SIZE)
                    .map(|i| i.wrapping_mul(29).wrapping_add(7) as u8)
                    .collect();
                for (index, word) in words.into_iter().enumerate() {
                    if let Some(offset) = pointer
                        .checked_add(index as u64 * 8)
                        .and_then(|p| p.checked_sub(BASE))
                        .filter(|&p| p <= (SIZE - 8) as u64)
                    {
                        memory[offset as usize..offset as usize + 8]
                            .copy_from_slice(&word.to_le_bytes());
                    }
                }
                let mut registers = [0; 32];
                registers[x86::RDI] = pointer;
                registers[x86::RSP] = BASE + SIZE as u64;
                let report = source
                    .run_with_memory(&registers, BASE, &memory, 32)
                    .unwrap();
                let mut row = match report.status {
                    RunStatus::Returned(result) => {
                        kinds[0] += 1;
                        if pointer == BASE {
                            let oracle = if name == "overwritten" {
                                (x / 3) ^ (x % 3) ^ 99
                            } else {
                                (0..3u64)
                                    .map(|i| x.wrapping_add(i))
                                    .fold(0u64, |a, x| a.wrapping_add((x / 3) ^ (x % 3)))
                            };
                            assert_eq!(result, oracle);
                        }
                        vec![0, 0, 0, 0, result]
                    }
                    RunStatus::Fault(f) => {
                        let access = match f.access {
                            nirvana::ir::AccessKind::Read => 1,
                            _ => 2,
                        };
                        kinds[access] += 1;
                        vec![1, f.address, access as u64, f.width.bytes() as u64, 0]
                    }
                    _ => panic!("straight-line source suspended"),
                };
                row.extend(
                    report
                        .state
                        .memory
                        .chunks_exact(8)
                        .map(|w| u64::from_le_bytes(w.try_into().unwrap())),
                );
                expected.push(row);
            }
        }
        assert!(kinds[0] > 0 && kinds[1] > 0);
        if name == "overwritten" {
            assert!(kinds[2] > 0);
        }
        for coalesce in [false, true] {
            for recover_objects in [false, true] {
                let output = readable::emit_readable_c_with_options(
                    &source,
                    readable::ReadableOptions {
                        stack_register: Some(Reg(x86::RSP)),
                        coalesce_locals: coalesce,
                        recover_objects,
                        compact_memory: true,
                    },
                )
                .unwrap();
                assert!(
                    output.expression_evidence.is_some(),
                    "{name}, coalesce={coalesce}: {}\n{:#?}",
                    output.code,
                    nirvana::reduce::reduce(&source)
                        .unwrap()
                        .program()
                        .instructions()
                );
                assert!(
                    !output.code.contains("nirvana_umul_high"),
                    "{}",
                    output.code
                );
                assert!(output.code.contains(" / 3"), "{}", output.code);
                let harness = checked_c::source_with_size(&output, 32, 4, SIZE);
                for opt in ["-O0", "-O2"] {
                    let path = scratch.0.join(format!(
                        "captured-{name}-{coalesce}-{recover_objects}{opt}.c"
                    ));
                    std::fs::write(&path, &harness).unwrap();
                    let obj = path.with_extension("o");
                    let bin = path.with_extension("bin");
                    native::object(&path, &obj, opt, "nirvana_readable");
                    native::link(&[&obj], &bin);
                    assert_eq!(
                        native::run_fields(&bin, &inputs, FIELDS),
                        expected,
                        "coalesce={coalesce},objects={recover_objects},opt={opt}"
                    );
                }
            }
        }
    }
}

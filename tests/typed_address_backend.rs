//! Compare address display with machine IR, including overlapping input/stack,
//! overwritten address producers, destination faults and successful writes.
#[path = "support/checked_c.rs"]
#[allow(dead_code)]
mod checked_c;
#[path = "support/native.rs"]
#[allow(dead_code)]
mod native;
use nirvana::ir::{
    AccessKind, Assignment, BinaryOp as B, Control, Expr, IrInstruction, Place, Program, Reg,
    RunStatus, Width,
};
use nirvana::readable::{ReadableOptions, emit_readable_c_with_options};
use nirvana::{frontend, x86};
use std::fmt::Write as _;
const BASE: u64 = 4096;
const SIZE: usize = 128;
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
fn indexed(base: usize, index: usize) -> Expr {
    b(B::Add, r(base), b(B::Mul, b(B::And, r(index), c(7)), c(4)))
}
fn captured_address() -> Program {
    Program::new(
        0,
        32,
        vec![IrInstruction {
            address: 0,
            size: 1,
            assignments: vec![
                set(20, Expr::load(r(x86::RDI), Width::U64)),
                set(21, Expr::load(b(B::Add, r(x86::RDI), c(8)), Width::U64)),
                set(22, indexed(21, 20)),
                set(20, b(B::Add, r(20), c(1))),
                set(21, Expr::load(b(B::Add, r(x86::RDI), c(16)), Width::U64)),
                Assignment {
                    destination: Place::Memory {
                        address: r(22),
                        width: Width::U32,
                    },
                    value: Expr::load(indexed(21, 20), Width::U32),
                },
            ],
            control: Control::Return(Expr::load(r(22), Width::U32)),
        }],
    )
    .unwrap()
}
fn lazy_address() -> Program {
    // A syntactic Load in the unselected address arm must stay lazy. The
    // address recognizer must decline this even if the arm is rarely chosen.
    let base = Expr::Select {
        condition: Box::new(b(B::And, r(20), c(1))),
        taken: Box::new(r(21)),
        not_taken: Box::new(Expr::load(c(u64::MAX), Width::U64)),
    };
    Program::new(
        0,
        32,
        vec![IrInstruction {
            address: 0,
            size: 1,
            assignments: vec![
                set(20, Expr::load(r(x86::RDI), Width::U64)),
                set(21, Expr::load(b(B::Add, r(x86::RDI), c(8)), Width::U64)),
                Assignment {
                    destination: Place::Memory {
                        address: b(B::Add, base, b(B::Mul, b(B::And, r(20), c(3)), c(4))),
                        width: Width::U32,
                    },
                    value: Expr::load(b(B::Add, r(x86::RDI), c(24)), Width::U64),
                },
            ],
            control: Control::Return(r(20)),
        }],
    )
    .unwrap()
}

fn checked_store() -> Program {
    // Destination and RHS can both fault. A view must still check the entire
    // destination before reading the second pointer or any RHS guest bytes.
    Program::new(
        0,
        32,
        vec![IrInstruction {
            address: 0,
            size: 1,
            assignments: vec![
                set(20, Expr::load(r(x86::RDI), Width::U64)),
                set(21, Expr::load(b(B::Add, r(x86::RDI), c(8)), Width::U64)),
                Assignment {
                    destination: Place::Memory {
                        address: indexed(21, 20),
                        width: Width::U32,
                    },
                    value: Expr::load(
                        b(
                            B::Add,
                            Expr::load(b(B::Add, r(x86::RDI), c(16)), Width::U64),
                            b(B::Mul, b(B::And, r(20), c(7)), c(4)),
                        ),
                        Width::U32,
                    ),
                },
            ],
            control: Control::Return(Expr::load(indexed(21, 20), Width::U32)),
        }],
    )
    .unwrap()
}

fn compare(program: &Program, label: &str, expect_typed_array: bool) -> usize {
    let scratch = native::Scratch::new();
    let original = program.instructions().to_vec();
    let mut text = String::new();
    let mut expected = Vec::new();
    let mut kinds = [0; 3];
    for record in [
        BASE - 1,
        BASE,
        BASE + 1,
        BASE + 80,
        BASE + 104,
        BASE + 120,
        u64::MAX,
    ] {
        for pointer in [
            0,
            BASE - 1,
            BASE,
            BASE + 8,
            BASE + 31,
            BASE + 96,
            BASE + 124,
            u64::MAX,
        ] {
            for index in [0, 1, 2, 7, 8, (1 << 32) + 3, 1 << 63, u64::MAX] {
                let input = [index, pointer, pointer.wrapping_add(4), u64::MAX];
                let mut memory: Vec<_> = (0..SIZE)
                    .map(|i| i.wrapping_mul(29).wrapping_add(7) as u8)
                    .collect();
                for (i, word) in input.into_iter().enumerate() {
                    if let Some(offset) = record
                        .checked_add(i as u64 * 8)
                        .and_then(|p| p.checked_sub(BASE))
                        .filter(|&p| p <= (SIZE - 8) as u64)
                    {
                        memory[offset as usize..offset as usize + 8]
                            .copy_from_slice(&word.to_le_bytes());
                    }
                }
                let mut registers = vec![0; program.register_count()];
                registers[x86::RDI] = record;
                registers[x86::RSP] = BASE + SIZE as u64;
                let report = program
                    .run_with_memory(&registers, BASE, &memory, 10000)
                    .unwrap();
                let mut row = match report.status {
                    RunStatus::Returned(value) => {
                        kinds[0] += 1;
                        vec![0, 0, 0, 0, value]
                    }
                    RunStatus::Fault(f) => {
                        let kind = if f.access == AccessKind::Read { 1 } else { 2 };
                        kinds[kind] += 1;
                        vec![1, f.address, kind as u64, f.width.bytes() as u64, 0]
                    }
                    RunStatus::Suspended => panic!("bounded address case suspended: {label}"),
                };
                row.extend(
                    report
                        .state
                        .memory
                        .chunks_exact(8)
                        .map(|w| u64::from_le_bytes(w.try_into().unwrap())),
                );
                expected.push(row);
                writeln!(
                    text,
                    "{record} {} {} {} {}",
                    input[0], input[1], input[2], input[3]
                )
                .unwrap();
            }
        }
    }
    assert!(kinds[0] > 0 && kinds[1] > 0, "{label}: {kinds:?}");
    if label.starts_with("record-update")
        || label == "captured-address"
        || label == "lazy-address"
        || label == "checked-store"
    {
        assert!(kinds[2] > 0, "{label}: no destination-fault coverage");
    }
    let mut comparisons = 0;
    for coalesce_locals in [false, true] {
        for recover_objects in [false, true] {
            for compact_memory in [false, true] {
                let output = emit_readable_c_with_options(
                    program,
                    ReadableOptions {
                        stack_register: Some(Reg(x86::RSP)),
                        recover_objects,
                        coalesce_locals,
                        compact_memory,
                    },
                )
                .unwrap();
                let body = output
                    .code
                    .split_once("uint64_t nirvana_readable(")
                    .unwrap()
                    .1;
                if expect_typed_array && recover_objects && !coalesce_locals {
                    assert!(
                        output
                            .locals
                            .iter()
                            .any(|l| l.address_width == Some(Width::U32)),
                        "{label}: no loaded-pointer type\n{body}"
                    );
                    if compact_memory {
                        assert!(
                            body.contains("read32(element("),
                            "{label}: no dynamic array view\n{body}"
                        );
                    }
                }
                if !recover_objects {
                    assert!(output.locals.iter().all(|l| l.address_width.is_none()));
                }
                for local in &output.locals {
                    if local.address_width.is_some() {
                        assert_eq!(local.width, Width::U64);
                    }
                }
                let harness =
                    checked_c::source_with_size(&output, program.register_count(), 4, SIZE);
                for copt in ["-O0", "-O2"] {
                    let source = scratch.0.join(format!(
                        "{coalesce_locals}-{recover_objects}-{compact_memory}{copt}.c"
                    ));
                    std::fs::write(&source, &harness).unwrap();
                    let object = source.with_extension("o");
                    let bin = source.with_extension("bin");
                    native::object(&source, &object, copt, "nirvana_readable");
                    native::link(&[&object], &bin);
                    assert_eq!(
                        native::run_fields(&bin, &text, 5 + SIZE / 8),
                        expected,
                        "{label}: storage={coalesce_locals}, views={recover_objects}, compact={compact_memory}, C={copt}"
                    );
                    comparisons += expected.len();
                }
            }
        }
    }
    assert_eq!(program.instructions(), original);
    println!(
        "{label}: {comparisons} return/full128-byte/first-fault comparisons, source outcomes={kinds:?}"
    );
    comparisons
}

#[test]
fn loaded_pointer_arrays_preserve_machine_behavior_under_native_c_optimization() {
    let scratch = native::Scratch::new();
    let mut comparisons = 0;
    for name in ["record-index", "record-update"] {
        for opt in ["-O0", "-O2"] {
            let object = scratch.0.join(format!("{name}{opt}.o"));
            native::object(
                &native::fixture_root().join(format!("types/{name}.c")),
                &object,
                opt,
                "fixture",
            );
            let lifted = frontend::lift_elf(&std::fs::read(object).unwrap(), "fixture").unwrap();
            comparisons += compare(
                &lifted.program,
                &format!("{name}{opt}"),
                name == "record-index" && opt == "-O2",
            );
        }
    }
    assert_eq!(comparisons, 28672);
}

#[test]
fn current_operands_and_lazy_address_loads_survive_display_views() {
    assert_eq!(
        compare(&captured_address(), "captured-address", false),
        7168
    );
    assert_eq!(compare(&lazy_address(), "lazy-address", false), 7168);
    assert_eq!(compare(&checked_store(), "checked-store", false), 7168);
}

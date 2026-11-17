//! Check the point-aware arithmetic view through the real C printer.
#[allow(dead_code)]
#[path = "support/checked_c.rs"]
mod checked_c;
#[allow(dead_code)]
#[path = "support/native.rs"]
mod native;

use nirvana::ir::{
    AccessKind, Assignment, BinaryOp as B, Control, Expr, IrInstruction, Program, Reg, RunStatus,
    Width,
};
use nirvana::readable::{ReadableOptions, emit_readable_c_with_options};
use nirvana::x86;
use std::fmt::Write as _;
use std::process::Command;

const BASE: u64 = 4096;
const SIZE: usize = 64;
fn r(index: usize) -> Expr {
    Expr::Register(Reg(index))
}
fn c(value: u64) -> Expr {
    Expr::Const(value)
}
fn b(op: B, left: Expr, right: Expr) -> Expr {
    Expr::binary(op, left, right)
}
fn set(index: usize, value: Expr) -> Assignment {
    Assignment {
        destination: Reg(index).into(),
        value,
    }
}
fn store(offset: u64, value: Expr) -> Assignment {
    Assignment {
        destination: nirvana::ir::Place::Memory {
            address: b(B::Add, r(x86::RDI), c(offset)),
            width: Width::U64,
        },
        value,
    }
}
fn program(kind: usize, divisor: u64) -> Program {
    let value = match kind {
        1 => b(B::Add, r(0), c(u64::MAX)),
        2 => Expr::select(
            b(B::Ult, r(0), c(1 << 63)),
            b(B::Add, r(0), c(17)),
            b(B::Sub, r(0), c(5)),
        ),
        _ => r(0),
    };
    let (magic, shift) = if divisor == 10 {
        (0xcccc_cccc_cccc_cccd, 3)
    } else {
        (u64::MAX, 63)
    };
    let quotient = b(B::Shr, b(B::UMulHigh, value.clone(), c(magic)), c(shift));
    let mut assignments = vec![
        set(0, Expr::load(r(x86::RDI), Width::U64)),
        set(1, quotient.clone()),
        // Alias the original input for the Select case. The captured register
        // remains stable even when its old guest-memory location changes.
        store(if kind == 2 { 0 } else { 8 }, r(1)),
    ];
    match kind {
        4 => assignments.push(set(0, b(B::Add, r(0), c(1)))),
        5 => assignments.push(set(1, b(B::Add, r(1), c(1)))),
        6 => assignments.push(set(0, Expr::load(b(B::Add, r(x86::RDI), c(8)), Width::U64))),
        _ => {}
    }
    let q = if kind == 3 { quotient } else { r(1) };
    assignments.push(set(2, b(B::Sub, value, b(B::Mul, q, c(divisor)))));
    assignments.push(store(16, r(2)));
    Program::new(
        0,
        x86::REGISTER_COUNT,
        vec![IrInstruction {
            address: 0,
            size: 1,
            assignments,
            control: Control::Return(b(B::Xor, r(1), r(2))),
        }],
    )
    .unwrap()
}
fn prepare(address: u64, input: [u64; 4]) -> Vec<u8> {
    let mut memory: Vec<_> = (0..SIZE).map(|i| (i * 29 + 7) as u8).collect();
    for (index, word) in input.into_iter().enumerate() {
        if let Some(offset) = address
            .checked_add(index as u64 * 8)
            .and_then(|a| a.checked_sub(BASE))
            && offset <= (SIZE - 8) as u64
        {
            let offset = offset as usize;
            memory[offset..offset + 8].copy_from_slice(&word.to_le_bytes());
        }
    }
    memory
}

#[test]
fn context_and_raw_remainders_keep_c_types_aliases_faults_and_stale_facts() {
    let scratch = native::Scratch::new();
    let values = [
        0,
        1,
        2,
        9,
        10,
        11,
        19,
        20,
        21,
        99,
        100,
        101,
        (1 << 63) - 1,
        1 << 63,
        (1 << 63) + 1,
        u64::MAX - 1,
        u64::MAX,
    ];
    let addresses = [
        BASE,
        BASE + 1,
        BASE + 8,
        BASE + 40,
        BASE + 48,
        BASE + 56,
        BASE + 63,
        0xffff,
        u64::MAX,
    ];
    let cases = [
        (0, 10),
        (1, 10),
        (2, 10),
        (0, (1 << 63) + 1),
        (1, (1 << 63) + 1),
        (2, (1 << 63) + 1),
        (3, 10),
        (4, 10),
        (5, 10),
        (6, 10),
    ];
    let mut comparisons = 0;
    for (kind, divisor) in cases {
        let program = program(kind, divisor);
        let original = program.instructions().to_vec();
        let mut input_text = String::new();
        let mut expected = Vec::new();
        for address in addresses {
            for value in values {
                let input = [value, u64::MAX, 1 << 63, 0xdead_beef];
                writeln!(
                    input_text,
                    "{address} {} {} {} {}",
                    input[0], input[1], input[2], input[3]
                )
                .unwrap();
                let mut registers = vec![0; program.register_count()];
                registers[x86::RDI] = address;
                registers[x86::RSP] = BASE + SIZE as u64;
                let report = program
                    .run_with_memory(&registers, BASE, &prepare(address, input), 10)
                    .unwrap();
                let mut row = match report.status {
                    RunStatus::Returned(value) => vec![0, 0, 0, 0, value],
                    RunStatus::Fault(fault) => vec![
                        1,
                        fault.address,
                        if fault.access == AccessKind::Read {
                            1
                        } else {
                            2
                        },
                        fault.width.bytes() as u64,
                        0,
                    ],
                    RunStatus::Suspended => panic!("single instruction suspended"),
                };
                row.extend(
                    report
                        .state
                        .memory
                        .chunks_exact(8)
                        .map(|word| u64::from_le_bytes(word.try_into().unwrap())),
                );
                expected.push(row);
            }
        }
        for compact in [false, true] {
            let output = emit_readable_c_with_options(
                &program,
                ReadableOptions {
                    compact_memory: compact,
                    coalesce_locals: compact,
                    recover_objects: compact,
                    ..ReadableOptions::default()
                },
            )
            .unwrap();
            let body = output
                .code
                .split("uint64_t nirvana_readable(")
                .nth(1)
                .unwrap();
            assert_eq!(
                body.contains(" % ") || body.contains(" %="),
                kind < 4,
                "kind={kind}, divisor={divisor}, compact={compact}\n{body}"
            );
            let source = checked_c::source(&output, program.register_count(), 4);
            for (optimization, sanitize) in [("-O0", false), ("-O2", false), ("-O2", true)] {
                let path = scratch.0.join(format!("context-{comparisons}.c"));
                std::fs::write(&path, &source).unwrap();
                let object = path.with_extension("o");
                let binary = path.with_extension("bin");
                if sanitize {
                    let result = Command::new("cc")
                        .args([
                            "-std=c11",
                            "-Wall",
                            "-Wextra",
                            "-Werror",
                            "-pedantic",
                            "-fno-lto",
                            optimization,
                            "-fsanitize=undefined",
                            "-fno-sanitize-recover=all",
                        ])
                        .arg(&path)
                        .arg("-o")
                        .arg(&binary)
                        .output()
                        .unwrap();
                    assert!(
                        result.status.success(),
                        "{}",
                        String::from_utf8_lossy(&result.stderr)
                    );
                } else {
                    native::object(&path, &object, optimization, "nirvana_readable");
                    native::link(&[&object], &binary);
                }
                assert_eq!(
                    native::run_fields(&binary, &input_text, 5 + SIZE / 8),
                    expected,
                    "kind={kind}, divisor={divisor}, compact={compact}, {optimization}"
                );
                comparisons += expected.len();
            }
        }
        assert_eq!(program.instructions(), original);
    }
    assert_eq!(comparisons, 9180);
}

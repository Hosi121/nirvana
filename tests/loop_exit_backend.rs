//! Returning loop tails through actual O2 machine code and adverse guest memory.
//! Compare return, every guest byte, and the first fault's address/kind/width.
#[path = "support/checked_c.rs"]
mod checked_c;
#[allow(dead_code)]
#[path = "support/native.rs"]
mod native;

use nirvana::ir::{
    AccessKind, Assignment, BinaryOp, Control, Expr, IrInstruction, Place, Program, Reg, RunStatus,
    Width,
};
use nirvana::readable::{ReadableOptions, emit_readable_c_with_options};
use nirvana::{frontend, x86};
use std::fmt::Write as _;

fn compare(program: &Program, cases: &[(u64, [u64; 4])], label: &str) {
    let scratch = native::Scratch::new();
    let mut input = String::new();
    let mut expected = Vec::new();
    for &(address, words) in cases {
        writeln!(
            input,
            "{address} {} {} {} {}",
            words[0], words[1], words[2], words[3]
        )
        .unwrap();
        let mut memory: Vec<_> = (0..64usize)
            .map(|i| i.wrapping_mul(29).wrapping_add(7) as u8)
            .collect();
        for (index, value) in words.into_iter().enumerate() {
            if let Some(offset) = address
                .checked_add(index as u64 * 8)
                .and_then(|a| a.checked_sub(4096))
                && offset <= 56
            {
                memory[offset as usize..offset as usize + 8].copy_from_slice(&value.to_le_bytes());
            }
        }
        let mut registers = vec![0; program.register_count()];
        registers[x86::RDI] = address;
        registers[x86::RSP] = 4160;
        let report = program
            .run_with_memory(&registers, 4096, &memory, 100_000)
            .unwrap();
        let mut row = match report.status {
            RunStatus::Returned(value) => vec![0, 0, 0, 0, value],
            RunStatus::Fault(f) => vec![
                1,
                f.address,
                if f.access == AccessKind::Read { 1 } else { 2 },
                f.width.bytes() as u64,
                0,
            ],
            RunStatus::Suspended => panic!("{label} unexpectedly suspended"),
        };
        row.extend(
            report
                .state
                .memory
                .chunks_exact(8)
                .map(|bytes| u64::from_le_bytes(bytes.try_into().unwrap())),
        );
        expected.push(row);
    }
    for views in [false, true] {
        let output = emit_readable_c_with_options(
            program,
            ReadableOptions {
                stack_register: Some(Reg(x86::RSP)),
                recover_objects: views,
                coalesce_locals: true,
                compact_memory: true,
            },
        )
        .unwrap();
        let body = output
            .code
            .split("uint64_t nirvana_readable(")
            .nth(1)
            .unwrap();
        assert!(body.contains("} while ("), "{label}: {body}");
        assert!(!body.contains("for (;;)"), "{label}: {body}");
        let source_text = checked_c::source(&output, program.register_count(), 4);
        for opt in ["-O0", "-O2"] {
            let source = scratch.0.join(format!("{label}-{views}{opt}.c"));
            std::fs::write(&source, &source_text).unwrap();
            let object = source.with_extension("o");
            let binary = source.with_extension("bin");
            native::object(&source, &object, opt, "nirvana_readable");
            native::link(&[&object], &binary);
            assert_eq!(
                native::run_fields(&binary, &input, 13),
                expected,
                "{label}, views={views}, {opt}"
            );
        }
    }
}

#[test]
fn actual_o2_returning_loop_tail_keeps_first_fault_and_every_guest_byte() {
    let scratch = native::Scratch::new();
    let object = scratch.0.join("branch-break.o");
    native::object(
        &native::fixture_root().join("recovery/branch-break.c"),
        &object,
        "-O2",
        "fixture",
    );
    let lifted = frontend::lift_elf(&std::fs::read(object).unwrap(), "fixture").unwrap();
    let words: Vec<[u64; 4]> = include_str!("fixtures/inputs.tsv")
        .lines()
        .filter(|line| !line.is_empty() && !line.starts_with('#'))
        .map(|line| {
            line.split('\t')
                .skip(1)
                .map(|word| word.parse().unwrap())
                .collect::<Vec<_>>()
                .try_into()
                .unwrap()
        })
        .collect();
    assert_eq!(words.len(), 63);
    let cases: Vec<_> = [4096, 4097, 4112, 4136, 4159, u64::MAX]
        .into_iter()
        .flat_map(|address| words.iter().map(move |&words| (address, words)))
        .collect();
    assert_eq!(cases.len(), 378);
    compare(&lifted.program, &cases, "branch-break");
}

#[test]
fn inverted_nonboolean_latch_keeps_destination_check_rhs_and_return_faults_in_order() {
    let r = |id| Expr::Register(Reg(id));
    let c = Expr::Const;
    let b = Expr::binary;
    let set = |id, value| Assignment {
        destination: Place::Register(Reg(id)),
        value,
    };
    let store = |address, width, value| Assignment {
        destination: Place::Memory { address, width },
        value,
    };
    let instruction = |address, assignments, control| IrInstruction {
        address,
        size: 1,
        assignments,
        control,
    };
    let program = Program::new(
        0,
        8,
        vec![
            instruction(
                0,
                vec![
                    set(
                        0,
                        b(
                            BinaryOp::Add,
                            b(BinaryOp::And, Expr::load(r(7), Width::U64), c(3)),
                            c(1),
                        ),
                    ),
                    set(
                        1,
                        b(
                            BinaryOp::Or,
                            Expr::load(b(BinaryOp::Add, r(7), c(8)), Width::U64),
                            c(2),
                        ),
                    ),
                    set(4, Expr::load(b(BinaryOp::Add, r(7), c(16)), Width::U64)),
                    set(5, Expr::load(b(BinaryOp::Add, r(7), c(24)), Width::U64)),
                    set(2, c(0)),
                ],
                Control::Next,
            ),
            instruction(
                1,
                vec![
                    set(2, b(BinaryOp::Add, r(2), c(1))),
                    store(c(4159), Width::U8, r(2)),
                    set(3, Expr::select(b(BinaryOp::Ult, r(2), r(0)), c(0), r(1))),
                ],
                Control::Branch {
                    condition: r(3),
                    target: 3,
                },
            ),
            instruction(2, vec![], Control::Jump(1)),
            instruction(
                3,
                vec![
                    store(
                        r(4),
                        Width::U16,
                        b(BinaryOp::Add, Expr::load(r(5), Width::U8), r(2)),
                    ),
                    store(c(4158), Width::U8, c(0xa5)),
                ],
                Control::Return(b(BinaryOp::Add, Expr::load(r(5), Width::U32), r(2))),
            ),
        ],
    )
    .unwrap();
    let mut cases = Vec::new();
    for limit in [0, 1, 3] {
        for raw in [0, 2, u64::MAX] {
            for write in [4144, 4159, u64::MAX] {
                for read in [4144, 4159, u64::MAX] {
                    cases.push((4096, [limit, raw, write, read]));
                }
            }
        }
    }
    assert_eq!(cases.len(), 81);
    compare(&program, &cases, "inverted-latch");
}

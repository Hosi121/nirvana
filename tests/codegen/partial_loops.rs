//! Partial natural-loop fallback with residual irreducible edges and lazy faults.
use crate::support::{checked_c, native};
use nirvana::ir::{
    AccessKind, Assignment, BinaryOp, Control, Expr, IrInstruction, Place, Program, Reg, RunStatus,
    Width,
};
use nirvana::readable::{ReadableOptions, emit_readable_c_with_options};
use nirvana::{structure::StructuredFunction, x86};
use std::fmt::Write as _;

fn program() -> Program {
    let r = |index| Expr::Register(Reg(index));
    let k = Expr::Const;
    let add = |a, b| Expr::binary(BinaryOp::Add, a, b);
    let assign = |index, value| Assignment {
        destination: Reg(index).into(),
        value,
    };
    let address = |offset| add(r(x86::RDI), k(offset));
    let mut instructions = vec![IrInstruction {
        address: 0,
        size: 1,
        assignments: vec![
            assign(
                0,
                Expr::binary(BinaryOp::And, Expr::load(address(0), Width::U64), k(7)),
            ),
            assign(2, Expr::load(address(8), Width::U64)),
            assign(4, Expr::load(address(24), Width::U64)),
        ],
        control: Control::Jump(10),
    }];
    for pc in 0..6 {
        let mut assignments = vec![];
        if pc < 5 {
            assignments.push(assign(
                0,
                Expr::select(r(0), Expr::binary(BinaryOp::Sub, r(0), k(1)), k(0)),
            ));
            assignments.push(assign(2, add(r(2), k(pc + 1))));
        }
        if pc == 2 || pc == 4 {
            assignments.push(Assignment {
                destination: Place::Memory {
                    address: address(16 + u64::from(pc == 4)),
                    width: Width::U8,
                },
                value: if pc == 2 {
                    r(2)
                } else {
                    Expr::load(add(r(x86::RDI), r(4)), Width::U8)
                },
            });
        }
        instructions.push(IrInstruction {
            address: 10 + pc,
            size: 1,
            assignments,
            control: if pc == 5 {
                Control::Return(add(r(2), Expr::load(address(16), Width::U16)))
            } else {
                Control::Branch {
                    condition: Expr::select(
                        r(0),
                        Expr::load(add(r(x86::RDI), r(4)), Width::U8),
                        k(0),
                    ),
                    target: 10 + [3, 4, 1, 0, 2][pc as usize],
                }
            },
        });
    }
    Program::new(0, 80, instructions).unwrap()
}

#[test]
fn irreducible_inner_edges_keep_the_outer_loop_and_exact_fault_memory_behavior() {
    let program = program();
    assert!(StructuredFunction::recover(&program).is_err());
    let mut input = String::new();
    let mut expected = Vec::new();
    for address in [4096u64, 4128, 4095, 4160, u64::MAX] {
        for count in [0, 1, 2, 7] {
            for offset in [0, 16, 17, 64, u64::MAX] {
                let words = [count, u64::MAX - 15, 0x1234, offset];
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
                        memory[offset as usize..offset as usize + 8]
                            .copy_from_slice(&value.to_le_bytes());
                    }
                }
                let mut registers = vec![0; 80];
                registers[x86::RDI] = address;
                registers[x86::RSP] = 4160;
                let report = program
                    .run_with_memory(&registers, 4096, &memory, 1000)
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
                    RunStatus::Suspended => panic!("bounded counter did not terminate"),
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
        }
    }
    let scratch = native::Scratch::new();
    for views in [false, true] {
        let output = emit_readable_c_with_options(
            &program,
            ReadableOptions {
                recover_objects: views,
                compact_memory: true,
                ..ReadableOptions::default()
            },
        )
        .unwrap();
        assert!(output.structure_stats.is_none());
        let body = output
            .code
            .split("uint64_t nirvana_readable(")
            .nth(1)
            .unwrap();
        assert!(body.contains("for (;;)"), "{body}");
        assert!(body.contains("goto bb"), "{body}");
        let text = checked_c::source(&output, 80, 4);
        for opt in ["-O0", "-O2"] {
            let source = scratch.0.join(format!("partial-loops-{views}{opt}.c"));
            std::fs::write(&source, &text).unwrap();
            let object = source.with_extension("o");
            let binary = source.with_extension("bin");
            native::object(&source, &object, opt, "nirvana_readable");
            native::link(&[&object], &binary);
            assert_eq!(
                native::run_fields(&binary, &input, 13),
                expected,
                "views={views} {opt}"
            );
        }
    }
}

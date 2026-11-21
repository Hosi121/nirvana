//! Statement-form header setup: final visits, continues, aliasing and lazy faults.
use crate::support::checked_c;
use crate::support::loop_headers;
use crate::support::native;

use nirvana::ir::{
    Assignment, BinaryOp as B, Control, Expr, IrInstruction, Place, Program, Reg, RunStatus, Width,
};
use nirvana::readable::{ReadableOptions, emit_readable_c_with_options};
use nirvana::x86;
use std::fmt::Write;

const BASE: u64 = 4096;
const SIZE: usize = 128;
use crate::support::ir::c;
use crate::support::ir::r;
fn b(op: B, a: Expr, z: Expr) -> Expr {
    Expr::binary(op, a, z)
}
fn load(a: Expr) -> Expr {
    Expr::load(a, Width::U64)
}
fn set(n: usize, value: Expr) -> Assignment {
    Assignment {
        destination: Reg(n).into(),
        value,
    }
}
fn store(a: Expr, value: Expr) -> Assignment {
    Assignment {
        destination: Place::Memory {
            address: a,
            width: Width::U64,
        },
        value,
    }
}
fn ins(address: u64, assignments: Vec<Assignment>, control: Control) -> IrInstruction {
    IrInstruction {
        address,
        size: 1,
        assignments,
        control,
    }
}

fn source(kind: usize) -> Program {
    let read = if kind == 1 {
        Expr::select(b(B::And, r(22), c(1)), load(r(21)), c(7))
    } else {
        load(r(21))
    };
    let mut header = vec![set(23, read)];
    if kind == 2 {
        header.push(set(24, load(b(B::Add, r(21), c(8)))));
    } else {
        header.push(set(24, b(B::Add, r(23), r(22))));
    }
    header.push(set(25, b(B::Add, r(21), c(8))));
    Program::new(
        0,
        32,
        vec![
            ins(
                0,
                vec![
                    set(20, b(B::And, load(r(x86::RDI)), c(3))),
                    set(21, load(b(B::Add, r(x86::RDI), c(8)))),
                    set(22, c(0)),
                ],
                Control::Jump(10),
            ),
            ins(
                10,
                header,
                Control::Branch {
                    condition: b(B::Ult, r(22), r(20)),
                    target: 20,
                },
            ),
            ins(
                11,
                vec![],
                Control::Return(load(b(B::Add, r(x86::RDI), c(16)))),
            ),
            ins(
                20,
                vec![
                    store(b(B::Add, r(x86::RDI), c(16)), r(24)),
                    set(21, r(25)),
                    set(22, b(B::Add, r(22), c(1))),
                ],
                Control::Branch {
                    condition: b(B::And, r(23), c(1)),
                    target: 10,
                },
            ),
            ins(
                21,
                vec![store(b(B::Add, r(x86::RDI), c(24)), r(23))],
                Control::Jump(10),
            ),
        ],
    )
    .unwrap()
}

fn memory(address: u64, input: &[u64; 4]) -> Vec<u8> {
    let mut bytes: Vec<_> = (0..SIZE).map(|i| (i * 29 + 7) as u8).collect();
    for (word, value) in input.iter().enumerate() {
        if let Some(location) = address.checked_add(word as u64 * 8)
            && let Some(offset) = location.checked_sub(BASE)
            && offset <= (SIZE - 8) as u64
        {
            bytes[offset as usize..offset as usize + 8].copy_from_slice(&value.to_le_bytes());
        }
    }
    bytes
}

#[test]
fn header_statements_preserve_final_faults_continues_and_every_guest_byte() {
    let scratch = native::Scratch::new();
    let addresses = [
        BASE,
        BASE + 1,
        BASE + 64,
        BASE + SIZE as u64 - 32,
        BASE + SIZE as u64 - 8,
        BASE - 1,
        u64::MAX,
    ];
    let pointers = [
        BASE + 32,
        BASE + 16,
        BASE + SIZE as u64 - 8,
        BASE + SIZE as u64,
        BASE - 1,
    ];
    let mut total = 0;
    let mut final_faults = 0;
    for kind in 0..3 {
        let program = source(kind);
        let original = program.instructions().to_vec();
        let mut text = String::new();
        let mut expected = Vec::new();
        let mut returns = 0;
        for address in addresses {
            for count in 0..4 {
                for pointer in pointers {
                    let input = [count, pointer, 0xabc, 0xdef];
                    writeln!(
                        text,
                        "{address} {} {} {} {}",
                        input[0], input[1], input[2], input[3]
                    )
                    .unwrap();
                    let mut regs = vec![0; program.register_count()];
                    regs[x86::RDI] = address;
                    regs[x86::RSP] = BASE + SIZE as u64;
                    let report = program
                        .run_with_memory(&regs, BASE, &memory(address, &input), 1000)
                        .unwrap();
                    let mut row = match report.status {
                        RunStatus::Returned(value) => {
                            returns += 1;
                            vec![0, 0, 0, 0, value]
                        }
                        RunStatus::Fault(fault) => {
                            if kind == 0
                                && address == BASE
                                && count == 1
                                && pointer == BASE + SIZE as u64 - 8
                            {
                                // Body writes survive the load on the final
                                // header visit, even though its test is false.
                                assert_eq!(fault.address, BASE + SIZE as u64);
                                assert_ne!(
                                    u64::from_le_bytes(
                                        report.state.memory[16..24].try_into().unwrap()
                                    ),
                                    0xabc
                                );
                                final_faults += 1;
                            }
                            vec![
                                1,
                                fault.address,
                                if fault.access == nirvana::ir::AccessKind::Read {
                                    1
                                } else {
                                    2
                                },
                                fault.width.bytes() as u64,
                                0,
                            ]
                        }
                        other => panic!("unexpected outcome:{other:?}"),
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
        }
        assert!(returns > 0 && returns < expected.len());
        for recover_objects in [false, true] {
            for coalesce_locals in [false, true] {
                let output = emit_readable_c_with_options(
                    &program,
                    ReadableOptions {
                        stack_register: Some(Reg(x86::RSP)),
                        recover_objects,
                        coalesce_locals,
                        compact_memory: true,
                    },
                )
                .unwrap();
                assert!(
                    !loop_headers::assert_pure_conditions(&output.code).is_empty(),
                    "fixture must exercise a rendered loop"
                );
                assert_eq!(program.instructions(), original);
                let path = scratch.0.join(format!(
                    "header-{kind}-{recover_objects}-{coalesce_locals}.c"
                ));
                std::fs::write(
                    &path,
                    checked_c::source_with_size(&output, program.register_count(), 4, SIZE),
                )
                .unwrap();
                for opt in ["-O0", "-O2"] {
                    let object = path.with_extension("o");
                    let binary = path.with_extension("bin");
                    native::object(&path, &object, opt, "fixture");
                    native::link(&[&object], &binary);
                    assert_eq!(
                        native::run_fields(&binary, &text, 5 + SIZE / 8),
                        expected,
                        "kind={kind},views={recover_objects},coalescing={coalesce_locals},{opt}"
                    );
                    total += expected.len();
                }
            }
        }
    }
    assert_eq!(final_faults, 1);
    assert_eq!(total, 3360);
    eprintln!(
        "{total} statement-header C comparisons: return/fault metadata and every128 guest bytes"
    );
}

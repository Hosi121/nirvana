//! Checked C backend regression for signed-order helper presentation.
//!
//! Original lifted IR is authoritative, including O0 stack/input aliasing.
//! Source C is never run on these guest addresses. Compare return, all 256 guest
//! bytes and the first fault's address/access/width. Instruction traces and the
//! final machine register file are separate IR observations.

#[allow(dead_code)]
#[path = "support/checked_c.rs"]
mod checked_c;
#[allow(dead_code)]
#[path = "support/native.rs"]
mod native;

use nirvana::ir::{AccessKind, Reg, RunStatus};
use nirvana::readable::{ReadableOptions, emit_readable_c_with_options};
use nirvana::{frontend, x86};
use std::fmt::Write as _;

const BASE: u64 = 0x1000;
const MEMORY_SIZE: usize = 256;
const FIELDS: usize = 5 + MEMORY_SIZE / 8;
const SIGN: u64 = 1 << 63;
const VALUES: [u64; 6] = [0, 1, SIGN - 1, SIGN, SIGN + 1, u64::MAX];
const ADDRESSES: [u64; 12] = [
    BASE,
    BASE + 1,
    BASE + 16,
    BASE + 160,
    BASE + 176,
    BASE + 192,
    BASE + 224,
    BASE + 240,
    BASE + 248,
    BASE + 255,
    0xffff,
    u64::MAX,
];

// Match checked_c::source_with_size(..., 4, MEMORY_SIZE): each word is initialized
// when its individual address addition and full eight-byte access are valid.
fn prepare(address: u64, words: [u64; 4]) -> Vec<u8> {
    let mut memory: Vec<_> = (0..MEMORY_SIZE)
        .map(|index| index.wrapping_mul(29).wrapping_add(7) as u8)
        .collect();
    for (word, value) in words.into_iter().enumerate() {
        if let Some(offset) = address
            .checked_add(word as u64 * 8)
            .and_then(|location| location.checked_sub(BASE))
            && offset <= (MEMORY_SIZE - 8) as u64
        {
            let offset = offset as usize;
            memory[offset..offset + 8].copy_from_slice(&value.to_le_bytes());
        }
    }
    memory
}

#[test]
fn actual_signed_helpers_preserve_full_guest_memory_return_and_first_fault() {
    let scratch = native::Scratch::new();
    let mut compared = 0;
    for name in ["signed-compare", "signed-branch"] {
        for original_optimization in ["-O0", "-O2"] {
            let object = scratch
                .0
                .join(format!("{name}-original{original_optimization}.o"));
            native::object(
                &native::fixture_root().join(format!("recovery/{name}.c")),
                &object,
                original_optimization,
                "fixture",
            );
            let lifted = frontend::lift_elf(&std::fs::read(object).unwrap(), "fixture").unwrap();
            let program = &lifted.program;
            let instructions = program.instructions().to_vec();
            let mut input_text = String::new();
            let mut expected = Vec::new();
            let (mut returns, mut reads, mut writes) = (0, 0, 0);
            let mut base_returns = 0;
            for address in ADDRESSES {
                for left in VALUES {
                    for right in VALUES {
                        let input = [left, right, 0xaaaa_aaaa_aaaa_aaaa, 0x5555_5555_5555_5555];
                        writeln!(
                            input_text,
                            "{address} {} {} {} {}",
                            input[0], input[1], input[2], input[3]
                        )
                        .unwrap();
                        let memory = prepare(address, input);
                        let mut registers = vec![0; program.register_count()];
                        registers[x86::RDI] = address;
                        registers[x86::RSP] = BASE + MEMORY_SIZE as u64;
                        let report = program
                            .run_with_memory(&registers, BASE, &memory, 100_000)
                            .unwrap();
                        if address == BASE {
                            // The source data and O0 stack are disjoint here.
                            // A return traverses the fixture's comparisons,
                            // covering O0 helper execution beyond the prologue.
                            let lt = u64::from((left as i64) < (right as i64));
                            let le = u64::from((left as i64) <= (right as i64));
                            let value = if name == "signed-compare" {
                                lt | (le << 1) | ((1 - le) << 2) | ((1 - lt) << 3)
                            } else {
                                lt | (le << 1)
                            };
                            assert_eq!(report.status, RunStatus::Returned(value));
                            base_returns += 1;
                        }
                        let mut observation = match report.status {
                            RunStatus::Returned(value) => {
                                returns += 1;
                                vec![0, 0, 0, 0, value]
                            }
                            RunStatus::Fault(fault) => {
                                let access = match fault.access {
                                    AccessKind::Read => {
                                        reads += 1;
                                        1
                                    }
                                    AccessKind::Write => {
                                        writes += 1;
                                        2
                                    }
                                };
                                vec![1, fault.address, access, fault.width.bytes() as u64, 0]
                            }
                            RunStatus::Suspended => panic!(
                                "{name}{original_optimization} suspended: address={address:#x}, input={input:?}"
                            ),
                        };
                        observation.extend(
                            report
                                .state
                                .memory
                                .chunks_exact(8)
                                .map(|word| u64::from_le_bytes(word.try_into().unwrap())),
                        );
                        assert_eq!(observation.len(), FIELDS);
                        expected.push(observation);
                    }
                }
            }
            assert_eq!(expected.len(), 432);
            assert_eq!(base_returns, VALUES.len() * VALUES.len());
            assert!(
                returns > 0 && reads > 0 && writes > 0,
                "lost return/read-fault/write-fault coverage in {name}{original_optimization}"
            );
            for recover_objects in [false, true] {
                let output = emit_readable_c_with_options(
                    program,
                    ReadableOptions {
                        stack_register: Some(Reg(x86::RSP)),
                        recover_objects,
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
                assert!(
                    body.contains("nirvana_slt64(") || body.contains("nirvana_sle64("),
                    "helper absent from function body: {name}{original_optimization}, views={recover_objects}\n{body}"
                );
                assert_eq!(program.instructions(), instructions);
                let source =
                    checked_c::source_with_size(&output, program.register_count(), 4, MEMORY_SIZE);
                for generated_optimization in ["-O0", "-O2"] {
                    let stem = format!(
                        "{name}-{original_optimization}-{recover_objects}-{generated_optimization}"
                    );
                    let path = scratch.0.join(format!("{stem}.c"));
                    std::fs::write(&path, &source).unwrap();
                    let object = path.with_extension("o");
                    let binary = path.with_extension("bin");
                    native::object(&path, &object, generated_optimization, "nirvana_readable");
                    native::link(&[&object], &binary);
                    assert_eq!(
                        native::run_fields(&binary, &input_text, FIELDS),
                        expected,
                        "{name} source{original_optimization}, views={recover_objects}, generated{generated_optimization}"
                    );
                    compared += expected.len();
                }
            }
            assert_eq!(program.instructions(), instructions);
            println!(
                "{name} {original_optimization}: 432 IR inputs, returns={returns}, read faults={reads}, write faults={writes}; views off/on and generated O0/O2 agree"
            );
        }
    }
    assert_eq!(compared, 6912);
    println!(
        "signed helper backend: {compared} exact return/full-256-byte/first-fault comparisons"
    );
}

#[test]
#[ignore = "requires NIRVANA_Z3; checked-memory block obligations for shared differences"]
fn shared_difference_reduction_preserves_live_boundaries_and_checked_memory() {
    use nirvana::ir::{
        Assignment, BinaryOp as B, Control, Expr, IrInstruction, Place, Program, Width,
    };
    let solver = nirvana::verify::Solver::new(
        std::env::var_os("NIRVANA_Z3").expect("set NIRVANA_Z3 to the optional solver"),
    );
    let r = |index| Expr::Register(Reg(index));
    let c = Expr::Const;
    let b = Expr::binary;
    let set = |index, value| Assignment {
        destination: Place::Register(Reg(index)),
        value,
    };
    let overflow = b(
        B::Ne,
        b(
            B::And,
            b(B::And, b(B::Xor, r(0), r(1)), b(B::Xor, r(0), r(3))),
            c(SIGN),
        ),
        c(0),
    );
    let instructions = vec![
        IrInstruction {
            address: 0,
            size: 1,
            assignments: vec![set(3, b(B::Sub, r(0), r(1)))],
            control: Control::Next,
        },
        IrInstruction {
            address: 1,
            size: 1,
            assignments: vec![
                set(4, b(B::Shr, r(3), c(63))),
                set(5, overflow),
                set(6, b(B::Xor, r(4), r(5))),
            ],
            control: Control::Next,
        },
        IrInstruction {
            address: 2,
            size: 1,
            assignments: vec![Assignment {
                destination: Place::Memory {
                    address: r(2),
                    width: Width::U8,
                },
                value: r(6),
            }],
            control: Control::Jump(3),
        },
        IrInstruction {
            address: 3,
            size: 1,
            assignments: vec![],
            control: Control::Return(r(6)),
        },
    ];
    let program = Program::new(0, 7, instructions).unwrap();
    let reduced = nirvana::reduce::reduce(&program).unwrap();
    let validation = nirvana::block_verify::validate_program(&program, reduced.program(), &solver);
    assert!(validation.accepted(), "{validation:?}");
    assert_eq!(validation.blocks.len(), 2);
}

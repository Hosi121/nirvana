//! Checked C backend regression for pure bit-helper rendering.
//!
//! The original lifted IR is authoritative, including O0 stack/input aliasing.
//! Native source C is never executed on these guest addresses. Comparison covers
//! return, every guest byte, and the first fault's address/access/width; neither
//! original instruction traces nor final complete registers are C observations.

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
const MEMORY_SIZE: usize = 64;
const ADDRESSES: [u64; 9] = [
    BASE,
    BASE + 1,
    BASE + 16,
    BASE + 32,
    BASE + 48,
    BASE + 56,
    BASE + 63,
    0xffff,
    u64::MAX,
];
const COUNTS: [u64; 6] = [0, 1, 63, 64, 255, u64::MAX];

fn words(count: u64) -> [[u64; 4]; 2] {
    [
        [
            0x0123_4567_89ab_cdef,
            count,
            0x8000_0000_0000_0001,
            0xfedc_ba98_7654_3210,
        ],
        [u64::MAX, count, 0, 0x8000_0000_ffff_0001],
    ]
}

// Match checked_c::source(...,4) exactly, including partial initialization and
// overflowing address+word*8. The poison pattern makes untouched bytes visible.
fn prepare(address: u64, input: [u64; 4]) -> Vec<u8> {
    let mut memory: Vec<_> = (0..MEMORY_SIZE)
        .map(|index| index.wrapping_mul(29).wrapping_add(7) as u8)
        .collect();
    for (word, value) in input.into_iter().enumerate() {
        if let Some(offset) = address
            .checked_add(word as u64 * 8)
            .and_then(|a| a.checked_sub(BASE))
            && offset <= (MEMORY_SIZE - 8) as u64
        {
            let offset = offset as usize;
            memory[offset..offset + 8].copy_from_slice(&value.to_le_bytes());
        }
    }
    memory
}

#[test]
fn actual_rotate_and_bswap_helpers_keep_full_memory_return_and_first_fault() {
    let scratch = native::Scratch::new();
    let mut compared = 0;
    for name in ["rotates", "byte-swap"] {
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
            for address in ADDRESSES {
                for count in COUNTS {
                    for input in words(count) {
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
                                "{name}{original_optimization} unexpectedly suspended at address={address:#x}, input={input:?}"
                            ),
                        };
                        observation.extend(
                            report
                                .state
                                .memory
                                .chunks_exact(8)
                                .map(|word| u64::from_le_bytes(word.try_into().unwrap())),
                        );
                        assert_eq!(observation.len(), 13);
                        expected.push(observation);
                    }
                }
            }
            assert_eq!(expected.len(), 108);
            assert!(
                returns > 0 && reads > 0,
                "cohort lost successful/read-fault coverage"
            );
            if original_optimization == "-O0" {
                assert!(
                    writes > 0,
                    "cohort lost O0 stack-alias write-fault coverage"
                );
            }
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
                let required = if name == "rotates" {
                    ["nirvana_rol64(", "nirvana_ror64("]
                } else {
                    ["nirvana_bswap32(", "nirvana_bswap64("]
                };
                for helper in required {
                    assert!(
                        body.contains(helper),
                        "helper declined in actual {name}{original_optimization}, views={recover_objects}: {helper}\n{body}"
                    );
                }
                if name == "rotates" {
                    for helper in ["nirvana_rol16(", "nirvana_rol32(", "nirvana_ror8("] {
                        assert_eq!(
                            body.contains(helper),
                            original_optimization == "-O2",
                            "masked narrow idiom scope: {name}{original_optimization}, views={recover_objects}: {helper}\n{body}",
                        );
                    }
                }
                assert_eq!(program.instructions(), instructions);
                let source = checked_c::source(&output, program.register_count(), 4);
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
                        native::run_fields(&binary, &input_text, 13),
                        expected,
                        "{name} source{original_optimization}, views={recover_objects}, generated{generated_optimization}"
                    );
                    compared += expected.len();
                }
            }
            assert_eq!(program.instructions(), instructions);
            println!(
                "{name} {original_optimization}: 108 IR inputs, returns={returns}, read faults={reads}, write faults={writes}; both views and generated O0/O2 agree"
            );
        }
    }
    assert_eq!(compared, 1728);
    println!("bit helper backend: {compared} exact return/full-64-byte/first-fault comparisons");
}

//! Native checked-memory regression for adopted finite loop display recovery.
//!
//! The original sum fixture is compiled only at O2. Invalid guest addresses are
//! exercised against lifted IR and generated checked C, never native pointer C.
//! This cohort compares every guest byte and the first failing guest address;
//! it does not distinguish access kinds/widths or reproduce original IR traces.

#[path = "support/checked_c.rs"]
mod checked_c;
#[allow(dead_code)]
#[path = "support/native.rs"]
mod native;

use nirvana::ir::{AccessKind, Reg, RunStatus, Width};
use nirvana::readable::{ReadableOptions, emit_readable_c_with_options};
use nirvana::{frontend, x86};
use std::fmt::Write as _;

const BASE: u64 = 0x1000;
const MEMORY_SIZE: usize = 64;
const ADDRESSES: [u64; 6] = [0x1000, 0x1010, 0x1028, 0x1038, 0x103f, 0xffff];

fn prepare(address: u64, value: u64) -> Vec<u8> {
    let mut memory: Vec<_> = (0..MEMORY_SIZE)
        .map(|index| index.wrapping_mul(29).wrapping_add(7) as u8)
        .collect();
    if let Some(offset) = address.checked_sub(BASE)
        && offset <= (MEMORY_SIZE - 8) as u64
    {
        let offset = offset as usize;
        memory[offset..offset + 8].copy_from_slice(&value.to_le_bytes());
    }
    memory
}

#[test]
fn compiled_sum_o2_finite_loop_matches_lifted_ir_full_memory_and_first_fault() {
    let scratch = native::Scratch::new();
    let object = scratch.0.join("sum-original-O2.o");
    native::object(
        &native::fixture_root().join("cases/sum.c"),
        &object,
        "-O2",
        "fixture",
    );
    let lifted = frontend::lift_elf(&std::fs::read(object).unwrap(), "fixture").unwrap();
    let program = &lifted.program;
    let original = program.instructions().to_vec();
    let mut input = String::new();
    let mut expected = Vec::new();
    for address in ADDRESSES {
        for value in 0..8u64 {
            writeln!(input, "{address} {value} 0 0 0").unwrap();
            let memory = prepare(address, value);
            let mut registers = vec![0; program.register_count()];
            registers[x86::RDI] = address;
            registers[x86::RSP] = BASE + MEMORY_SIZE as u64;
            let report = program
                .run_with_memory(&registers, BASE, &memory, 100_000)
                .unwrap();
            let (fault, fault_address, result) = match report.status {
                RunStatus::Returned(result) => {
                    assert!(matches!(address, 0x1000 | 0x1010));
                    assert_eq!(result, value * value.saturating_sub(1) / 2);
                    (0, 0, result)
                }
                RunStatus::Fault(fault) => {
                    assert!(!matches!(address, 0x1000 | 0x1010));
                    assert_eq!(fault.width, Width::U64);
                    if address == 0x1028 {
                        assert_eq!(fault.access, AccessKind::Write);
                        assert_eq!(fault.address, address + 24);
                    } else if address == 0x1038 {
                        assert_eq!(fault.access, AccessKind::Write);
                        assert!(fault.address >= BASE + MEMORY_SIZE as u64);
                    } else {
                        assert_eq!(fault.access, AccessKind::Read);
                        assert_eq!(fault.address, address);
                    }
                    (1, fault.address, 0)
                }
                RunStatus::Suspended => panic!("sum fixture unexpectedly suspended"),
            };
            if address == 0x1028 {
                // The final output store fails after both prior full-width
                // stores committed. Compare those values as well as all bytes.
                for offset in [48, 56] {
                    assert_eq!(
                        u64::from_le_bytes(
                            report.state.memory[offset..offset + 8].try_into().unwrap()
                        ),
                        value,
                    );
                }
            }
            if matches!(address, 0x1038 | 0x103f | 0xffff) {
                assert_eq!(
                    report.state.memory, memory,
                    "first fault must precede stores"
                );
            }
            let mut observation = vec![fault, fault_address, result];
            observation.extend(
                report
                    .state
                    .memory
                    .chunks_exact(8)
                    .map(|word| u64::from_le_bytes(word.try_into().unwrap())),
            );
            assert_eq!(observation.len(), 11);
            expected.push(observation);
        }
    }
    assert_eq!(expected.len(), 48);

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
        assert_eq!(output.finite_regions.len(), 1, "{}", output.code);
        assert_eq!(output.finite_regions[0].cases, 8);
        let body = output
            .code
            .split("uint64_t nirvana_readable(")
            .nth(1)
            .unwrap();
        assert_eq!(
            body.matches("while (").count() + body.matches("for (").count(),
            1,
            "{body}"
        );
        assert!(output.fallback_reason.is_none());
        assert_eq!(program.instructions(), original);

        let source_text = checked_c::source(&output, program.register_count(), 1);
        for optimization in ["-O0", "-O2"] {
            let source = scratch
                .0
                .join(format!("sum-generated-{recover_objects}{optimization}.c"));
            std::fs::write(&source, &source_text).unwrap();
            let object = source.with_extension("o");
            let binary = source.with_extension("bin");
            native::object(&source, &object, optimization, "nirvana_readable");
            native::link(&[&object], &binary);
            assert_eq!(
                native::run_fields(&binary, &input, 11),
                expected,
                "object views={recover_objects}, generated {optimization}"
            );
        }
    }
}

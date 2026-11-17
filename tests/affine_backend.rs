//! Native regression for affine display recovery from an actual O2 C fixture.
//!
//! Invalid guest pointers run only in lifted IR and generated checked C. We
//! compare every guest byte, return value, and first fault address; access kind,
//! access width, original instruction traces, and final registers are excluded.

#[path = "support/checked_c.rs"]
mod checked_c;
#[allow(dead_code)]
#[path = "support/native.rs"]
mod native;

use nirvana::ir::{Reg, RunStatus};
use nirvana::readable::{ReadableOptions, emit_readable_c_with_options};
use nirvana::{frontend, x86};
use std::fmt::Write as _;

const BASE: u64 = 0x1000;
const MEMORY_SIZE: usize = 64;
const ADDRESSES: [u64; 6] = [0x1000, 0x1010, 0x1028, 0x1038, 0x103f, 0xffff];
const SEEDS: [u64; 8] = [
    0,
    1,
    u64::MAX,
    u64::MAX - 1,
    1 << 63,
    0x5555_5555_5555_5555,
    0xaaaa_aaaa_aaaa_aaaa,
    0x8000_0000_0000_0001,
];

fn initialize_word(memory: &mut [u8], address: u64, value: u64) {
    if let Some(offset) = address.checked_sub(BASE)
        && offset <= (memory.len() - 8) as u64
    {
        let offset = offset as usize;
        memory[offset..offset + 8].copy_from_slice(&value.to_le_bytes());
    }
}

fn prepare(address: u64, limit: u64, seed: u64) -> Vec<u8> {
    let mut memory: Vec<_> = (0..MEMORY_SIZE)
        .map(|index| index.wrapping_mul(29).wrapping_add(7) as u8)
        .collect();
    initialize_word(&mut memory, address, limit);
    if let Some(seed_address) = address.checked_add(8) {
        initialize_word(&mut memory, seed_address, seed);
    }
    memory
}

#[test]
fn compiled_seeded_sum_o2_affine_loop_matches_ir_full_memory_return_and_first_fault() {
    let scratch = native::Scratch::new();
    let object = scratch.0.join("seeded-sum-original-O2.o");
    native::object(
        &native::fixture_root().join("recovery/seeded-sum.c"),
        &object,
        "-O2",
        "fixture",
    );
    let lifted = frontend::lift_elf(&std::fs::read(object).unwrap(), "fixture").unwrap();
    let program = &lifted.program;
    let original = program.instructions().to_vec();
    let mut input = String::new();
    let mut expected = Vec::new();
    let mut returned = 0;
    let mut faults = 0;
    for address in ADDRESSES {
        for limit in 0..8u64 {
            for seed in SEEDS {
                writeln!(input, "{address} {limit} {seed} 0 0").unwrap();
                let memory = prepare(address, limit, seed);
                let mut registers = vec![0; program.register_count()];
                registers[x86::RDI] = address;
                registers[x86::RSP] = BASE + MEMORY_SIZE as u64;
                let report = program
                    .run_with_memory(&registers, BASE, &memory, 100_000)
                    .unwrap();
                let (fault, fault_address, result) = match report.status {
                    RunStatus::Returned(result) => {
                        returned += 1;
                        assert!(matches!(address, 0x1000 | 0x1010));
                        assert_eq!(
                            result,
                            seed.wrapping_add(limit * limit.saturating_sub(1) / 2),
                        );
                        (0, 0, result)
                    }
                    RunStatus::Fault(fault) => {
                        faults += 1;
                        // Do not infer access order from the C source. In
                        // particular, O2 can read the seed at address+8 before
                        // other source operations. The lifted IR is the oracle.
                        (1, fault.address, 0)
                    }
                    RunStatus::Suspended => panic!("seeded sum unexpectedly suspended"),
                };
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
    }
    assert_eq!(expected.len(), 384);
    assert_eq!(returned, 128);
    assert_eq!(faults, 256);

    let mut native_rows = 0;
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
        assert!(output.finite_regions.is_empty(), "{}", output.code);
        assert_eq!(output.affine_regions.len(), 1, "{}", output.code);
        let evidence = &output.affine_regions[0];
        assert_eq!(evidence.cases, 8);
        assert!(
            evidence
                .maxima
                .contains(&(evidence.symbolic_input, u64::MAX))
        );
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

        let source_text = checked_c::source(&output, program.register_count(), 2);
        for optimization in ["-O0", "-O2"] {
            let source = scratch.0.join(format!(
                "seeded-sum-generated-{recover_objects}{optimization}.c"
            ));
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
            native_rows += expected.len();
        }
    }
    assert_eq!(native_rows, 1536);
    eprintln!(
        "affine backend: 384 IR inputs ({returned} returned/{faults} faulted), {native_rows} native rows"
    );
}

//! Transfers across nested loops with checked memory and overlapping stack data.
use crate::support::checked_c;
use crate::support::native;

use nirvana::ir::{AccessKind, Reg, RunStatus};
use nirvana::readable::{ReadableOptions, emit_readable_c_with_options};
use nirvana::{frontend, x86};
use std::fmt::Write as _;

const BASE: u64 = 4096;
const SIZE: usize = 256;
const ADDRESSES: [u64; 12] = [
    BASE,
    BASE + 1,
    BASE + 16,
    BASE + 128,
    BASE + 160,
    BASE + 192,
    BASE + 208,
    BASE + 224,
    BASE + 240,
    BASE + 248,
    BASE + 255,
    u64::MAX,
];

fn prepare(address: u64, input: [u64; 4]) -> Vec<u8> {
    let mut memory: Vec<_> = (0..SIZE).map(|i| (i * 29 + 7) as u8).collect();
    for (index, word) in input.into_iter().enumerate() {
        if let Some(offset) = address
            .checked_add(index as u64 * 8)
            .and_then(|location| location.checked_sub(BASE))
            && offset <= (SIZE - 8) as u64
        {
            let offset = offset as usize;
            memory[offset..offset + 8].copy_from_slice(&word.to_le_bytes());
        }
    }
    memory
}

#[test]
fn compiled_nonlocal_transfers_keep_all_memory_and_the_first_fault() {
    let scratch = native::Scratch::new();
    let mut compared = 0;
    let mut write_faults = 0;
    for original_optimization in ["-O0", "-O2"] {
        let object = scratch.0.join(format!("original{original_optimization}.o"));
        native::object(
            &native::fixture_root().join("recovery/nested-transfer-effects.c"),
            &object,
            original_optimization,
            "fixture",
        );
        let program = frontend::lift_elf(&std::fs::read(object).unwrap(), "fixture")
            .unwrap()
            .program;
        let original = program.instructions().to_vec();
        let mut text = String::new();
        let mut expected = Vec::new();
        let (mut returns, mut reads, mut writes) = (0, 0, 0);
        for address in ADDRESSES {
            for mode in 0..8u64 {
                for initial in [0, 1 << 63, u64::MAX] {
                    let input = [mode, initial ^ mode, !initial, 63 - mode];
                    writeln!(
                        text,
                        "{address} {} {} {} {}",
                        input[0], input[1], input[2], input[3]
                    )
                    .unwrap();
                    let mut registers = vec![0; program.register_count()];
                    registers[x86::RDI] = address;
                    registers[x86::RSP] = BASE + SIZE as u64;
                    let report = program
                        .run_with_memory(&registers, BASE, &prepare(address, input), 100_000)
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
                        RunStatus::Suspended => {
                            panic!("bounded fixture suspended: {address:#x}, {input:?}")
                        }
                    };
                    observation.extend(
                        report
                            .state
                            .memory
                            .chunks_exact(8)
                            .map(|word| u64::from_le_bytes(word.try_into().unwrap())),
                    );
                    expected.push(observation);
                }
            }
        }
        assert_eq!(expected.len(), 288);
        assert!(returns > 0 && reads > 0);
        write_faults += writes;
        for recover_objects in [false, true] {
            let output = emit_readable_c_with_options(
                &program,
                ReadableOptions {
                    stack_register: Some(Reg(x86::RSP)),
                    recover_objects,
                    coalesce_locals: true,
                    compact_memory: true,
                },
            )
            .unwrap();
            assert!(output.fallback_reason.is_none());
            assert!(output.structure_evidence.is_some());
            assert!(output.display_structure_evidence.is_some());
            assert!(!output.code.contains("nirvana_transfer"));
            assert!(!output.code.contains("nirvana_continue ="));
            let source = checked_c::source_with_size(&output, program.register_count(), 4, SIZE);
            for generated_optimization in ["-O0", "-O2"] {
                let path = scratch.0.join(format!(
                    "generated{original_optimization}-{recover_objects}{generated_optimization}.c"
                ));
                std::fs::write(&path, &source).unwrap();
                let object = path.with_extension("o");
                let binary = path.with_extension("bin");
                native::object(&path, &object, generated_optimization, "nirvana_readable");
                native::link(&[&object], &binary);
                assert_eq!(
                    native::run_fields(&binary, &text, 5 + SIZE / 8),
                    expected,
                    "source {original_optimization}, views={recover_objects}, C {generated_optimization}"
                );
                compared += expected.len();
            }
        }
        assert_eq!(program.instructions(), original);
        println!(
            "{original_optimization}: 288 inputs, {returns} returns, {reads} read faults, {writes} write faults"
        );
    }
    assert_eq!(compared, 2304);
    assert!(
        write_faults > 0,
        "the cohort must include destination faults"
    );
}

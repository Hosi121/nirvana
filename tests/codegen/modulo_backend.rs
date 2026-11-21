//! Real modulo-bounded accumulation, including arbitrary initial accumulator.
//!
//! The source compiles at ordinary O0/O2. Original lifted IR is the oracle for
//! stack/input aliases and invalid guest addresses. Checked C must match all
//! 256 bytes, return and exact first fault; source C receives no guest pointers.
//! The independent Rust oracle applies at BASE, where source stack is disjoint.

use crate::support::checked_c;
use crate::support::native;

use nirvana::ir::{AccessKind, Reg, RunStatus};
use nirvana::readable::{ReadableOptions, emit_readable_c_with_options};
use nirvana::{frontend, x86};
use std::fmt::Write as _;

const BASE: u64 = 4096;
const MEMORY_SIZE: usize = 256;
const FIELDS: usize = 5 + MEMORY_SIZE / 8;
const SIGN: u64 = 1 << 63;
const VALUES: [u64; 26] = [
    0,
    1,
    2,
    3,
    4,
    5,
    6,
    7,
    8,
    9,
    10,
    11,
    12,
    13,
    14,
    15,
    16,
    17,
    18,
    19,
    SIGN - 1,
    SIGN,
    SIGN + 1,
    u64::MAX - 9,
    u64::MAX - 1,
    u64::MAX,
];
const SEEDS: [u64; 8] = [
    0,
    1,
    u64::MAX,
    u64::MAX - 1,
    SIGN,
    0x5555_5555_5555_5555,
    0xaaaa_aaaa_aaaa_aaaa,
    SIGN + 1,
];
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

fn prepare(address: u64, input: [u64; 4]) -> Vec<u8> {
    let mut memory: Vec<_> = (0..MEMORY_SIZE)
        .map(|i| i.wrapping_mul(29).wrapping_add(7) as u8)
        .collect();
    for (index, word) in input.into_iter().enumerate() {
        if let Some(offset) = address
            .checked_add(index as u64 * 8)
            .and_then(|location| location.checked_sub(BASE))
            && offset <= (MEMORY_SIZE - 8) as u64
        {
            let offset = offset as usize;
            memory[offset..offset + 8].copy_from_slice(&word.to_le_bytes());
        }
    }
    memory
}

#[test]
fn modulo_bounded_sum_recovers_one_loop_and_preserves_full_guest_observations() {
    let scratch = native::Scratch::new();
    let mut comparisons = 0;
    let mut total_write_faults = 0;
    for source_optimization in ["-O0", "-O2"] {
        let object = scratch
            .0
            .join(format!("modulo-source{source_optimization}.o"));
        native::object(
            &native::fixture_root().join("recovery/modulo-sum.c"),
            &object,
            source_optimization,
            "fixture",
        );
        let lifted = frontend::lift_elf(&std::fs::read(object).unwrap(), "fixture").unwrap();
        let program = &lifted.program;
        let original = program.instructions().to_vec();
        let mut input_text = String::new();
        let mut expected = Vec::new();
        let (mut returns, mut read_faults, mut write_faults, mut base_oracles) = (0, 0, 0, 0);
        for address in ADDRESSES {
            for value in VALUES {
                for seed in SEEDS {
                    let input = [value, seed, 0xaaaa_aaaa_aaaa_aaaa, 0x5555_5555_5555_5555];
                    writeln!(
                        input_text,
                        "{address} {} {} {} {}",
                        input[0], input[1], input[2], input[3]
                    )
                    .unwrap();
                    let mut registers = vec![0; program.register_count()];
                    registers[x86::RDI] = address;
                    registers[x86::RSP] = BASE + MEMORY_SIZE as u64;
                    let report = program
                        .run_with_memory(&registers, BASE, &prepare(address, input), 100_000)
                        .unwrap();
                    if address == BASE {
                        let limit = value % 10;
                        let total = seed.wrapping_add(limit * limit.saturating_sub(1) / 2);
                        assert_eq!(report.status, RunStatus::Returned(total));
                        let state: Vec<_> = report.state.memory[..32]
                            .chunks_exact(8)
                            .map(|word| u64::from_le_bytes(word.try_into().unwrap()))
                            .collect();
                        assert_eq!(state, [value, limit, limit, total]);
                        base_oracles += 1;
                    }
                    let mut row = match report.status {
                        RunStatus::Returned(result) => {
                            returns += 1;
                            vec![0, 0, 0, 0, result]
                        }
                        RunStatus::Fault(fault) => {
                            let access = match fault.access {
                                AccessKind::Read => {
                                    read_faults += 1;
                                    1
                                }
                                AccessKind::Write => {
                                    write_faults += 1;
                                    2
                                }
                            };
                            vec![1, fault.address, access, fault.width.bytes() as u64, 0]
                        }
                        RunStatus::Suspended => panic!(
                            "bounded sum suspended: {source_optimization}, address={address:#x}, input={input:?}"
                        ),
                    };
                    row.extend(
                        report
                            .state
                            .memory
                            .chunks_exact(8)
                            .map(|word| u64::from_le_bytes(word.try_into().unwrap())),
                    );
                    assert_eq!(row.len(), FIELDS);
                    expected.push(row);
                }
            }
        }
        assert_eq!(base_oracles, VALUES.len() * SEEDS.len());
        assert_eq!(expected.len(), 2496);
        assert!(returns > 0 && read_faults > 0);
        total_write_faults += write_faults;
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
            assert!(output.finite_regions.is_empty());
            if source_optimization == "-O2" {
                assert_eq!(output.affine_regions.len(), 1, "{}", output.code);
                let evidence = &output.affine_regions[0];
                assert_eq!(evidence.cases, 10);
                assert!(
                    evidence
                        .inputs
                        .iter()
                        .any(|(_, values)| *values == (0..10).collect::<Vec<_>>())
                );
                assert!(
                    evidence
                        .maxima
                        .contains(&(evidence.symbolic_input, u64::MAX))
                );
            } else {
                assert!(output.affine_regions.is_empty());
            }
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
            let source =
                checked_c::source_with_size(&output, program.register_count(), 4, MEMORY_SIZE);
            for generated_optimization in ["-O0", "-O2"] {
                let path = scratch.0.join(format!(
                    "modulo-{source_optimization}-{recover_objects}-{generated_optimization}.c"
                ));
                std::fs::write(&path, &source).unwrap();
                let object = path.with_extension("o");
                let binary = path.with_extension("bin");
                native::object(&path, &object, generated_optimization, "nirvana_readable");
                native::link(&[&object], &binary);
                assert_eq!(
                    native::run_fields(&binary, &input_text, FIELDS),
                    expected,
                    "{source_optimization}, views={recover_objects}, generated{generated_optimization}"
                );
                comparisons += expected.len();
            }
        }
        eprintln!(
            "modulo {source_optimization}: returns={returns}, read-faults={read_faults}, write-faults={write_faults}, rows={}",
            expected.len()
        );
    }
    assert!(total_write_faults > 0, "missing destination-fault coverage");
    assert_eq!(comparisons, 19_968);
}

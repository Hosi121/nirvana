//! Native C regression for certified constant-division presentation.
//!
//! Original lifted IR defines the guest behavior, including stack/input aliases.
//! Compare return, every guest byte and exact first fault. Native source C is
//! never called with guest addresses; BASE cases also use an independent Rust
//! unsigned-division oracle with the same low32 lane.

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

const BASE: u64 = 4096;
const MEMORY_SIZE: usize = 256;
const FIELDS: usize = 5 + MEMORY_SIZE / 8;
const SIGN: u64 = 1 << 63;
const VALUES: [u64; 28] = [
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
    17,
    18,
    19,
    20,
    21,
    99,
    100,
    101,
    SIGN - 2,
    SIGN - 1,
    SIGN,
    SIGN + 1,
    u64::MAX - 9,
    u64::MAX - 2,
    u64::MAX - 1,
    u64::MAX,
];
const WORDS: [u64; 5] = [0, 9, 10, 11, u64::MAX];
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
            .and_then(|p| p.checked_sub(BASE))
            && offset <= (MEMORY_SIZE - 8) as u64
        {
            let offset = offset as usize;
            memory[offset..offset + 8].copy_from_slice(&word.to_le_bytes());
        }
    }
    memory
}

fn has_constant_operator(body: &str, operator: &str, divisor: u64) -> bool {
    let compact: String = body.chars().filter(|c| !c.is_ascii_whitespace()).collect();
    [
        format!("{operator}{divisor}"),
        format!("{operator}UINT64_C({divisor})"),
        format!("{operator}UINT64_C(0x{divisor:x})"),
    ]
    .iter()
    .any(|needle| {
        compact.match_indices(needle).any(|(index, _)| {
            compact[index + needle.len()..]
                .chars()
                .next()
                .is_none_or(|c| !(c.is_ascii_alphanumeric() || c == '_'))
        })
    })
}

#[test]
fn actual_constant_division_preserves_aliases_partial_memory_and_exact_first_fault() {
    let scratch = native::Scratch::new();
    let mut comparisons = 0;
    let mut total_write_faults = 0;
    for (fixture, divisor, source_optimization) in [
        ("unsigned-div-constant", 10_u64),
        ("unsigned-div-seven", 7_u64),
        ("unsigned-div-three", 3_u64),
        ("unsigned-div-five", 5_u64),
        ("unsigned-div-nine", 9_u64),
        ("unsigned-div-fifteen", 15_u64),
        ("unsigned-div-large", (1_u64 << 63) - 1),
    ]
    .into_iter()
    .flat_map(|(fixture, divisor)| {
        ["-O0", "-O2"].map(move |optimization| (fixture, divisor, optimization))
    }) {
        let object = scratch
            .0
            .join(format!("division-{fixture}{source_optimization}.o"));
        native::object(
            &native::fixture_root().join(format!("recovery/{fixture}.c")),
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
                for word in WORDS {
                    let input = [value, 0xaaaa_aaaa_aaaa_aaaa, 0x5555_5555_5555_5555, word];
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
                        let q = value / divisor;
                        let remainder = value % divisor;
                        let lane = u64::from(word as u32);
                        let small = lane / 10 + lane % 10;
                        assert_eq!(
                            report.status,
                            RunStatus::Returned(if divisor == 10 {
                                q ^ (remainder << 8) ^ small
                            } else {
                                q ^ remainder
                            })
                        );
                        let state = report.state.memory[..32]
                            .chunks_exact(8)
                            .map(|w| u64::from_le_bytes(w.try_into().unwrap()))
                            .collect::<Vec<_>>();
                        assert_eq!(
                            state,
                            [
                                value,
                                q,
                                remainder,
                                if divisor == 10 { small } else { word }
                            ]
                        );
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
                            "straight-line division suspended: {source_optimization}, address={address:#x}, input={input:?}"
                        ),
                    };
                    row.extend(
                        report
                            .state
                            .memory
                            .chunks_exact(8)
                            .map(|w| u64::from_le_bytes(w.try_into().unwrap())),
                    );
                    assert_eq!(row.len(), FIELDS);
                    expected.push(row);
                }
            }
        }
        assert_eq!(base_oracles, VALUES.len() * WORDS.len());
        assert_eq!(expected.len(), ADDRESSES.len() * VALUES.len() * WORDS.len());
        assert!(
            returns > 0 && read_faults > 0,
            "lost return/read-fault coverage"
        );
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
            if divisor == 10 && source_optimization == "-O2" {
                assert!(output.locals.iter().any(|local| {
                    local.role == Some(nirvana::value_role::ValueRole::Quotient)
                        && local.name == "quotient"
                }));
            }
            let body = output
                .code
                .split("uint64_t nirvana_readable(")
                .nth(1)
                .unwrap();
            // The graph remainder view keeps the original high/shift quotient
            // computation and its read dependencies. Raw quotient views still
            // cover the existing inline reciprocal fixtures.
            if divisor == 10 || (source_optimization == "-O2" && ![3, 5, 9].contains(&divisor)) {
                assert!(
                    has_constant_operator(body, "/", divisor),
                    "constant division was not adopted: {fixture}, {source_optimization}, views={recover_objects}\n{body}"
                );
            }
            if divisor == 10 && source_optimization == "-O2" {
                assert!(
                    !body.contains("0xcccccccd")
                        && body.contains(" % 10")
                        && body.contains(" %= 10;"),
                    "narrow reciprocal remains: {body}"
                );
            }
            if source_optimization == "-O2" {
                assert!(
                    has_constant_operator(body, "%=", divisor),
                    "materialized remainder not adopted: {fixture}\n{body}"
                );
            }
            if divisor == 7 && source_optimization == "-O2" {
                assert!(
                    !body.contains("0x2492492492492493"),
                    "extended reciprocal remains: {body}"
                );
            }
            assert_eq!(program.instructions(), original);
            let source =
                checked_c::source_with_size(&output, program.register_count(), 4, MEMORY_SIZE);
            for generated_optimization in ["-O0", "-O2"] {
                let stem = format!(
                    "division-{fixture}-{source_optimization}-{recover_objects}-{generated_optimization}"
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
                    "{source_optimization}, views={recover_objects}, generated{generated_optimization}"
                );
                comparisons += expected.len();
            }
        }
        assert_eq!(program.instructions(), original);
        println!(
            "{fixture} {source_optimization}: {} inputs, returns={returns}, read faults={read_faults}, write faults={write_faults}; BASE oracles={base_oracles}; views2/Copts2 agree",
            expected.len()
        );
    }
    // A source optimization can turn all near-end cases into read faults before
    // a destination is reached. Require destination-fault coverage for the whole
    // cohort, while comparing each actual first access and width independently.
    assert!(total_write_faults > 0);
    assert_eq!(
        comparisons,
        7 * 2 * 2 * 2 * ADDRESSES.len() * VALUES.len() * WORDS.len()
    );
    println!("division backend: {comparisons} full256-byte/return/exact-first-fault comparisons");
}

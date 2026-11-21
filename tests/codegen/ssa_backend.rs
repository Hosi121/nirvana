//! Global SSA constants expose reciprocal arithmetic hoisted out of a loop.
//! Compare against original machine IR, including stack aliases and partial RAM.
use crate::support::checked_c;
use crate::support::native;
use nirvana::ir::{AccessKind, Reg, RunStatus};
use nirvana::readable::{ReadableOptions, emit_readable_c_with_options};
use nirvana::{frontend, x86};
use std::fmt::Write as _;
const BASE: u64 = 4096;
const SIZE: usize = 256;
const FIELDS: usize = 5 + SIZE / 8;
#[test]
fn hoisted_reciprocal_loop_preserves_return_full_memory_and_exact_first_fault() {
    let scratch = native::Scratch::new();
    let mut comparisons = 0;
    let mut prefix_cases = 0;
    for source_opt in ["-O0", "-O2"] {
        let object = scratch.0.join(format!("loop{source_opt}.o"));
        native::object(
            &native::fixture_root().join("recovery/hoisted-division-loop.c"),
            &object,
            source_opt,
            "fixture",
        );
        let lifted = frontend::lift_elf(&std::fs::read(object).unwrap(), "fixture").unwrap();
        let program = &lifted.program;
        let original = program.instructions().to_vec();
        let prefix_plan = nirvana::ssa_constants::ConstantPlan::analyze(program).unwrap();
        let prefix_candidate = prefix_plan
            .propose(program)
            .map(|(p, _)| p)
            .unwrap_or_else(|| program.clone());
        let mut text = String::new();
        let mut expected = Vec::new();
        let mut kinds = [0; 3];
        for pointer in [
            BASE,
            BASE + 1,
            BASE + 16,
            BASE + 160,
            BASE + 176,
            BASE + 192,
            BASE + 224,
            BASE + 232,
            BASE + 240,
            BASE + 248,
            BASE + 255,
            u64::MAX,
        ] {
            for x in [
                0,
                1,
                2,
                3,
                4,
                5,
                8,
                9,
                10,
                (1 << 63) - 1,
                1 << 63,
                (1 << 63) + 1,
                u64::MAX - 1,
                u64::MAX,
            ] {
                for seed in [0, u64::MAX] {
                    for count in [0, 1, 2, 7, u64::MAX] {
                        let input = [x, seed, 0x5555555555555555, count];
                        let mut memory: Vec<_> = (0..SIZE)
                            .map(|i| i.wrapping_mul(29).wrapping_add(7) as u8)
                            .collect();
                        for (index, word) in input.into_iter().enumerate() {
                            if let Some(offset) = pointer
                                .checked_add(index as u64 * 8)
                                .and_then(|p| p.checked_sub(BASE))
                                .filter(|&p| p <= (SIZE - 8) as u64)
                            {
                                memory[offset as usize..offset as usize + 8]
                                    .copy_from_slice(&word.to_le_bytes());
                            }
                        }
                        let mut registers = vec![0; program.register_count()];
                        registers[x86::RDI] = pointer;
                        registers[x86::RSP] = BASE + SIZE as u64;
                        let report = program
                            .run_with_memory(&registers, BASE, &memory, 100000)
                            .unwrap();
                        if report.status == RunStatus::Suspended {
                            // Guest stack/input overlap can overwrite loop bounds.
                            // Native C has no instruction cutoff. Keep these cases
                            // as explicit prefix checks, not completed C observations.
                            let transformed = prefix_candidate
                                .run_with_memory(&registers, BASE, &memory, 100000)
                                .unwrap();
                            assert_eq!(transformed.status, report.status);
                            assert_eq!(transformed.state.memory, report.state.memory);
                            assert_eq!(transformed.state.trace, report.state.trace);
                            prefix_cases += 1;
                            continue;
                        }
                        writeln!(
                            text,
                            "{pointer} {} {} {} {}",
                            input[0], input[1], input[2], input[3]
                        )
                        .unwrap();
                        if pointer == BASE {
                            let n = count & 7;
                            let total = (0..n)
                                .map(|i| x.wrapping_add(i))
                                .fold(seed, |a, v| a.wrapping_add((v / 3) ^ (v % 3)));
                            assert_eq!(report.status, RunStatus::Returned(total));
                            let state: Vec<_> = report.state.memory[..32]
                                .chunks_exact(8)
                                .map(|w| u64::from_le_bytes(w.try_into().unwrap()))
                                .collect();
                            assert_eq!(
                                state,
                                [
                                    x,
                                    total,
                                    if n == 0 {
                                        input[2]
                                    } else {
                                        x.wrapping_add(n - 1) % 3
                                    },
                                    count
                                ]
                            );
                        }
                        let mut row = match report.status {
                            RunStatus::Returned(value) => {
                                kinds[0] += 1;
                                vec![0, 0, 0, 0, value]
                            }
                            RunStatus::Fault(f) => {
                                let access = match f.access {
                                    AccessKind::Read => 1,
                                    AccessKind::Write => 2,
                                };
                                kinds[access] += 1;
                                vec![1, f.address, access as u64, f.width.bytes() as u64, 0]
                            }
                            _ => panic!("bounded hoisted loop suspended: {pointer:#x} {input:?}"),
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
        }
        assert!(!expected.is_empty());
        assert!(kinds[0] > 0 && kinds[1] > 0);
        for coalesce in [false, true] {
            for objects in [false, true] {
                let output = emit_readable_c_with_options(
                    program,
                    ReadableOptions {
                        stack_register: Some(Reg(x86::RSP)),
                        recover_objects: objects,
                        coalesce_locals: coalesce,
                        compact_memory: true,
                    },
                )
                .unwrap();
                if source_opt == "-O2" {
                    assert!(
                        output.ssa_constants.is_some(),
                        "global SSA selection unavailable"
                    );
                    assert!(
                        output.expression_evidence.is_some(),
                        "hoisted multiplier was not exposed"
                    );
                    let body = output
                        .code
                        .split("uint64_t nirvana_readable(")
                        .nth(1)
                        .unwrap();
                    assert!(body.contains(" / 3") && body.contains(" % 3"), "{body}");
                    assert!(
                        !body.contains("nirvana_umul_high"),
                        "hoisted machine arithmetic remains: {body}"
                    );
                }
                let harness =
                    checked_c::source_with_size(&output, program.register_count(), 4, SIZE);
                for copt in ["-O0", "-O2"] {
                    let source = scratch
                        .0
                        .join(format!("global-{source_opt}-{coalesce}-{objects}{copt}.c"));
                    std::fs::write(&source, &harness).unwrap();
                    let object = source.with_extension("o");
                    let bin = source.with_extension("bin");
                    native::object(&source, &object, copt, "nirvana_readable");
                    native::link(&[&object], &bin);
                    assert_eq!(
                        native::run_fields(&bin, &text, FIELDS),
                        expected,
                        "{source_opt}, coalesce={coalesce}, objects={objects}, C={copt}"
                    );
                    comparisons += expected.len();
                }
            }
        }
        assert_eq!(program.instructions(), original);
        println!(
            "{source_opt}: completed inputs={}, return/read/write counts={kinds:?}; storage2/views2/Copts2 agree",
            expected.len()
        );
    }
    assert_eq!(comparisons + prefix_cases * 8, 26880);
    println!(
        "SSA backend: {comparisons} full256-byte/return/exact-first-fault comparisons; {prefix_cases} suspended source/SSA prefix checks (native final observation inconclusive)"
    );
}

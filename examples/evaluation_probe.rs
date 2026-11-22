//! Prepare fixed ABI observers for one retained object and its actual generated C.
//! Native comparison observes the return/state[4]; checked C observes all RAM and
//! first faults. Source code is supplied only to the separate native compiler.
#[path = "../tests/support/checked_c.rs"]
#[allow(dead_code)]
mod checked_c;
#[path = "evaluation/fixture.rs"]
mod fixture;
#[path = "evaluation_probe/module.rs"]
mod module;
#[path = "evaluation_probe/stages.rs"]
mod stages;

use nirvana::{
    frontend,
    ir::{AccessKind, Reg, RunStatus},
    readable, x86,
};
use std::{fmt::Write, path::PathBuf};

use fixture::{BASE, POINTER, SIZE, STACK};

fn vectors(seed: u64, count: usize) -> Vec<[u64; 4]> {
    let fixed = [
        [0; 4],
        [1; 4],
        [u64::MAX; 4],
        [0, u64::MAX, 0, u64::MAX],
        [u64::MAX, 0, u64::MAX, 0],
        [1 << 63, 0, 1 << 63, 0],
        [1, 2, 3, 4],
        [0x8877665544332211, 3, 0x123456789abcdef0, 7],
    ];
    let mut state = seed;
    (0..count)
        .map(|n| {
            if n < fixed.len() {
                fixed[n]
            } else {
                std::array::from_fn(|_| {
                    state ^= state >> 12;
                    state ^= state << 25;
                    state ^= state >> 27;
                    state.wrapping_mul(0x2545f4914f6cdd1d)
                })
            }
        })
        .collect()
}
fn write_row(out: &mut String, words: &[u64]) {
    for (index, word) in words.iter().enumerate() {
        if index > 0 {
            out.push(' ');
        }
        write!(out, "{word}").unwrap();
    }
    out.push('\n');
}
fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut args = std::env::args().skip(1);
    let first = args.next().ok_or("object path required")?;
    if first == "--module" {
        return module::run(args);
    }
    if first == "--version" {
        if args.next().is_some() {
            return Err("--version accepts no additional arguments".into());
        }
        println!("{}", nirvana::BUILD_VERSION);
        return Ok(());
    }
    let object = PathBuf::from(first);
    let generated = PathBuf::from(args.next().ok_or("generated C path required")?);
    let out = PathBuf::from(args.next().ok_or("output directory required")?);
    let symbol = args.next().ok_or("symbol required")?;
    let mode = args.next().ok_or("emission mode required")?;
    let seed: u64 = args.next().ok_or("seed required")?.parse()?;
    let count: usize = args.next().ok_or("case count required")?.parse()?;
    let limit: usize = args.next().ok_or("step limit required")?.parse()?;
    let input_file = args.next();
    if args.next().is_some()
        || !(8..=256).contains(&count)
        || !(1..=1_000_000).contains(&limit)
        || symbol.is_empty()
        || !symbol
            .bytes()
            .enumerate()
            .all(|(i, c)| c == b'_' || c.is_ascii_alphabetic() || i > 0 && c.is_ascii_digit())
    {
        return Err("invalid evaluation profile".into());
    }
    std::fs::create_dir_all(&out)?;
    let source = frontend::lift_elf_auto(&std::fs::read(object)?, &symbol)?.program;
    let options = readable::ReadableOptions {
        stack_register: Some(Reg(x86::RSP)),
        recover_objects: true,
        coalesce_locals: true,
        compact_memory: true,
    };
    let output = match mode.as_str() {
        "readable-c" => readable::emit_readable_c_with_options(&source, options)?,
        "middle-c" => readable::emit_middle_c_with_options(
            &nirvana::middle_ir::Function::from_low(&source)?,
            options,
        )?,
        _ => return Err("unsupported evaluation emission mode".into()),
    };
    if output.code != std::fs::read_to_string(generated)? {
        return Err("generated C does not match object/mode/ABI descriptor".into());
    }
    if !output.uses_memory {
        return Err("evaluation profile requires checked guest memory".into());
    }
    std::fs::write(
        out.join("generated-probe.c"),
        checked_c::source_with_stack(&output, source.register_count(), 4, SIZE, STACK),
    )?;
    let native = format!(
        r#"#include <stdint.h>
#include <inttypes.h>
#include <stdio.h>
extern uint64_t {symbol}(uint64_t state[4]);
int main(void) {{
    uint64_t state[4];
    while (scanf("%" SCNu64 " %" SCNu64 " %" SCNu64 " %" SCNu64, &state[0], &state[1], &state[2], &state[3]) == 4) {{
        uint64_t value = {symbol}(state);
        printf("%" PRIu64 " %" PRIu64 " %" PRIu64 " %" PRIu64 " %" PRIu64 "\n", value, state[0], state[1], state[2], state[3]);
    }}
}}
"#
    );
    std::fs::write(out.join("native-probe.c"), native)?;
    let mut c_input = String::new();
    let mut c_expected = String::new();
    let mut native_input = String::new();
    let mut native_expected = String::new();
    let mut statuses = [0usize; 4];
    let mut native_cases = 0;
    let mut stages = stages::Stages::new(&source, &output, limit);
    let (generator, vectors) = if let Some(path) = input_file {
        let mut vectors = Vec::new();
        for line in std::fs::read_to_string(path)?.lines() {
            let words = line
                .split_whitespace()
                .map(str::parse)
                .collect::<Result<Vec<u64>, _>>()?;
            vectors.push(<[u64; 4]>::try_from(words).map_err(|_| "expected four input words")?);
        }
        if vectors.len() != count {
            return Err("input vector count differs from profile".into());
        }
        ("fixture-state4-input-file-v1", vectors)
    } else {
        ("fixture-state4-seeds-v1", vectors(seed, count))
    };
    for words in vectors {
        for pointer in [POINTER, BASE + SIZE as u64 - 16, u64::MAX] {
            let ram = fixture::memory(words, pointer);
            let regs = fixture::registers(source.register_count(), pointer);
            let report = source.run_with_memory(&regs, BASE, &ram, limit)?;
            stages.observe(&source, &regs, &ram, &report);
            let mut row = match report.status {
                RunStatus::Returned(value) => {
                    statuses[0] += 1;
                    if pointer == POINTER {
                        write_row(&mut native_input, &words);
                        let mut result = vec![value];
                        result.extend(
                            report.state.memory[128..160]
                                .chunks_exact(8)
                                .map(|b| u64::from_le_bytes(b.try_into().unwrap())),
                        );
                        write_row(&mut native_expected, &result);
                        native_cases += 1;
                    }
                    vec![0, 0, 0, 0, value]
                }
                RunStatus::Fault(f) => {
                    let kind = if f.access == AccessKind::Read { 1 } else { 2 };
                    statuses[kind] += 1;
                    vec![1, f.address, kind as u64, f.width.bytes() as u64, 0]
                }
                RunStatus::Suspended => {
                    statuses[3] += 1;
                    continue;
                }
            };
            let mut input = vec![pointer];
            input.extend(words);
            write_row(&mut c_input, &input);
            row.extend(
                report
                    .state
                    .memory
                    .chunks_exact(8)
                    .map(|b| u64::from_le_bytes(b.try_into().unwrap())),
            );
            write_row(&mut c_expected, &row);
        }
    }
    for (name, text) in [
        ("generated-inputs.txt", c_input),
        ("generated-expected.txt", c_expected),
        ("native-inputs.txt", native_input),
        ("native-expected.txt", native_expected),
    ] {
        std::fs::write(out.join(name), text)?;
    }
    println!(
        "{{\"schema\":\"nirvana-evaluation-probe-v1\",\"generator\":\"{generator}\",\"seed\":{seed},\"vectors\":{count},\"requested_cases\":{},\"checked_cases\":{},\"native_cases\":{native_cases},\"returned\":{},\"read_faults\":{},\"write_faults\":{},\"suspended\":{},\"step_limit\":{limit},\"memory_base\":{BASE},\"memory_size\":{SIZE},\"stack_pointer\":{STACK},\"state_pointer\":{POINTER},\"register_count\":{},\"row_words\":{},\"stage_checks\":{}}}",
        count * 3,
        statuses[0] + statuses[1] + statuses[2],
        statuses[0],
        statuses[1],
        statuses[2],
        statuses[3],
        source.register_count(),
        5 + SIZE / 8,
        stages.json(&output, &out)?
    );
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn seeded_profile_retains_boundary_vectors_and_replays_random_inputs() {
        let a = vectors(17, 16);
        let b = vectors(17, 16);
        assert_eq!(a, b);
        assert_eq!(a[2], [u64::MAX; 4]);
        assert_ne!(a[8..], vectors(19, 16)[8..]);
    }
}

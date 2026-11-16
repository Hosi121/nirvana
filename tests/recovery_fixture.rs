//! Independent source shapes for field, array, and alias recovery.
//!
//! Native C observes the return and four state words. Recompiled readable C
//! additionally matches an IR digest over every guest byte, including stack.

#[path = "support/native.rs"]
mod native;

use native::{Scratch, fixture_root, link, object, run, run_fields};
use nirvana::ir::{Execution, Reg};
use nirvana::{frontend, readable, x86};
use std::collections::BTreeMap;
use std::fmt::Write as _;

const BASE: u64 = 0x1000;
const STATE: usize = 0x1000;
const MEMORY_SIZE: usize = 0x10000;
const CASES: [&str; 3] = ["byte-fields", "strided-input", "selected-alias"];

fn inputs() -> Vec<[u64; 4]> {
    let mut inputs: Vec<_> = include_str!("fixtures/inputs.tsv")
        .lines()
        .filter(|line| !line.is_empty() && !line.starts_with('#'))
        .map(|line| {
            let fields: Vec<_> = line.split('\t').collect();
            std::array::from_fn(|i| fields[i + 1].parse().unwrap())
        })
        .collect();
    inputs.extend([
        [
            0x0807_0605_0403_0201,
            0x100f_0e0d_0c0b_0a09,
            0x1817_1615_1413_1211,
            0,
        ],
        [u64::MAX, 8, 0, 1],
        [0, 16, u64::MAX, 2],
        [u64::MAX, 56, u64::MAX, 3],
        [0, u64::MAX, 1 << 63, u64::MAX],
        [
            0xff00_ff00_ff00_ff00,
            0x00ff_00ff_00ff_00ff,
            0x8000_0000_0000_0001,
            1,
        ],
    ]);
    inputs
}

fn prepare(input: &[u64; 4]) -> (Vec<u64>, Vec<u8>) {
    let mut registers = vec![0; x86::REGISTER_COUNT];
    registers[x86::RDI] = BASE + STATE as u64;
    registers[x86::RSP] = 0x10000;
    let mut memory: Vec<_> = (0..MEMORY_SIZE)
        .map(|i| (i.wrapping_mul(29).wrapping_add(7)) as u8)
        .collect();
    for (index, value) in input.iter().enumerate() {
        memory[STATE + index * 8..STATE + index * 8 + 8].copy_from_slice(&value.to_le_bytes());
    }
    (registers, memory)
}

fn visible(execution: &Execution) -> Vec<u64> {
    let mut result = vec![execution.value];
    result.extend((0..4).map(|index| {
        u64::from_le_bytes(
            execution.memory[STATE + index * 8..STATE + index * 8 + 8]
                .try_into()
                .unwrap(),
        )
    }));
    result
}

fn memory_digest(memory: &[u8]) -> u64 {
    memory.iter().fold(0xcbf29ce484222325, |hash, byte| {
        (hash ^ u64::from(*byte)).wrapping_mul(0x100000001b3)
    })
}

fn readable_harness(output: &readable::ReadableC) -> String {
    let mut arguments: Vec<_> = output
        .parameters
        .iter()
        .map(|reg| format!("r[{}]", reg.0))
        .collect();
    if output.uses_memory {
        arguments.extend(["memory", "UINT64_C(4096)", "sizeof(memory)"].map(String::from));
    }
    let call = format!("nirvana_readable({})", arguments.join(", "));
    format!(
        r#"
#include <inttypes.h>
#include <stdio.h>
int main(void) {{
    uint64_t input[4];
    while (scanf("%" SCNu64 " %" SCNu64 " %" SCNu64 " %" SCNu64,
                 &input[0], &input[1], &input[2], &input[3]) == 4) {{
        uint64_t r[32] = {{0}};
        uint8_t memory[65536];
        for (unsigned i = 0; i < sizeof(memory); ++i) memory[i] = (uint8_t)(i * 29 + 7);
        r[7] = UINT64_C(8192); r[4] = UINT64_C(65536);
        for (unsigned i = 0; i < 4; ++i)
            for (unsigned j = 0; j < 8; ++j) memory[4096 + i * 8 + j] = (uint8_t)(input[i] >> (j * 8));
        uint64_t value = {call};
        uint64_t hash = UINT64_C(14695981039346656037);
        for (unsigned i = 0; i < sizeof(memory); ++i) hash = (hash ^ memory[i]) * UINT64_C(1099511628211);
        for (unsigned i = 0; i < 4; ++i) {{
            input[i] = 0;
            for (unsigned j = 0; j < 8; ++j) input[i] |= (uint64_t)memory[4096 + i * 8 + j] << (j * 8);
        }}
        printf("%" PRIu64 " %" PRIu64 " %" PRIu64 " %" PRIu64 " %" PRIu64 " %" PRIu64 "\n",
               value, input[0], input[1], input[2], input[3], hash);
    }}
}}
"#
    )
}

#[test]
fn independent_recovery_sources_match_native_ir_and_readable_c() {
    let scratch = Scratch::new();
    let root = fixture_root();
    let inputs = inputs();
    assert_eq!(inputs.len(), 69);
    let mut input_text = String::new();
    for input in &inputs {
        writeln!(
            input_text,
            "{} {} {} {}",
            input[0], input[1], input[2], input[3]
        )
        .unwrap();
    }
    let mut native_reference = BTreeMap::new();
    let mut comparisons = 0;
    for optimization in ["-O0", "-O2"] {
        let directory = scratch.0.join(optimization);
        std::fs::create_dir(&directory).unwrap();
        let harness = directory.join("harness.o");
        object(&root.join("harness.c"), &harness, optimization, "fixture");
        for name in CASES {
            let original = directory.join(format!("{name}.o"));
            object(
                &root.join("recovery").join(format!("{name}.c")),
                &original,
                optimization,
                "fixture",
            );
            let native_binary = directory.join(format!("{name}-native"));
            link(&[&original, &harness], &native_binary);
            let native = run(&native_binary, &input_text);
            assert_eq!(native.len(), inputs.len());
            if optimization == "-O0" {
                native_reference.insert(name, native.clone());
            } else {
                assert_eq!(
                    native, native_reference[name],
                    "{name}: native O0/O2 disagree"
                );
            }
            // Every source/optimization is required to lift. Never skip a new
            // unsupported decoder operation or relocation to retain a green test.
            let program = frontend::lift_elf(&std::fs::read(&original).unwrap(), "fixture")
                .unwrap_or_else(|error| panic!("{name} {optimization}: {error}"))
                .program;
            let mut expected_memory = Vec::new();
            for (input, native) in inputs.iter().zip(&native) {
                let (registers, memory) = prepare(input);
                let execution = program
                    .execute_with_memory(&registers, BASE, &memory, 10_000)
                    .unwrap_or_else(|error| {
                        panic!("{name} {optimization}, input={input:?}: {error}")
                    });
                let mut expected = visible(&execution);
                assert_eq!(&expected, native, "{name} {optimization}, input={input:?}");
                expected.push(memory_digest(&execution.memory));
                expected_memory.push(expected);
            }
            let output = readable::emit_readable_c_with_options(
                &program,
                readable::ReadableOptions {
                    stack_register: Some(Reg(x86::RSP)),
                    recover_objects: true,
                    coalesce_locals: true,
                },
            )
            .unwrap();
            let indexed_reads: usize = output
                .object_views
                .iter()
                .flat_map(|o| &o.indexed)
                .map(|i| i.read_sites)
                .sum();
            if name == "strided-input" && optimization == "-O2" {
                assert!(
                    indexed_reads > 0,
                    "strided input should expose an indexed view"
                );
            }
            println!(
                "{name} {optimization}: {} objects, {} indexed reads, {} narrow locals",
                output.object_views.len(),
                indexed_reads,
                output
                    .locals
                    .iter()
                    .filter(|v| v.width != nirvana::ir::Width::U64)
                    .count()
            );
            let generated = directory.join(format!("{name}-readable.c"));
            std::fs::write(&generated, output.code.clone() + &readable_harness(&output)).unwrap();
            let compiled = generated.with_extension("o");
            let binary = directory.join(format!("{name}-readable"));
            object(&generated, &compiled, optimization, "nirvana_readable");
            link(&[&compiled], &binary);
            assert_eq!(
                run_fields(&binary, &input_text, 6),
                expected_memory,
                "{name} {optimization}: readable return/state/full-memory digest differs from IR"
            );
            println!(
                "{name} {optimization}: {} instructions, {} stack views, {} inputs agree",
                program.instructions().len(),
                output.stack_views.len(),
                inputs.len()
            );
            comparisons += inputs.len();
        }
    }
    assert_eq!(comparisons, CASES.len() * 2 * inputs.len());
}

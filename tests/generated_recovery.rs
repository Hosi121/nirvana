//! Deterministic source-generated holdouts for the actual compiler-to-readable
//! pipeline. This is extra source coverage, not a claim about real binaries.
//! All generated files live in Scratch and every case is required to lift.

#[path = "support/native.rs"]
mod native;

use native::{Scratch, fixture_root, link, object, run, run_fields};
use nirvana::ir::{Execution, Reg, Width};
use nirvana::{frontend, readable, x86};
use std::collections::BTreeMap;
use std::fmt::Write as _;

const BASE: u64 = 0x1000;
const STATE: usize = 0x1000;
const MEMORY_SIZE: usize = 0x10000;
const VARIANTS: usize = 8;

struct Source {
    name: String,
    code: String,
}

fn sources() -> Vec<Source> {
    let mut sources = vec![];
    for (family, name) in [
        "chain-index",
        "alias-bytes",
        "narrow-select",
        "selected-store",
    ]
    .into_iter()
    .enumerate()
    {
        for seed in [3u64, 10] {
            let statements = match family {
                0 => {
                    r#"
    uint64_t count = (state[3] & UINT64_C(3)) + UINT64_C(1);
    uint64_t sum = state[0] ^ SEED;
    for (uint64_t i = 0; i < count; ++i) {
        uint64_t index = (i + SEED) & UINT64_C(3);
        uint64_t next = (index + UINT64_C(1)) & UINT64_C(3);
        uint64_t before = state[index];
        sum += before ^ (state[next] >> ((i + SEED) & UINT64_C(7)));
        state[index] = sum + state[next];
        state[next] ^= state[index] + SEED;
    }
    return sum ^ state[2];
"#
                }
                1 => {
                    r#"
    unsigned char *bytes = (unsigned char *)state;
    uint64_t count = (state[3] & UINT64_C(3)) + UINT64_C(1);
    uint64_t sum = SEED;
    for (uint64_t i = 0; i < count; ++i) {
        uint64_t index = (i + SEED) & UINT64_C(3);
        uint64_t byte = (state[1] + i + SEED) & UINT64_C(31);
        uint64_t before = state[index];
        bytes[byte] = (unsigned char)((uint64_t)bytes[byte] + before + SEED);
        state[index] ^= (uint64_t)bytes[(byte + UINT64_C(1)) & UINT64_C(31)] << 8;
        sum += state[index] + before;
    }
    return sum ^ state[0];
"#
                }
                2 => {
                    r#"
    volatile uint8_t small = (uint8_t)state[0];
    volatile uint16_t medium = (uint16_t)(state[1] >> (SEED & UINT64_C(7)));
    volatile uint32_t wide = (uint32_t)state[2];
    uint64_t count = (state[3] & UINT64_C(3)) + UINT64_C(1);
    uint64_t sum = SEED;
    for (uint64_t i = 0; i < count; ++i) {
        uint64_t index = (i + SEED) & UINT64_C(3);
        uint64_t selected = (state[index] & UINT64_C(1)) != 0
            ? (uint64_t)medium : (uint64_t)wide;
        medium = (uint16_t)((uint64_t)medium + selected + (uint64_t)small + SEED);
        wide = (uint32_t)((uint64_t)wide ^ state[index]);
        small = (uint8_t)((uint64_t)small + state[(index + UINT64_C(1)) & UINT64_C(3)]);
        state[index] = (uint64_t)medium + (uint64_t)wide + (uint64_t)small;
        sum ^= state[index] + i;
    }
    return sum + (uint64_t)medium;
"#
                }
                3 => {
                    r#"
    uint64_t *selected = (state[3] & UINT64_C(1)) != 0 ? &state[0] : &state[2];
    unsigned char *alias = (unsigned char *)selected;
    uint64_t count = (state[3] & UINT64_C(3)) + UINT64_C(1);
    uint64_t sum = SEED;
    for (uint64_t i = 0; i < count; ++i) {
        uint64_t index = (i + SEED) & UINT64_C(3);
        uint64_t before = *selected;
        *selected = before + state[index] + SEED;
        alias[(i + SEED) & UINT64_C(7)] = (unsigned char)(*selected >> 9);
        state[(index + UINT64_C(1)) & UINT64_C(3)] += *selected;
        sum ^= before + *selected;
    }
    return *selected ^ sum;
"#
                }
                _ => unreachable!(),
            };
            sources.push(Source {
                name: format!("generated-{name}-seed-{seed:02}"),
                code: format!(
                    "#include <stdint.h>\n#define SEED UINT64_C({seed})\nuint64_t FIXTURE_ENTRY(uint64_t state[4]) {{\n{statements}}}\n"
                ),
            });
        }
    }
    sources
}

fn inputs() -> Vec<[u64; 4]> {
    let mut inputs: Vec<_> = include_str!("fixtures/inputs.tsv")
        .lines()
        .filter(|line| !line.is_empty() && !line.starts_with('#'))
        .map(|line| {
            let fields: Vec<_> = line.split('\t').collect();
            std::array::from_fn(|index| fields[index + 1].parse().unwrap())
        })
        .collect();
    assert_eq!(inputs.len(), 63);
    inputs.extend([
        [0x0807_0605_0403_0201, 0x100f_0e0d_0c0b_0a09, u64::MAX, 2],
        [u64::MAX, u64::MAX, u64::MAX, 3],
        [0xff00_ff00_ff00_ff00, 0x00ff_00ff_00ff_00ff, 1 << 63, 1],
        [0xffff, 0xffff_ffff, 0x8000_0000_0000_0001, 0],
    ]);
    inputs
}

fn prepare(input: &[u64; 4]) -> (Vec<u64>, Vec<u8>) {
    let mut registers = vec![0; x86::REGISTER_COUNT];
    registers[x86::RDI] = BASE + STATE as u64;
    registers[x86::RSP] = 0x10000;
    let mut memory: Vec<_> = (0..MEMORY_SIZE)
        .map(|index| (index.wrapping_mul(29).wrapping_add(7)) as u8)
        .collect();
    for (index, value) in input.iter().enumerate() {
        memory[STATE + index * 8..STATE + index * 8 + 8].copy_from_slice(&value.to_le_bytes());
    }
    (registers, memory)
}

fn visible(execution: &Execution) -> Vec<u64> {
    let mut values = vec![execution.value];
    values.extend((0..4).map(|index| {
        u64::from_le_bytes(
            execution.memory[STATE + index * 8..STATE + index * 8 + 8]
                .try_into()
                .unwrap(),
        )
    }));
    values
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
        .map(|register| format!("r[{}]", register.0))
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
fn generated_holdout_sources_match_native_ir_and_readable_c() {
    let scratch = Scratch::new();
    let sources = sources();
    assert_eq!(sources.len(), VARIANTS);
    let inputs = inputs();
    let mut input_text = String::new();
    for input in &inputs {
        writeln!(
            input_text,
            "{} {} {} {}",
            input[0], input[1], input[2], input[3]
        )
        .unwrap();
    }
    for source in &sources {
        std::fs::write(scratch.0.join(format!("{}.c", source.name)), &source.code).unwrap();
    }
    let mut native_references = BTreeMap::new();
    let mut comparisons = 0;
    for optimization in ["-O0", "-O2"] {
        let directory = scratch.0.join(optimization);
        std::fs::create_dir(&directory).unwrap();
        let harness = directory.join("harness.o");
        object(
            &fixture_root().join("harness.c"),
            &harness,
            optimization,
            "fixture",
        );
        for source in &sources {
            let name = &source.name;
            let original = directory.join(format!("{name}.o"));
            object(
                &scratch.0.join(format!("{name}.c")),
                &original,
                optimization,
                "fixture",
            );
            let binary = directory.join(format!("{name}-native"));
            link(&[&original, &harness], &binary);
            let native = run(&binary, &input_text);
            assert_eq!(native.len(), inputs.len(), "{name} {optimization}");
            if optimization == "-O0" {
                native_references.insert(name.clone(), native.clone());
            } else {
                assert_eq!(
                    native, native_references[name],
                    "{name}: native O0/O2 differ"
                );
            }
            let program = frontend::lift_elf(&std::fs::read(&original).unwrap(), "fixture")
                .unwrap_or_else(|error| panic!("{name} {optimization}: {error}"))
                .program;
            let mut expected_memory = Vec::with_capacity(inputs.len());
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
                },
            )
            .unwrap_or_else(|error| panic!("{name} {optimization}: {error}"));
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
                "{name} {optimization}: {} instructions, {} objects, {} indexed views, {} narrow locals; {} cases agree",
                program.instructions().len(),
                output.object_views.len(),
                output
                    .object_views
                    .iter()
                    .map(|object| object.indexed.len())
                    .sum::<usize>(),
                output
                    .locals
                    .iter()
                    .filter(|local| local.width != Width::U64)
                    .count(),
                inputs.len(),
            );
            comparisons += inputs.len();
        }
    }
    assert_eq!(comparisons, VARIANTS * 2 * inputs.len());
    println!(
        "generated holdout: {VARIANTS} variants x 2 optimization levels x {} inputs = {comparisons} native/IR/readable comparisons",
        inputs.len(),
    );
}

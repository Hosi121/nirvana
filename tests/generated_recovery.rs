//! Deterministic source-generated holdouts for the actual compiler-to-readable
//! pipeline. This is extra source coverage, not a claim about real binaries.
//! Every case must lift. Sources, commands, hashes and first failure stay in target/.

#[allow(dead_code)]
#[path = "support/native.rs"]
mod native;

use native::{fixture_root, run, run_fields};
use nirvana::ir::{Execution, Reg, Width};
use nirvana::{frontend, readable, x86};
use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::io::Write as _;
use std::path::{Path, PathBuf};

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

fn exercise_sources(sources: &[Source], inputs: &[[u64; 4]], root: &Path) -> usize {
    let mut input_text = String::new();
    for input in inputs {
        writeln!(
            input_text,
            "{} {} {} {}",
            input[0], input[1], input[2], input[3]
        )
        .unwrap();
    }
    for source in sources {
        std::fs::write(root.join(format!("{}.c", source.name)), &source.code).unwrap();
    }
    let mut native_references = BTreeMap::new();
    let mut comparisons = 0;
    std::fs::write(root.join("inputs.txt"), &input_text).unwrap();
    for optimization in ["-O0", "-O2"] {
        let directory = root.join(optimization);
        std::fs::create_dir(&directory).unwrap();
        let harness = directory.join("harness.o");
        object(
            &fixture_root().join("harness.c"),
            &harness,
            optimization,
            "fixture",
        );
        for source in sources {
            let name = &source.name;
            progress(root, name, optimization, "compile-original");
            let original = directory.join(format!("{name}.o"));
            object(
                &root.join(format!("{name}.c")),
                &original,
                optimization,
                "fixture",
            );
            let binary = directory.join(format!("{name}-native"));
            link(&[&original, &harness], &binary);
            progress(root, name, optimization, "run-original");
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
            progress(root, name, optimization, "lift-and-execute-ir");
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
            progress(root, name, optimization, "emit-readable");
            let output = readable::emit_readable_c_with_options(
                &program,
                readable::ReadableOptions {
                    stack_register: Some(Reg(x86::RSP)),
                    recover_objects: true,
                    coalesce_locals: true,
                    compact_memory: true,
                },
            )
            .unwrap_or_else(|error| panic!("{name} {optimization}: {error}"));
            let generated = directory.join(format!("{name}-readable.c"));
            std::fs::write(&generated, output.code.clone() + &readable_harness(&output)).unwrap();
            progress(root, name, optimization, "compile-and-run-readable");
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
            if let Some(directory) = std::env::var_os("NIRVANA_RECOVERY_ARTIFACTS") {
                let directory = std::path::PathBuf::from(directory);
                std::fs::create_dir_all(&directory).unwrap();
                let opt = optimization.trim_start_matches('-');
                std::fs::copy(
                    root.join(format!("{name}.c")),
                    directory.join(format!("{name}-{opt}.c")),
                )
                .unwrap();
                std::fs::copy(&original, directory.join(format!("{name}-{opt}.o"))).unwrap();
                std::fs::copy(
                    &generated,
                    directory.join(format!("{name}-{opt}-readable.c")),
                )
                .unwrap();
            }
            comparisons += inputs.len();
        }
    }
    assert_eq!(comparisons, sources.len() * 2 * inputs.len());
    println!(
        "generated recovery: {} variants x 2 optimization levels x {} inputs = {comparisons} native/IR/readable comparisons",
        sources.len(),
        inputs.len(),
    );
    comparisons
}

fn json(value: &str) -> String {
    let mut result = String::from("\"");
    for character in value.chars() {
        match character {
            '"' => result.push_str("\\\""),
            '\\' => result.push_str("\\\\"),
            '\n' => result.push_str("\\n"),
            '\r' => result.push_str("\\r"),
            '\t' => result.push_str("\\t"),
            c if c < ' ' => write!(result, "\\u{:04x}", c as u32).unwrap(),
            c => result.push(c),
        }
    }
    result.push('"');
    result
}

fn record_command(root: &Path, arguments: &[String]) {
    let mut file = std::fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(root.join("commands.jsonl"))
        .unwrap();
    writeln!(
        file,
        "[{}]",
        arguments
            .iter()
            .map(|arg| json(arg))
            .collect::<Vec<_>>()
            .join(",")
    )
    .unwrap();
}

fn object(source: &Path, output: &Path, optimization: &str, entry: &str) {
    let mut command = [
        "cc",
        "-std=c11",
        "-Wall",
        "-Wextra",
        "-Werror",
        "-pedantic",
        "-fno-lto",
        optimization,
    ]
    .map(String::from)
    .to_vec();
    command.extend([
        format!("-DFIXTURE_ENTRY={entry}"),
        "-c".to_owned(),
        source.display().to_string(),
        "-o".to_owned(),
        output.display().to_string(),
    ]);
    record_command(output.parent().unwrap().parent().unwrap(), &command);
    native::object(source, output, optimization, entry);
}

fn link(objects: &[&Path], output: &Path) {
    let mut command = vec!["cc".to_owned(), "-fno-lto".to_owned()];
    command.extend(objects.iter().map(|object| object.display().to_string()));
    command.extend(["-o".to_owned(), output.display().to_string()]);
    record_command(output.parent().unwrap().parent().unwrap(), &command);
    native::link(objects, output);
}

fn progress(root: &Path, source: &str, optimization: &str, stage: &str) {
    std::fs::write(
        root.join("progress.json"),
        format!(
            "{{\"source\":{},\"optimization\":{},\"stage\":{}}}\n",
            json(source),
            json(optimization),
            json(stage)
        ),
    )
    .unwrap();
}

fn artifact_directory(label: &str) -> PathBuf {
    let nonce = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let directory = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("target/generated-recovery")
        .join(format!("{label}-{}-{nonce}", std::process::id()));
    std::fs::create_dir_all(&directory).unwrap();
    directory
}

fn files(root: &Path, directory: &Path, output: &mut Vec<PathBuf>) -> std::io::Result<()> {
    for entry in std::fs::read_dir(directory)? {
        let path = entry?.path();
        if path.is_dir() {
            files(root, &path, output)?;
        } else if path
            .file_name()
            .is_some_and(|name| name != "files.sha256" && name != "manifest.json")
        {
            output.push(path.strip_prefix(root).unwrap().to_owned());
        }
    }
    Ok(())
}

fn manifest(
    root: &Path,
    label: &str,
    sources: usize,
    inputs: usize,
    failure: Option<&str>,
) -> Result<(), String> {
    let compiler = std::process::Command::new("cc")
        .arg("--version")
        .output()
        .map_err(|error| error.to_string())?;
    if !compiler.status.success() {
        return Err("cc --version failed".to_owned());
    }
    let mut paths = Vec::new();
    files(root, root, &mut paths).map_err(|error| error.to_string())?;
    paths.sort();
    let hashes = std::process::Command::new("sha256sum")
        .arg("--")
        .args(&paths)
        .current_dir(root)
        .output()
        .map_err(|error| {
            format!("sha256sum is required for recovery artifact manifests: {error}")
        })?;
    if !hashes.status.success() {
        return Err(String::from_utf8_lossy(&hashes.stderr).into_owned());
    }
    std::fs::write(root.join("files.sha256"), hashes.stdout).map_err(|error| error.to_string())?;
    let body = format!(
        "{{\n  \"campaign\":{},\n  \"source_count\":{sources},\n  \"input_count\":{inputs},\n  \"machine_optimizations\":[\"-O0\",\"-O2\"],\n  \"readable_optimization\":\"same as machine object\",\n  \"memory_comparison\":\"IR/readable full 65536-byte guest-memory FNV1a64 digest\",\n  \"compiler\":{},\n  \"architecture\":{},\n  \"os\":{},\n  \"status\":{},\n  \"failure\":{},\n  \"files\":{}\n}}\n",
        json(label),
        json(&String::from_utf8_lossy(&compiler.stdout)),
        json(std::env::consts::ARCH),
        json(std::env::consts::OS),
        json(if failure.is_some() {
            "failed"
        } else {
            "passed"
        }),
        failure.map_or_else(|| "null".to_owned(), json),
        paths.len()
    );
    std::fs::write(root.join("manifest.json"), body).map_err(|error| error.to_string())
}

fn run_preserving(label: &str, sources: Vec<Source>, inputs: Vec<[u64; 4]>) {
    let directory = artifact_directory(label);
    std::fs::write(
        directory.join("generator.rs"),
        include_str!("generated_recovery.rs"),
    )
    .unwrap();
    println!("recovery artifacts: {}", directory.display());
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        exercise_sources(&sources, &inputs, &directory)
    }));
    let failure = result.as_ref().err().map(|payload| {
        payload
            .downcast_ref::<String>()
            .cloned()
            .or_else(|| {
                payload
                    .downcast_ref::<&str>()
                    .map(|text| (*text).to_owned())
            })
            .unwrap_or_else(|| "non-string panic".to_owned())
    });
    if let Some(failure) = &failure {
        std::fs::write(directory.join("failure.txt"), failure).unwrap();
    }
    let recorded = manifest(
        &directory,
        label,
        sources.len(),
        inputs.len(),
        failure.as_deref(),
    );
    if let Err(payload) = result {
        if let Err(error) = recorded {
            eprintln!("manifest error: {error}");
        }
        eprintln!("first failure retained: {}", directory.display());
        std::panic::resume_unwind(payload);
    }
    recorded.unwrap();
}

#[test]
fn generated_holdout_sources_match_native_ir_and_readable_c() {
    let cases = sources();
    assert_eq!(cases.len(), VARIANTS);
    run_preserving("holdout", cases, inputs());
}

struct Random(u64);
impl Random {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
}

fn campaign_sources(count: usize) -> Vec<Source> {
    (0..count).map(|seed| {
        let mut random = Random(0x5a17_9832_946e_f02du64 ^ ((seed as u64 + 1) * 0x0101_0101_0101_0101));
        let constant = random.next();
        let index = random.next() & 3;
        let small = random.next() & 255;
        let medium = random.next() & 65535;
        let mut statements = String::new();
        // All expression operands are unsigned64; shifts are always masked.
        // Character accesses alias only the 32-byte representation of state.
        for _ in 0..3 {
            let operation = random.next() % 7;
            let field = random.next() & 3;
            let mask = random.next() & 63;
            let expression = match operation {
                0 => format!("sum + (state[{field}] ^ UINT64_C({constant}))"),
                1 => format!("sum ^ (state[{field}] << ((count + UINT64_C({mask})) & UINT64_C(63)))"),
                2 => format!("sum + (state[{field}] >> ((count ^ UINT64_C({mask})) & UINT64_C(63)))"),
                3 => format!("ROL64(sum ^ state[{field}], count + UINT64_C({mask}))"),
                4 => format!("ROR64(sum + state[{field}], count ^ UINT64_C({mask}))"),
                5 => format!("__builtin_bswap64(sum ^ state[{field}])"),
                _ => format!("sum * ((state[{field}] & UINT64_C(7)) + UINT64_C(1))"),
            };
            writeln!(statements, "        sum = {expression};").unwrap();
        }
        let branch = match seed % 4 {
            0 => "        if (((sum ^ state[index]) & UINT64_C(3)) == UINT64_C(1)) { state[index] ^= sum; continue; }\n",
            1 => "        if ((state[index] & UINT64_C(1)) != 0) sum += state[next]; else sum ^= state[next];\n",
            2 => "        if (i == UINT64_C(1) && (sum & UINT64_C(1)) != 0) { *selected += sum; continue; }\n",
            _ => "        if (((sum + i) & UINT64_C(7)) < UINT64_C(3)) { sum ^= *selected; } else if ((state[next] & UINT64_C(1)) != 0) { sum += i; }\n",
        };
        let code = format!(r#"#include <stdint.h>
#define ROL64(v,c) (((v) << ((c) & UINT64_C(63))) | ((v) >> ((UINT64_C(0) - (c)) & UINT64_C(63))))
#define ROR64(v,c) (((v) >> ((c) & UINT64_C(63))) | ((v) << ((UINT64_C(0) - (c)) & UINT64_C(63))))
uint64_t FIXTURE_ENTRY(uint64_t state[4]) {{
    volatile uint8_t small = (uint8_t)(state[0] ^ UINT64_C({small}));
    volatile uint16_t medium = (uint16_t)(state[1] + UINT64_C({medium}));
    volatile uint32_t wide = (uint32_t)state[2];
    unsigned char *bytes = (unsigned char *)state;
    uint64_t *selected = (state[3] & UINT64_C(1)) != 0 ? &state[{index}] : &state[2];
    uint64_t trips = (state[3] & UINT64_C(3)) + UINT64_C(1);
    uint64_t sum = state[0] ^ UINT64_C({constant});
    for (uint64_t i = 0; i < trips; ++i) {{
        uint64_t index = (i + state[1] + UINT64_C({index})) & UINT64_C(3);
        uint64_t next = (index + UINT64_C(1)) & UINT64_C(3);
        uint64_t count = (state[1] + i) & UINT64_C(63);
{statements}{branch}        uint64_t before = *selected;
        *selected = ROL64(before + sum, count);
        uint64_t byte = (sum ^ state[next] ^ i) & UINT64_C(31);
        bytes[byte] = (unsigned char)((uint64_t)bytes[byte] + (uint64_t)small + sum);
        medium = (uint16_t)((uint64_t)medium + (uint64_t)small + sum);
        wide = __builtin_bswap32((uint32_t)((uint64_t)wide ^ state[index]));
        small = (uint8_t)((uint64_t)small + (uint64_t)medium + i);
        state[index] ^= (uint64_t)medium + (uint64_t)wide + (uint64_t)small;
        sum = ROR64(sum ^ *selected, (count + UINT64_C(17)) & UINT64_C(63));
    }}
    state[3] ^= (uint64_t)medium + (uint64_t)wide + (uint64_t)small;
    return __builtin_bswap64(sum) ^ state[0];
}}
"#);
        Source { name: format!("campaign-seed-{seed:02}"), code }
    }).collect()
}

fn campaign_inputs() -> Vec<[u64; 4]> {
    let mut result = inputs();
    for count in [0, 1, 7, 8, 15, 16, 31, 32, 63, 64, 65, 255, u64::MAX] {
        for value in [0, 1, u64::MAX, 0x8000_0000_ffff_ffff] {
            result.push([value, count, !value, count & 3]);
        }
    }
    result
}

/// Explicit bounded opt-in: NIRVANA_RECOVERY_CASES=1..64 (default64).
/// Requires cc and sha256sum; all sources/objects/C/commands stay in target/.
#[test]
#[ignore = "bounded differential campaign; set NIRVANA_RECOVERY_CASES=16 or64"]
fn seeded_pipeline_differential_campaign() {
    let count = std::env::var("NIRVANA_RECOVERY_CASES").map_or(64, |value| {
        value
            .parse::<usize>()
            .expect("NIRVANA_RECOVERY_CASES must be an integer in1..64")
    });
    assert!(
        (1..=64).contains(&count),
        "NIRVANA_RECOVERY_CASES must be in1..64"
    );
    run_preserving("seeded-v1", campaign_sources(count), campaign_inputs());
}

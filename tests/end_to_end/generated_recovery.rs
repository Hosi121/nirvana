//! Deterministic source-generated holdouts for the actual compiler-to-readable
//! pipeline. This is extra source coverage, not a claim about real binaries.
//! Every case must lift. Sources, commands, hashes and first failure stay in target/.

use crate::support::native;

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

#[derive(Debug, Eq, PartialEq)]
struct Profiles {
    // Canonical compiler flags, preserving requested order. Effective always
    // starts with O0 so every optimized native result has the same baseline.
    requested: Vec<&'static str>,
    effective: Vec<&'static str>,
}

/// Comma-separated names, not arbitrary compiler flags. Bound before parsing.
fn parse_profiles(value: Option<&str>) -> Result<Profiles, String> {
    let mut requested = Vec::new();
    if let Some(value) = value {
        if value.len() > 64 {
            return Err("NIRVANA_RECOVERY_PROFILES exceeds 64 bytes".to_owned());
        }
        for token in value.split(',') {
            if requested.len() == 5 {
                return Err("NIRVANA_RECOVERY_PROFILES allows at most 5 profiles".to_owned());
            }
            let flag = match token.trim() {
                "O0" => "-O0",
                "O1" => "-O1",
                "O2" => "-O2",
                "Os" => "-Os",
                "O3" => "-O3",
                "" => return Err("NIRVANA_RECOVERY_PROFILES contains an empty profile".to_owned()),
                _ => return Err("NIRVANA_RECOVERY_PROFILES allows only O0,O1,O2,Os,O3".to_owned()),
            };
            if requested.contains(&flag) {
                return Err(format!("NIRVANA_RECOVERY_PROFILES repeats {flag}"));
            }
            requested.push(flag);
        }
    } else {
        requested.extend(["-O0", "-O2"]);
    }
    let mut effective = vec!["-O0"];
    effective.extend(
        requested
            .iter()
            .copied()
            .filter(|profile| *profile != "-O0"),
    );
    Ok(Profiles {
        requested,
        effective,
    })
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
    let mut inputs: Vec<_> = include_str!("../fixtures/inputs.tsv")
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

fn exercise_sources(
    sources: &[Source],
    inputs: &[[u64; 4]],
    root: &Path,
    optimizations: &[&str],
) -> usize {
    assert_eq!(optimizations.first(), Some(&"-O0"));
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
    for &optimization in optimizations {
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
                    "{name}: native O0/{optimization} differ"
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
    assert_eq!(
        comparisons,
        sources.len() * optimizations.len() * inputs.len()
    );
    println!(
        "generated recovery: {} variants x {} optimization levels x {} inputs = {comparisons} native/IR/readable comparisons",
        sources.len(),
        optimizations.len(),
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

fn json_array(values: &[&str]) -> String {
    format!(
        "[{}]",
        values
            .iter()
            .map(|value| json(value))
            .collect::<Vec<_>>()
            .join(",")
    )
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
    profiles: &Profiles,
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
        "{{\n  \"campaign\":{},\n  \"source_count\":{sources},\n  \"input_count\":{inputs},\n  \"requested_profiles\":{},\n  \"effective_profiles\":{},\n  \"machine_optimizations\":{},\n  \"expected_comparisons\":{},\n  \"readable_optimization\":\"same as machine object\",\n  \"memory_comparison\":\"IR/readable full 65536-byte guest-memory FNV1a64 digest\",\n  \"compiler\":{},\n  \"architecture\":{},\n  \"os\":{},\n  \"status\":{},\n  \"failure\":{},\n  \"files\":{}\n}}\n",
        json(label),
        json_array(&profiles.requested),
        json_array(&profiles.effective),
        json_array(&profiles.effective),
        sources * inputs * profiles.effective.len(),
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

fn run_preserving(label: &str, sources: Vec<Source>, inputs: Vec<[u64; 4]>, profiles: Profiles) {
    let directory = artifact_directory(label);
    std::fs::write(
        directory.join("generator.rs"),
        include_str!("generated_recovery.rs"),
    )
    .unwrap();
    println!("recovery artifacts: {}", directory.display());
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        exercise_sources(&sources, &inputs, &directory, &profiles.effective)
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
        &profiles,
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
    // The regular test deliberately never reads the profile environment.
    run_preserving("holdout", cases, inputs(), parse_profiles(None).unwrap());
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
/// Optional NIRVANA_RECOVERY_PROFILES=O0,O1,O2,Os,O3; default O0,O2.
/// Missing O0 is prepended. Requires cc/sha256sum; artifacts stay in target/.
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
    let requested = match std::env::var("NIRVANA_RECOVERY_PROFILES") {
        Ok(value) => Some(value),
        Err(std::env::VarError::NotPresent) => None,
        Err(std::env::VarError::NotUnicode(_)) => {
            panic!("NIRVANA_RECOVERY_PROFILES must be Unicode")
        }
    };
    let profiles = parse_profiles(requested.as_deref()).unwrap_or_else(|error| panic!("{error}"));
    run_preserving(
        "seeded-v1",
        campaign_sources(count),
        campaign_inputs(),
        profiles,
    );
}

#[test]
fn profile_parser_defaults_and_preserves_requests_while_prepending_baseline() {
    let default = parse_profiles(None).unwrap();
    assert_eq!(default.requested, ["-O0", "-O2"]);
    assert_eq!(default.effective, default.requested);
    let only = parse_profiles(Some("O3")).unwrap();
    assert_eq!(only.requested, ["-O3"]);
    assert_eq!(only.effective, ["-O0", "-O3"]);
    let reordered = parse_profiles(Some(" O3, O1, O0 ")).unwrap();
    assert_eq!(reordered.requested, ["-O3", "-O1", "-O0"]);
    assert_eq!(reordered.effective, ["-O0", "-O3", "-O1"]);
    let full = parse_profiles(Some("O0,O1,O2,Os,O3")).unwrap();
    assert_eq!(full.requested.len(), 5);
    assert_eq!(full.requested, full.effective);
    let filled = parse_profiles(Some("O1,O2,Os,O3")).unwrap();
    assert_eq!(filled.effective, full.effective);
}

#[test]
fn profile_parser_rejects_empty_duplicate_and_unlisted_flags() {
    for value in [
        "",
        "  ",
        ",",
        "O0,",
        ",O2",
        "O1,,O3",
        "O0,O0",
        "O2, O2",
        "O4",
        "Ofast",
        "-O2",
        "o0",
        "OS",
        "O2,-march=native",
        "O0,O1,O2,Os,O3,O0",
    ] {
        assert!(parse_profiles(Some(value)).is_err(), "{value:?}");
    }
}

#[test]
fn profile_parser_checks_byte_budget_before_splitting() {
    let boundary = format!("{:>64}", "O3");
    assert_eq!(
        parse_profiles(Some(&boundary)).unwrap().effective,
        ["-O0", "-O3"]
    );
    assert!(parse_profiles(Some(&(" ".to_owned() + &boundary))).is_err());
    assert!(parse_profiles(Some(&"O3,".repeat(1000))).is_err());
}

/// A separate deterministic CFG corpus. Every dynamic cycle consumes a bound:
/// at most 4x4 inner iterations, or at most 16 explicit fuel units. Character
/// accesses stay within state[0..4]'s 32-byte representation. No generated
/// expression relies on signed overflow, input range, or uninitialized locals.
fn control_flow_sources(count: usize) -> Vec<Source> {
    assert!((1..=64).contains(&count));
    (0..count)
        .map(|seed| {
            let mut random = Random(
                0xd13f_5a77_369e_c02bu64
                    ^ ((seed as u64 + 1) * 0x0101_0101_0101_0101),
            );
            let constant = random.next();
            let lane = random.next() & 3;
            let shift = random.next() & 63;
            let tag = random.next() & 7;
            let (family, statements) = match seed % 5 {
                0 => (
                    "nested",
                    r#"
    uint64_t outer = (state[3] & UINT64_C(3)) + UINT64_C(1);
    uint64_t inner = (state[2] & UINT64_C(3)) + UINT64_C(1);
    for (uint64_t i = 0; i < outer; ++i) {
        for (uint64_t j = 0; j < inner; ++j) {
            uint64_t index = (i + j + LANE) & UINT64_C(3);
            uint64_t before = state[index];
            sum += before ^ (i + j + SEED);
            if (((before ^ sum) & UINT64_C(7)) == TAG) {
                uint64_t byte = (sum + i + j) & UINT64_C(31);
                bytes[byte] = (unsigned char)((uint64_t)bytes[byte] ^ sum);
                continue;
            }
            if (((before + sum + j) & UINT64_C(7)) == (TAG ^ UINT64_C(3))) {
                state[index] = sum;
                break;
            }
            state[index] = before + sum;
            sum ^= state[(index + UINT64_C(1)) & UINT64_C(3)] >> ((i + j + SHIFT) & UINT64_C(63));
        }
        state[(i + LANE) & UINT64_C(3)] ^= sum + i;
    }
    state[3] ^= sum;
    return sum ^ state[LANE];
"#,
                ),
                1 => (
                    "post-test",
                    r#"
    uint64_t trips = (state[3] & UINT64_C(15)) + UINT64_C(1);
    uint64_t stop = state[2] & UINT64_C(7);
    uint64_t i = 0;
    do {
        uint64_t index = (i + LANE) & UINT64_C(3);
        uint64_t before = state[index];
        sum += before ^ SEED;
        state[index] = sum ^ before;
        ++i;
        if (((sum + i) & UINT64_C(3)) == 0) {
            uint64_t byte = (sum ^ i) & UINT64_C(31);
            bytes[byte] = (unsigned char)((uint64_t)bytes[byte] + (sum >> ((i + SHIFT) & UINT64_C(63))));
            continue;
        }
        if ((sum & UINT64_C(7)) == stop) break;
        sum ^= state[(index + UINT64_C(1)) & UINT64_C(3)];
    } while (i < trips);
    state[LANE] += sum;
    return sum ^ state[3];
"#,
                ),
                2 => (
                    "shared-tail",
                    r#"
    uint64_t trips = (state[3] & UINT64_C(7)) + UINT64_C(1);
    for (uint64_t i = 0; i < trips; ++i) {
        uint64_t index = (i + LANE) & UINT64_C(3);
        uint64_t next = (index + UINT64_C(1)) & UINT64_C(3);
        uint64_t before = state[index];
        if ((before & UINT64_C(1)) != 0) goto odd;
        sum += state[next] ^ SEED;
        bytes[(sum + i) & UINT64_C(31)] = (unsigned char)(sum >> ((i + SHIFT) & UINT64_C(63)));
        goto shared;
odd:
        sum ^= state[next] + SEED;
        state[next] += before;
shared:
        state[index] = sum + state[next];
        sum ^= state[index] + before;
    }
    state[3] += sum;
    return state[LANE] ^ sum;
"#,
                ),
                3 => (
                    "two-entry",
                    r#"
    uint64_t fuel = (state[3] & UINT64_C(15)) + UINT64_C(1);
    uint64_t index = 0;
    uint64_t before = 0;
    uint64_t byte = 0;
    if ((state[0] & UINT64_C(1)) != 0) goto left;
    goto right;
left:
    if (fuel == 0) goto done;
    --fuel;
    index = (sum + fuel + LANE) & UINT64_C(3);
    before = state[index];
    sum += before ^ SEED;
    state[index] = sum + before;
    if ((sum & UINT64_C(1)) != 0) goto right;
    goto left;
right:
    if (fuel == 0) goto done;
    --fuel;
    index = (sum ^ fuel ^ LANE) & UINT64_C(3);
    before = state[index];
    sum ^= before + SEED;
    byte = (sum + fuel) & UINT64_C(31);
    bytes[byte] = (unsigned char)((uint64_t)bytes[byte] + (sum >> ((before + SHIFT) & UINT64_C(63))));
    if ((sum & UINT64_C(2)) != 0) goto left;
    goto right;
done:
    state[3] ^= sum;
    return sum + state[LANE];
"#,
                ),
                _ => (
                    "early-return",
                    r#"
    uint64_t trips = (state[3] & UINT64_C(15)) + UINT64_C(1);
    uint64_t stop = state[2] & UINT64_C(7);
    for (uint64_t i = 0; i < trips; ++i) {
        uint64_t index = (i + LANE) & UINT64_C(3);
        uint64_t next = (index + UINT64_C(1)) & UINT64_C(3);
        uint64_t before = state[index];
        if (((sum ^ before) & UINT64_C(7)) == stop) {
            state[index] = sum + before;
            return state[index] ^ state[next];
        }
        bytes[(sum + i) & UINT64_C(31)] = (unsigned char)(before >> ((i + SHIFT) & UINT64_C(63)));
        sum += state[index] ^ SEED;
        if ((before & UINT64_C(3)) == 0) continue;
        if ((sum & UINT64_C(15)) == (stop + UINT64_C(1))) {
            state[next] ^= sum;
            break;
        }
        state[index] = sum + state[next];
    }
    state[3] += sum;
    return sum ^ state[LANE];
"#,
                ),
            };
            Source {
                name: format!("cfg-{family}-seed-{seed:02}"),
                code: format!(
                    "#include <stdint.h>\n#define SEED UINT64_C({constant})\n#define LANE UINT64_C({lane})\n#define SHIFT UINT64_C({shift})\n#define TAG UINT64_C({tag})\nuint64_t FIXTURE_ENTRY(uint64_t state[4]) {{\n    unsigned char *bytes = (unsigned char *)state;\n    uint64_t sum = state[0] ^ SEED;\n{statements}}}\n"
                ),
            }
        })
        .collect()
}

/// Opt-in CFG/loop holdout. Shares the existing ABI, 119 inputs, profile
/// selector and first-failure artifacts; source count1..64 defaults to16.
#[test]
#[ignore = "bounded CFG differential campaign; optional NIRVANA_RECOVERY_CASES=1..64"]
fn seeded_control_flow_differential_campaign() {
    let count = std::env::var("NIRVANA_RECOVERY_CASES").map_or(16, |value| {
        value
            .parse::<usize>()
            .expect("NIRVANA_RECOVERY_CASES must be an integer in1..64")
    });
    assert!(
        (1..=64).contains(&count),
        "NIRVANA_RECOVERY_CASES must be in1..64"
    );
    let requested = match std::env::var("NIRVANA_RECOVERY_PROFILES") {
        Ok(value) => Some(value),
        Err(std::env::VarError::NotPresent) => None,
        Err(std::env::VarError::NotUnicode(_)) => {
            panic!("NIRVANA_RECOVERY_PROFILES must be Unicode")
        }
    };
    let profiles = parse_profiles(requested.as_deref()).unwrap_or_else(|error| panic!("{error}"));
    let inputs = campaign_inputs();
    assert_eq!(inputs.len(), 119);
    run_preserving("cfg-v1", control_flow_sources(count), inputs, profiles);
}

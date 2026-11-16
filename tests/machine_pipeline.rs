//! C -> ELF machine code -> self-contained decoder/lifter -> IR -> C -> native.
//! No disassembler output or handwritten IR is used as frontend input.

#[path = "support/native.rs"]
mod native;

use native::{Scratch, fixture_root, link, object, run};
use nirvana::{emit, frontend, structure::StructuredFunction, x86};
use std::fmt::Write as _;

const BASE: u64 = 0x1000;
const STATE: usize = 0x1000;
const MEMORY_SIZE: usize = 0x10000;

fn prepare(input: &[u64; 4]) -> (Vec<u64>, Vec<u8>) {
    let mut registers = vec![0; x86::REGISTER_COUNT];
    registers[x86::RDI] = BASE + STATE as u64;
    registers[x86::RSP] = 0x10000;
    let mut memory = vec![0; MEMORY_SIZE];
    for (index, value) in input.iter().enumerate() {
        memory[STATE + index * 8..STATE + index * 8 + 8].copy_from_slice(&value.to_le_bytes());
    }
    (registers, memory)
}

fn visible_result(execution: &nirvana::ir::Execution) -> Vec<u64> {
    let mut result = vec![execution.value];
    for index in 0..4 {
        result.push(u64::from_le_bytes(
            execution.memory[STATE + index * 8..STATE + index * 8 + 8]
                .try_into()
                .unwrap(),
        ));
    }
    result
}

fn generated_harness(uses_memory: bool) -> String {
    let call = if uses_memory {
        "nirvana_fn(r, memory, UINT64_C(4096), sizeof(memory))"
    } else {
        "nirvana_fn(r)"
    };
    format!(
        r#"
#include <inttypes.h>
#include <stdio.h>
#include <string.h>
int main(void) {{
    uint64_t input[4];
    while (scanf("%" SCNu64 " %" SCNu64 " %" SCNu64 " %" SCNu64,
                 &input[0], &input[1], &input[2], &input[3]) == 4) {{
        uint64_t r[32] = {{0}};
        uint8_t memory[65536];
        memset(memory, 0, sizeof(memory));
        r[7] = UINT64_C(8192); r[4] = UINT64_C(65536);
        for (unsigned i = 0; i < 4; ++i)
            for (unsigned j = 0; j < 8; ++j) memory[4096 + i * 8 + j] = (uint8_t)(input[i] >> (j * 8));
        uint64_t value = {call};
        for (unsigned i = 0; i < 4; ++i) {{
            input[i] = 0;
            for (unsigned j = 0; j < 8; ++j) input[i] |= (uint64_t)memory[4096 + i * 8 + j] << (j * 8);
        }}
        printf("%" PRIu64 " %" PRIu64 " %" PRIu64 " %" PRIu64 " %" PRIu64 "\n",
               value, input[0], input[1], input[2], input[3]);
    }}
    return 0;
}}
"#
    )
}

#[test]
fn compiled_c_fixtures_round_trip_through_real_machine_code_and_ir() {
    let scratch = Scratch::new();
    let root = fixture_root();
    let inputs: Vec<[u64; 4]> = include_str!("fixtures/inputs.tsv")
        .lines()
        .filter(|line| !line.is_empty() && !line.starts_with('#'))
        .map(|line| {
            let fields: Vec<_> = line.split('\t').collect();
            std::array::from_fn(|i| fields[i + 1].parse().unwrap())
        })
        .collect();
    let cases: Vec<_> = include_str!("fixtures/cases.tsv")
        .lines()
        .filter(|line| !line.is_empty() && !line.starts_with('#'))
        .map(|line| line.split('\t').next().unwrap())
        .collect();
    let mut input_text = String::new();
    for input in &inputs {
        writeln!(
            input_text,
            "{} {} {} {}",
            input[0], input[1], input[2], input[3]
        )
        .unwrap();
    }
    let mut lifted = 0;
    let mut structured = 0;
    let mut comparisons = 0;
    for optimization in ["-O0", "-O2"] {
        let directory = scratch.0.join(optimization);
        std::fs::create_dir(&directory).unwrap();
        let harness = directory.join("harness.o");
        let helpers = directory.join("helpers.o");
        object(&root.join("harness.c"), &harness, optimization, "fixture");
        object(&root.join("helpers.c"), &helpers, optimization, "fixture");
        for &name in &cases {
            let object_path = directory.join(format!("{name}.o"));
            object(
                &root.join("cases").join(format!("{name}.c")),
                &object_path,
                optimization,
                "fixture",
            );
            let object_bytes = std::fs::read(&object_path).unwrap();
            let function = match frontend::lift_elf(&object_bytes, "fixture") {
                Ok(function) => function,
                Err(error) => {
                    // These failures require linking/runtime features outside
                    // the current contract, not a different source or flags.
                    let allowed = matches!(name, "switch" | "array-walk" | "call-chain")
                        || (name == "nonlocal-exit" && optimization == "-O2");
                    assert!(
                        allowed && matches!(&error, frontend::FrontendError::Relocations(_)),
                        "unexpected frontend failure for {name} {optimization}: {error}"
                    );
                    println!("unsupported {name} {optimization}: {error}");
                    continue;
                }
            };
            lifted += 1;
            let program = function.program;
            let tree = StructuredFunction::recover(&program).ok();
            structured += usize::from(tree.is_some());
            let original_binary = directory.join(format!("{name}-original"));
            link(&[&object_path, &harness, &helpers], &original_binary);
            let native = run(&original_binary, &input_text);
            assert_eq!(native.len(), inputs.len());
            for (input, expected) in inputs.iter().zip(&native) {
                let (registers, memory) = prepare(input);
                let execution = program
                    .execute_with_memory(&registers, BASE, &memory, 10_000)
                    .unwrap_or_else(|error| {
                        panic!("{name} {optimization}, input={input:?}: {error}")
                    });
                assert_eq!(
                    &visible_result(&execution),
                    expected,
                    "{name} {optimization}, input={input:?}"
                );
                if let Some(tree) = &tree {
                    assert_eq!(
                        tree.execute_with_memory(&registers, BASE, &memory, 10_000)
                            .unwrap(),
                        execution,
                        "structured IR differs for {name} {optimization}, input={input:?}"
                    );
                }
                comparisons += 1;
            }
            let output = emit::emit_c(&program);
            let source = directory.join(format!("{name}-lifted.c"));
            std::fs::write(
                &source,
                output.code + &generated_harness(program.uses_memory()),
            )
            .unwrap();
            let compiled = directory.join(format!("{name}-lifted.o"));
            object(&source, &compiled, optimization, "nirvana_fn");
            let binary = directory.join(format!("{name}-lifted"));
            link(&[&compiled], &binary);
            assert_eq!(
                run(&binary, &input_text),
                native,
                "machine-derived C differs for {name} {optimization}"
            );
        }
    }
    assert!(
        lifted >= 33,
        "only {lifted} of 40 C/optimization configurations lifted"
    );
    assert_eq!(comparisons, lifted * 63);
    println!(
        "machine pipeline: {lifted}/40 configurations lifted, {structured} structured, {comparisons} inputs match native C and recompiled lifted C"
    );
}

#[test]
fn cli_runs_a_real_object_and_reports_unsupported_input() {
    let scratch = Scratch::new();
    let source = fixture_root().join("cases/diamond.c");
    let object_path = scratch.0.join("diamond.o");
    object(&source, &object_path, "-O2", "fixture");
    let result = std::process::Command::new(env!("CARGO_BIN_EXE_nirvana"))
        .arg(&object_path)
        .args(["--run", "12,2,3,4"])
        .output()
        .unwrap();
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
    assert_eq!(
        String::from_utf8(result.stdout).unwrap().trim(),
        "32 12 32 3 4"
    );
    let raw = scratch.0.join("unsupported.bin");
    std::fs::write(&raw, [0x0f, 0x0b]).unwrap();
    let result = std::process::Command::new(env!("CARGO_BIN_EXE_nirvana"))
        .arg(raw)
        .args(["--raw", "--base", "0x1000"])
        .output()
        .unwrap();
    assert!(!result.status.success());
    assert!(String::from_utf8_lossy(&result.stderr).contains("0x1000"));
}

#[test]
fn machine_multiply_overflow_affects_recompiled_c_like_the_native_compiler() {
    // mov rax,[rdi]; imul rax,[rdi+8]; seto al; movzx eax,al; ret.
    // This makes the high product and signed-overflow flag externally visible.
    let code = [
        0x48, 0x8b, 0x07, 0x48, 0x0f, 0xaf, 0x47, 0x08, 0x0f, 0x90, 0xc0, 0x0f, 0xb6, 0xc0, 0xc3,
    ];
    let program = x86::lift(&code, 0, 0).unwrap();
    let scratch = Scratch::new();
    let original = scratch.0.join("original.c");
    std::fs::write(&original, "#include <stdint.h>\nuint64_t fixture(uint64_t *r) { int64_t result; return __builtin_mul_overflow((int64_t)r[0], (int64_t)r[1], &result); }\n").unwrap();
    let values = [0, 1, 2, (1u64 << 63) - 1, 1 << 63, u64::MAX - 1, u64::MAX];
    let mut text = String::new();
    let mut expected = Vec::new();
    for left in values {
        for right in values {
            let input = [left, right, 0, 0];
            writeln!(text, "{left} {right} 0 0").unwrap();
            let (registers, memory) = prepare(&input);
            expected.push(visible_result(
                &program
                    .execute_with_memory(&registers, BASE, &memory, 10)
                    .unwrap(),
            ));
        }
    }
    for optimization in ["-O0", "-O2"] {
        let object_path = scratch.0.join(format!("original{optimization}.o"));
        let harness = scratch.0.join(format!("harness{optimization}.o"));
        let native = scratch.0.join(format!("original{optimization}"));
        object(&original, &object_path, optimization, "fixture");
        object(
            &fixture_root().join("harness.c"),
            &harness,
            optimization,
            "fixture",
        );
        link(&[&object_path, &harness], &native);
        assert_eq!(run(&native, &text), expected);
        let source = scratch.0.join(format!("lifted{optimization}.c"));
        std::fs::write(
            &source,
            emit::emit_c(&program).code + &generated_harness(true),
        )
        .unwrap();
        let object_path = scratch.0.join(format!("lifted{optimization}.o"));
        let binary = scratch.0.join(format!("lifted{optimization}"));
        object(&source, &object_path, optimization, "nirvana_fn");
        link(&[&object_path], &binary);
        assert_eq!(run(&binary, &text), expected);
    }
}

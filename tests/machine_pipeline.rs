//! C -> ELF machine code -> self-contained decoder/lifter -> IR -> C -> native.
//! No disassembler output or handwritten IR is used as frontend input.

#[path = "support/native.rs"]
mod native;

use native::{Scratch, fixture_root, link, object, run, run_fields};
use nirvana::observe::{Comparison, Contract};
use nirvana::structure_verify;
use nirvana::{emit, frontend, readable, reduce, structure::StructuredFunction, x86};
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
    harness_for(call, false)
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
    harness_for(&format!("nirvana_readable({})", arguments.join(", ")), true)
}

fn memory_digest(memory: &[u8]) -> u64 {
    memory.iter().fold(0xcbf29ce484222325, |hash, byte| {
        (hash ^ u64::from(*byte)).wrapping_mul(0x100000001b3)
    })
}

fn harness_for(call: &str, with_digest: bool) -> String {
    let digest = if with_digest {
        "uint64_t hash = UINT64_C(14695981039346656037);\n        for (unsigned i = 0; i < sizeof(memory); ++i) hash = (hash ^ memory[i]) * UINT64_C(1099511628211);"
    } else {
        ""
    };
    let digest_format = if with_digest { " %\" PRIu64 \"" } else { "" };
    let digest_argument = if with_digest { ", hash" } else { "" };
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
        {digest}
        printf("%" PRIu64 " %" PRIu64 " %" PRIu64 " %" PRIu64 " %" PRIu64 "{digest_format}\n",
               value, input[0], input[1], input[2], input[3]{digest_argument});
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
    let mut original_assignments = 0;
    let mut reduced_assignments = 0;
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
            let reduced = reduce::reduce(&program).unwrap();
            let tree = StructuredFunction::recover(&program).ok();
            if let Some(tree) = &tree {
                let reachable_steps: usize = program
                    .cfg()
                    .reachable_blocks()
                    .iter()
                    .map(|&id| program.cfg().block(id).instructions.len())
                    .sum();
                assert_eq!(tree.evidence().original_steps, reachable_steps);
                assert_eq!(
                    structure_verify::validate(&program, tree.body()).unwrap(),
                    tree.evidence()
                );
            }
            structured += usize::from(tree.is_some());
            let original_binary = directory.join(format!("{name}-original"));
            link(&[&object_path, &harness, &helpers], &original_binary);
            let native = run(&original_binary, &input_text);
            assert_eq!(native.len(), inputs.len());
            let mut memory_results = Vec::new();
            for (input, expected) in inputs.iter().zip(&native) {
                let (registers, memory) = prepare(input);
                let report = program
                    .run_with_memory(&registers, BASE, &memory, 10_000)
                    .unwrap_or_else(|error| {
                        panic!("{name} {optimization}, input={input:?}: {error}")
                    });
                let execution = report.clone().into_execution().unwrap();
                assert_eq!(
                    &visible_result(&execution),
                    expected,
                    "{name} {optimization}, input={input:?}"
                );
                let reduced_report = reduced
                    .run_with_memory(&registers, BASE, &memory, 10_000)
                    .unwrap();
                assert_eq!(
                    Contract::return_memory()
                        .with_instruction_trace()
                        .compare(&report, &reduced_report),
                    Comparison::MatchForInput,
                    "reduction differs for {name} {optimization}, input={input:?}"
                );
                let mut memory_result = expected.clone();
                memory_result.push(memory_digest(&execution.memory));
                memory_results.push(memory_result);
                if let Some(tree) = &tree {
                    assert_eq!(
                        tree.run_with_memory(&registers, BASE, &memory, 10_000)
                            .unwrap(),
                        report,
                        "structured IR differs for {name} {optimization}, input={input:?}"
                    );
                }
                comparisons += 1;
            }
            let output = emit::emit_c(&program);
            assert_eq!(
                output.structure_evidence,
                tree.as_ref().map(StructuredFunction::evidence)
            );
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
            let baseline = readable::emit_readable_c(&program).unwrap();
            let output = readable::emit_readable_c_with_options(
                &program,
                readable::ReadableOptions {
                    stack_register: Some(nirvana::ir::Reg(x86::RSP)),
                    recover_objects: true,
                },
            )
            .unwrap();
            assert_eq!(baseline.parameters, output.parameters);
            assert_eq!(baseline.structure_evidence, output.structure_evidence);
            if optimization == "-O0" && matches!(name, "sum" | "struct-fields") {
                assert!(
                    output.stack_views.len() >= 4,
                    "{name}: {:?}",
                    output.stack_views
                );
                assert!(output.code.contains("nirvana_view_load(&m, stack_"));
                assert!(output.code.contains("nirvana_view_store(&m, stack_"));
            }
            println!(
                "{name} {optimization}: {} stack views, {} named reads, {} named writes",
                output.stack_views.len(),
                output
                    .stack_views
                    .iter()
                    .map(|v| v.read_sites)
                    .sum::<usize>(),
                output
                    .stack_views
                    .iter()
                    .map(|v| v.write_sites)
                    .sum::<usize>()
            );
            let reduced_tree = StructuredFunction::recover(reduced.program()).ok();
            assert_eq!(
                output.structure_evidence,
                reduced_tree.as_ref().map(StructuredFunction::evidence)
            );
            original_assignments += output.reduction_stats.original_assignments;
            reduced_assignments += output.reduction_stats.reduced_assignments;
            let source = directory.join(format!("{name}-readable.c"));
            std::fs::write(&source, output.code.clone() + &readable_harness(&output)).unwrap();
            let compiled = directory.join(format!("{name}-readable.o"));
            object(&source, &compiled, optimization, "nirvana_readable");
            let binary = directory.join(format!("{name}-readable"));
            link(&[&compiled], &binary);
            assert_eq!(
                run_fields(&binary, &input_text, 6),
                memory_results,
                "readable C differs for {name} {optimization}"
            );
            println!(
                "{name} {optimization}: assignments {} -> {}",
                output.reduction_stats.original_assignments,
                output.reduction_stats.reduced_assignments
            );
        }
    }
    assert!(
        lifted >= 33,
        "only {lifted} of 40 C/optimization configurations lifted"
    );
    assert_eq!(comparisons, lifted * 63);
    assert!(reduced_assignments < original_assignments);
    println!(
        "readable mode: {original_assignments} -> {reduced_assignments} assignments across {lifted} configurations"
    );
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
    let result = std::process::Command::new(env!("CARGO_BIN_EXE_nirvana"))
        .arg(&object_path)
        .args(["--emit", "readable-c"])
        .output()
        .unwrap();
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
    let code = String::from_utf8(result.stdout).unwrap();
    assert!(code.contains("nirvana_readable("));
    assert!(!code.contains("r["));
    let result = std::process::Command::new(env!("CARGO_BIN_EXE_nirvana"))
        .arg(&object_path)
        .args(["--emit", "structured-cfg"])
        .output()
        .unwrap();
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
    assert!(
        String::from_utf8(result.stdout)
            .unwrap()
            .starts_with("digraph structured_flow")
    );
    assert!(
        String::from_utf8(result.stderr)
            .unwrap()
            .contains("structured AST accepted under structured-flow-v1")
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

    // A real loop remains cyclic in the reconstructed graph; it is not a DAG.
    let looping = scratch.0.join("loop.bin");
    std::fs::write(&looping, [0xeb, 0xfe]).unwrap();
    let result = std::process::Command::new(env!("CARGO_BIN_EXE_nirvana"))
        .arg(looping)
        .args(["--raw", "--emit", "structured-cfg"])
        .output()
        .unwrap();
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
    let dot = String::from_utf8(result.stdout).unwrap();
    assert!(dot.contains("step 0x0"));
    assert!(dot.contains("route"));
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
    let mut expected_memory = Vec::new();
    let reduced = reduce::reduce(&program).unwrap();
    for left in values {
        for right in values {
            let input = [left, right, 0, 0];
            writeln!(text, "{left} {right} 0 0").unwrap();
            let (registers, memory) = prepare(&input);
            let execution = program
                .execute_with_memory(&registers, BASE, &memory, 10)
                .unwrap();
            assert_eq!(
                reduced
                    .execute_with_memory(&registers, BASE, &memory, 10)
                    .unwrap(),
                reduce::Observation {
                    value: execution.value,
                    memory: execution.memory.clone(),
                    trace: execution.trace.clone()
                }
            );
            let mut row = visible_result(&execution);
            expected.push(row.clone());
            row.push(memory_digest(&execution.memory));
            expected_memory.push(row);
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
        let output = readable::emit_readable_c(&program).unwrap();
        let source = scratch.0.join(format!("readable{optimization}.c"));
        std::fs::write(&source, output.code.clone() + &readable_harness(&output)).unwrap();
        let compiled = source.with_extension("o");
        let binary = source.with_extension("bin");
        object(&source, &compiled, optimization, "nirvana_readable");
        link(&[&compiled], &binary);
        assert_eq!(run_fields(&binary, &text, 6), expected_memory);
    }
}

enum ExpectedReduction {
    Accepted,
    Original,
    ResourceDependent,
}

fn check_checked_c_fixture(
    name: &str,
    optimization: &str,
    solver: &nirvana::verify::Solver,
    expected: ExpectedReduction,
) {
    let scratch = Scratch::new();
    let root = fixture_root();
    let object_path = scratch.0.join("original.o");
    object(
        &root.join("cases").join(format!("{name}.c")),
        &object_path,
        optimization,
        "fixture",
    );
    let program = frontend::lift_elf(&std::fs::read(&object_path).unwrap(), "fixture")
        .unwrap()
        .program;
    let (output, validation) = readable::emit_readable_c_with_checked_reduction_and_options(
        &program,
        solver,
        readable::ReadableOptions {
            stack_register: Some(nirvana::ir::Reg(x86::RSP)),
            recover_objects: true,
        },
    )
    .unwrap();
    match expected {
        ExpectedReduction::Accepted => assert!(
            validation.accepted(),
            "{name} {optimization}: {validation:?}"
        ),
        ExpectedReduction::Original => assert!(!validation.accepted()),
        ExpectedReduction::ResourceDependent if !validation.accepted() => {
            use nirvana::block_verify::BlockVerdict;
            use nirvana::verify::UnknownReason;
            assert!(
                matches!(validation.incomplete, Some(UnknownReason::SolverTimeout))
                    || matches!(
                        validation.blocks.last().map(|block| &block.verdict),
                        Some(BlockVerdict::Unknown(
                            UnknownReason::SolverUnknown | UnknownReason::SolverTimeout
                        ))
                    ),
                "only solver resource cutoffs may retain this known candidate: {validation:?}"
            );
        }
        ExpectedReduction::ResourceDependent => {}
    }
    assert!(
        !validation.blocks.iter().any(|block| matches!(
            block.verdict,
            nirvana::block_verify::BlockVerdict::Counterexample(_)
        )),
        "unexpected local counterexample: {validation:?}"
    );
    if !validation.accepted() {
        assert_eq!(output.reduction_stats.passes, 0);
        assert_eq!(
            output.reduction_stats.reduced_assignments,
            output.reduction_stats.original_assignments
        );
        assert_eq!(
            output.parameters,
            (0..program.register_count())
                .map(nirvana::ir::Reg)
                .collect::<Vec<_>>()
        );
    }
    let inputs: Vec<[u64; 4]> = include_str!("fixtures/inputs.tsv")
        .lines()
        .filter(|line| !line.is_empty() && !line.starts_with('#'))
        .map(|line| {
            let fields: Vec<_> = line.split('\t').collect();
            std::array::from_fn(|i| fields[i + 1].parse().unwrap())
        })
        .collect();
    let mut text = String::new();
    let mut expected_memory = Vec::new();
    let mut expected_visible = Vec::new();
    for input in inputs {
        writeln!(text, "{} {} {} {}", input[0], input[1], input[2], input[3]).unwrap();
        let (registers, memory) = prepare(&input);
        let execution = program
            .execute_with_memory(&registers, BASE, &memory, 10000)
            .unwrap();
        let mut row = visible_result(&execution);
        expected_visible.push(row.clone());
        row.push(memory_digest(&execution.memory));
        expected_memory.push(row);
    }
    let harness = scratch.0.join("harness.o");
    object(&root.join("harness.c"), &harness, optimization, "fixture");
    let original_binary = scratch.0.join("original");
    link(&[&object_path, &harness], &original_binary);
    assert_eq!(run(&original_binary, &text), expected_visible);
    let source = scratch.0.join("checked.c");
    std::fs::write(&source, output.code.clone() + &readable_harness(&output)).unwrap();
    let compiled = scratch.0.join("checked.o");
    object(&source, &compiled, optimization, "nirvana_readable");
    let binary = scratch.0.join("checked");
    link(&[&compiled], &binary);
    assert_eq!(run_fields(&binary, &text, 6), expected_memory);
}

#[test]
fn unavailable_verifier_keeps_original_ir_and_emits_executable_c() {
    check_checked_c_fixture(
        "arithmetic",
        "-O0",
        &nirvana::verify::Solver::new("/nirvana-no-such-solver"),
        ExpectedReduction::Original,
    );
    let result = std::process::Command::new(env!("CARGO_BIN_EXE_nirvana"))
        .args(["unused.o", "--verify-reduction", "/nirvana-no-such-solver"])
        .output()
        .unwrap();
    assert!(!result.status.success());
    assert!(String::from_utf8_lossy(&result.stderr).contains("requires --emit readable-c"));
}

#[test]
#[ignore = "requires Z3; set NIRVANA_Z3 and run with --include-ignored"]
fn accepted_reductions_feed_native_c_and_the_cli_reports_only_the_ir_scope() {
    let path = std::env::var_os("NIRVANA_Z3").unwrap_or_else(|| "z3".into());
    let solver = nirvana::verify::Solver::new(&path);
    for (name, optimization) in [("diamond", "-O2"), ("sum", "-O2")] {
        check_checked_c_fixture(name, optimization, &solver, ExpectedReduction::Accepted);
    }
    check_checked_c_fixture(
        "nonlocal-exit",
        "-O0",
        &solver,
        ExpectedReduction::ResourceDependent,
    );
    let scratch = Scratch::new();
    let object_path = scratch.0.join("diamond.o");
    object(
        &fixture_root().join("cases/diamond.c"),
        &object_path,
        "-O2",
        "fixture",
    );
    let result = std::process::Command::new(env!("CARGO_BIN_EXE_nirvana"))
        .arg(&object_path)
        .args(["--emit", "readable-c", "--verify-reduction"])
        .arg(path)
        .output()
        .unwrap();
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
    let message = String::from_utf8(result.stderr).unwrap();
    assert!(message.contains("IR reduction accepted under checked-memory-block-v1"));
    assert!(message.contains("C emission is separately tested"));
    assert!(
        String::from_utf8(result.stdout)
            .unwrap()
            .contains("nirvana_readable(")
    );
}

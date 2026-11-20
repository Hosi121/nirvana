//! Independent bounded algorithms: source C/native, binary IR, and generated C.
//! Fixture names describe the source corpus, never recovered algorithm/type names.

#[path = "support/checked_c.rs"]
#[allow(dead_code)]
mod checked_c;
#[path = "support/loop_headers.rs"]
mod loop_headers;
#[path = "support/native.rs"]
mod native;

use nirvana::ir::Execution;
use nirvana::{emit, frontend, readable, x86};
use std::collections::VecDeque;
use std::fmt::Write as _;
use std::path::Path;
use std::process::Command;

const BASE: u64 = 4096;
const STATE: usize = 64;
const SIZE: usize = 8192;
const NAMES: [&str; 5] = ["bfs", "dfs", "ring-queue", "linked-list", "bst-lookup"];

// Ubuntu's cc enables stack canaries by default. The single-function frontend
// has no TLS/import model; the identical object used for native and IR disables
// that host instrumentation, following existing standalone fixture conventions.
// O0/O2 and all vectorization choices remain unchanged.
fn algorithm_object(source: &Path, output: &Path, optimization: &str) {
    let result = Command::new("cc")
        .args([
            "-std=c11",
            "-Wall",
            "-Wextra",
            "-Werror",
            "-pedantic",
            "-fno-lto",
            "-fno-stack-protector",
            optimization,
            "-DFIXTURE_ENTRY=fixture",
            "-c",
        ])
        .arg(source)
        .arg("-o")
        .arg(output)
        .output()
        .expect("algorithm fixture tests require a C11 compiler named cc");
    assert!(
        result.status.success(),
        "{} {optimization}: {}",
        source.display(),
        String::from_utf8_lossy(&result.stderr)
    );
}

fn inputs(name: &str) -> Vec<[u64; 4]> {
    let mut cases = vec![
        [0; 4],
        [u64::MAX; 4],
        [0, u64::MAX, 0, u64::MAX],
        [u64::MAX, 0, u64::MAX, 0],
        [1 << 63, 1 << 63, 1 << 63, 1 << 63],
        [0xaaaa_aaaa_aaaa_aaaa, 7, 0x5555_5555_5555_5555, 15],
        [0x5555_5555_5555_5555, 63, 0xaaaa_aaaa_aaaa_aaaa, 31],
        [u64::MAX - 1, u64::MAX - 1, u64::MAX - 1, u64::MAX - 1],
    ];
    // A fixed xorshift sequence, independent of host randomness and test order.
    let mut seed = 0x6e69_7276_616e_6135_u64;
    for _ in 0..48 {
        cases.push(std::array::from_fn(|_| {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        }));
    }
    match name {
        "bfs" | "dfs" => {
            // Empty, self loops, chain, cycle, disconnected, dense and branching.
            for graph in [
                0,
                0x8040_2010_0804_0201,
                0x0080_4020_1008_0402,
                0x0180_4020_1008_0402,
                0x0000_0000_0001_0200,
                u64::MAX,
                0x0000_0000_8080_0606,
            ] {
                for config in [0, 7, 15, 63] {
                    cases.push([graph, config, 0x1234_5678, 0]);
                }
            }
        }
        "ring-queue" => {
            for operations in [
                0,
                u64::MAX,
                0x5555_5555_5555_5555,
                0xaaaa_aaaa_aaaa_aaaa,
                0x5555_0000_5555_0000,
                0x5555_5555_0000_0000,
                0x4444_4444_4444_4444,
                0x9999_9999_9999_9999,
            ] {
                for limit in [0, 7, 8, 31] {
                    cases.push([operations, limit, u64::MAX, u64::MAX - 1]);
                }
            }
        }
        "linked-list" => {
            for links in [
                0xffff_ffff,
                0x7654_3210,
                0xf765_4321,
                0x0765_4321,
                0x0000_0001,
            ] {
                for config in [0, 7, 63] {
                    for limit in [0, 15] {
                        cases.push([links, config, 0x8070_6050_4030_2010, limit]);
                    }
                }
            }
        }
        "bst-lookup" => {
            for (base, gap) in [(0, 1), (19, 3), (65535, 16)] {
                for rank in 0..7 {
                    cases.push([base, gap - 1, base + rank * gap, u64::MAX]);
                }
                cases.push([base, gap - 1, base + 7 * gap, 0]);
                cases.push([base, gap - 1, base.wrapping_sub(1), 0]);
            }
        }
        _ => unreachable!(),
    }
    cases
}

fn graph_config(input: &[u64; 4]) -> (usize, usize) {
    let n = (input[1] as usize & 7) + 1;
    let start = ((input[1] >> 3) as usize & 7).min(n - 1);
    (n, start)
}

fn reference(name: &str, input: &[u64; 4]) -> Vec<u64> {
    match name {
        "bfs" => {
            let (n, start) = graph_config(input);
            let mut queue = VecDeque::from([(start, 0)]);
            let (mut seen, mut count, mut order, mut distances) = (1 << start, 0, 0, 0);
            while let Some((vertex, distance)) = queue.pop_front() {
                count += 1;
                order = (order << 4) | (vertex as u64 + 1);
                distances += distance;
                for next in 0..n {
                    if input[0] >> (vertex * 8 + next) & 1 != 0 && seen >> next & 1 == 0 {
                        seen |= 1 << next;
                        queue.push_back((next, distance + 1));
                    }
                }
            }
            vec![input[2] ^ order ^ distances, seen, count, order, distances]
        }
        "dfs" => {
            // Recursive oracle versus explicit continuation frames in C.
            fn visit(graph: u64, n: usize, vertex: usize, depth: u64, out: &mut [u64; 4]) {
                out[0] |= 1 << vertex;
                out[1] += 1;
                out[2] = (out[2] << 4) | (vertex as u64 + 1);
                out[3] = out[3].max(depth);
                for next in 0..n {
                    if graph >> (vertex * 8 + next) & 1 != 0 && out[0] >> next & 1 == 0 {
                        visit(graph, n, next, depth + 1, out);
                    }
                }
            }
            let (n, start) = graph_config(input);
            let mut out = [0; 4];
            visit(input[0], n, start, 1, &mut out);
            vec![input[2] ^ out[2] ^ out[3], out[0], out[1], out[2], out[3]]
        }
        "ring-queue" => {
            let mut queue = VecDeque::new();
            let (mut value, mut checksum) = (input[2], input[3]);
            let (mut rejected, mut popped) = (0, 0);
            for step in 0..((input[1] & 31) + 1) {
                match input[0] >> (step * 2) & 3 {
                    0 | 3 if queue.len() < 8 => {
                        queue.push_back(value);
                        value = value.wrapping_mul(17).wrapping_add(step + 1);
                    }
                    1 if !queue.is_empty() => {
                        checksum = checksum
                            .wrapping_mul(33)
                            .wrapping_add(queue.pop_front().unwrap());
                        popped += 1;
                    }
                    2 if !queue.is_empty() => checksum ^= queue[0],
                    _ => rejected += 1,
                }
            }
            vec![
                checksum ^ queue.front().copied().unwrap_or(0) ^ (popped << 32),
                queue.len() as u64,
                rejected,
                checksum,
                value,
            ]
        }
        "linked-list" => {
            let (n, start) = graph_config(input);
            let mut node = Some(start);
            let (mut sum, mut steps, mut seen, mut trace) = (0, 0, 0, 0_u64);
            while let Some(index) = node {
                if steps == (input[3] & 15) + 1 {
                    break;
                }
                sum += (input[2] >> (index * 8) & 255) + index as u64;
                steps += 1;
                seen |= 1 << index;
                trace = trace.wrapping_mul(17).wrapping_add(index as u64 + 1);
                let next = (input[0] >> (index * 4) & 15) as usize;
                node = (next < n).then_some(next);
            }
            vec![
                sum ^ trace ^ if node.is_none() { 1 << 63 } else { 0 },
                sum,
                steps,
                seen,
                trace,
            ]
        }
        "bst-lookup" => {
            // Binary search on sorted ranks gives the same balanced tree path.
            let (base, gap) = (input[0] & 65535, (input[1] & 15) + 1);
            let (mut low, mut high) = (0, 7);
            let (mut found, mut key, mut steps, mut path) = (0, 0, 0, input[3]);
            while low < high {
                let rank = (low + high) / 2;
                let candidate = base + rank * gap;
                steps += 1;
                path = path.wrapping_mul(17).wrapping_add(candidate);
                match input[2].cmp(&candidate) {
                    std::cmp::Ordering::Equal => {
                        found = 1;
                        key = candidate;
                        break;
                    }
                    std::cmp::Ordering::Less => high = rank,
                    std::cmp::Ordering::Greater => low = rank + 1,
                }
            }
            vec![
                if found != 0 { key + 1 } else { 0 },
                found,
                key,
                steps,
                path,
            ]
        }
        _ => unreachable!(),
    }
}

fn prepare(input: &[u64; 4]) -> (Vec<u64>, Vec<u8>) {
    let mut registers = vec![0; x86::REGISTER_COUNT];
    registers[x86::RDI] = BASE + STATE as u64;
    registers[x86::RSP] = BASE + SIZE as u64;
    let mut memory: Vec<_> = (0..SIZE).map(|i| (i * 29 + 7) as u8).collect();
    for (i, word) in input.iter().enumerate() {
        memory[STATE + i * 8..STATE + i * 8 + 8].copy_from_slice(&word.to_le_bytes());
    }
    (registers, memory)
}

fn visible(execution: &Execution) -> Vec<u64> {
    let mut row = vec![execution.value];
    row.extend((0..4).map(|i| {
        u64::from_le_bytes(
            execution.memory[STATE + i * 8..STATE + i * 8 + 8]
                .try_into()
                .unwrap(),
        )
    }));
    row
}

fn digest(memory: &[u8]) -> u64 {
    memory.iter().fold(0xcbf29ce484222325, |hash, byte| {
        (hash ^ u64::from(*byte)).wrapping_mul(0x100000001b3)
    })
}

fn harness(call: &str, register_count: usize) -> String {
    format!(
        r#"
#undef abort
#include <inttypes.h>
#include <stdio.h>
_Noreturn void nirvana_test_abort(void) {{
    fprintf(stderr, "unexpected guest fault: address=%" PRIu64 " access=%u width=%" PRIu64 "\n",
            nirvana_test_address, nirvana_test_access, nirvana_test_width);
    exit(1);
}}
int main(void) {{
    uint64_t input[4];
    while (scanf("%" SCNu64 " %" SCNu64 " %" SCNu64 " %" SCNu64,
                 &input[0], &input[1], &input[2], &input[3]) == 4) {{
        uint64_t r[{register_count}] = {{0}};
        uint8_t memory[{SIZE}];
        for (unsigned i = 0; i < sizeof(memory); ++i) memory[i] = (uint8_t)(i * 29 + 7);
        r[{rdi}] = UINT64_C({state}); r[{rsp}] = UINT64_C({stack});
        for (unsigned i = 0; i < 4; ++i)
            for (unsigned j = 0; j < 8; ++j) memory[{STATE} + i * 8 + j] = (uint8_t)(input[i] >> (j * 8));
        uint64_t value = {call};
        uint64_t hash = UINT64_C(14695981039346656037);
        for (unsigned i = 0; i < sizeof(memory); ++i) hash = (hash ^ memory[i]) * UINT64_C(1099511628211);
        for (unsigned i = 0; i < 4; ++i) {{
            input[i] = 0;
            for (unsigned j = 0; j < 8; ++j) input[i] |= (uint64_t)memory[{STATE} + i * 8 + j] << (j * 8);
        }}
        printf("%" PRIu64 " %" PRIu64 " %" PRIu64 " %" PRIu64 " %" PRIu64 " %" PRIu64 "\n",
               value, input[0], input[1], input[2], input[3], hash);
    }}
    return 0;
}}
"#,
        rdi = x86::RDI,
        rsp = x86::RSP,
        state = BASE + STATE as u64,
        stack = BASE + SIZE as u64
    )
}

#[test]
fn bounded_algorithms_match_native_binary_ir_and_checked_generated_c() {
    let scratch = native::Scratch::new();
    let mut failures = Vec::new();
    let (mut native_cases, mut ir_cases, mut generated_cases) = (0, 0, 0);
    let (mut supported, mut unsupported, mut unsupported_cases) = (0, 0, 0);
    for name in NAMES {
        let inputs = inputs(name);
        let expected: Vec<_> = inputs.iter().map(|input| reference(name, input)).collect();
        let mut text = String::new();
        for input in &inputs {
            writeln!(text, "{} {} {} {}", input[0], input[1], input[2], input[3]).unwrap();
        }
        for optimization in ["-O0", "-O2"] {
            let directory = scratch.0.join(format!("{name}{optimization}"));
            std::fs::create_dir(&directory).unwrap();
            let original = directory.join("original.o");
            let native_harness = directory.join("native-harness.o");
            algorithm_object(
                &native::fixture_root().join(format!("algorithms/{name}.c")),
                &original,
                optimization,
            );
            native::object(
                &native::fixture_root().join("harness.c"),
                &native_harness,
                optimization,
                "fixture",
            );
            let binary = directory.join("native");
            native::link(&[&original, &native_harness], &binary);
            assert_eq!(
                native::run(&binary, &text),
                expected,
                "{name} {optimization}: native/oracle"
            );
            native_cases += inputs.len();
            // Only object bytes and the entry symbol enter the frontend.
            let lifted = match frontend::lift_elf(&std::fs::read(&original).unwrap(), "fixture") {
                Ok(lifted) => lifted,
                Err(error) => {
                    // The ordinary frontend has no opt-in vector runner. GCC
                    // currently emits GPR->XMM MOVQ in this one source profile.
                    // Keep its native/oracle checks and exact negative evidence;
                    // if lifting starts succeeding, run every positive check.
                    let known_vector_limit = name == "bst-lookup"
                        && optimization == "-O2"
                        && matches!(&error, frontend::FrontendError::Lift(x86::LiftError::Decode(error))
                            if error.reason == "unsupported opcode 0f 6e");
                    if known_vector_limit {
                        println!(
                            "known unsupported {name} {optimization}: {error}; all {} native/oracle cases pass",
                            inputs.len()
                        );
                        unsupported += 1;
                        unsupported_cases += inputs.len();
                        continue;
                    }
                    failures.push(format!("{name} {optimization}: frontend: {error}"));
                    continue;
                }
            };
            supported += 1;
            let program = &lifted.program;
            let mut with_memory = Vec::new();
            for (input, expected) in inputs.iter().zip(&expected) {
                let (registers, memory) = prepare(input);
                let execution = program
                    .execute_with_memory(&registers, BASE, &memory, 100_000)
                    .unwrap_or_else(|error| {
                        panic!("{name} {optimization} input={input:?}: {error}")
                    });
                let mut row = visible(&execution);
                assert_eq!(
                    &row, expected,
                    "{name} {optimization} input={input:?}: IR/oracle"
                );
                row.push(digest(&execution.memory));
                with_memory.push(row);
            }
            ir_cases += inputs.len();
            let core = emit::emit_c(program).unwrap();
            let mut modes = vec![(
                "core",
                checked_c::instrument(&core.code)
                    + &harness(
                        "nirvana_fn(r, memory, UINT64_C(4096), sizeof(memory))",
                        program.register_count(),
                    ),
            )];
            match readable::emit_readable_c(program) {
                Ok(output) => {
                    loop_headers::assert_pure_conditions(&output.code);
                    let mut arguments: Vec<_> = output
                        .parameters
                        .iter()
                        .map(|reg| format!("r[{}]", reg.0))
                        .collect();
                    arguments
                        .extend(["memory", "UINT64_C(4096)", "sizeof(memory)"].map(String::from));
                    modes.push((
                        "readable",
                        checked_c::instrument(&output.code)
                            + &harness(
                                &format!("nirvana_readable({})", arguments.join(", ")),
                                program.register_count(),
                            ),
                    ));
                }
                Err(error) => failures.push(format!("{name} {optimization}: readable: {error}")),
            }
            for (mode, source) in modes {
                let path = directory.join(format!("{mode}.c"));
                std::fs::write(&path, &source).unwrap();
                for copt in ["-O0", "-O2"] {
                    let object = directory.join(format!("{mode}{copt}.o"));
                    let binary = directory.join(format!("{mode}{copt}"));
                    native::object(&path, &object, copt, "fixture");
                    native::link(&[&object], &binary);
                    assert_eq!(
                        native::run_fields(&binary, &text, 6),
                        with_memory,
                        "{name} source={optimization} {mode} C={copt}: return/state/full-RAM digest"
                    );
                    generated_cases += inputs.len();
                }
            }
            println!(
                "{name} {optimization}: {} inputs, {} machine instructions; native/oracle/IR agree",
                inputs.len(),
                program.instructions().len()
            );
        }
    }
    println!(
        "algorithm corpus: supported={supported}/10, explicit limitations={unsupported}; native={native_cases}, IR={ir_cases}, generated-C/full-RAM={generated_cases}"
    );
    assert!(
        failures.is_empty(),
        "algorithm support failures:\n{}",
        failures.join("\n")
    );
    assert!(supported >= 9, "at least nine binary profiles must pass");
    assert_eq!(supported + unsupported, 10);
    assert!(unsupported <= 1);
    assert_eq!(ir_cases + unsupported_cases, native_cases);
    assert_eq!(generated_cases, 4 * ir_cases);
}

#[test]
fn optimized_bst_vectors_match_native_and_full_module_state() {
    use nirvana::linked_elf::LinkedOptions;
    use nirvana::module_ir::{self, Limits, Status};

    let scratch = native::Scratch::new();
    let original = scratch.0.join("bst.o");
    let driver = scratch.0.join("driver.o");
    algorithm_object(
        &native::fixture_root().join("algorithms/bst-lookup.c"),
        &original,
        "-O2",
    );
    native::object(
        &native::fixture_root().join("harness.c"),
        &driver,
        "-O2",
        "fixture",
    );
    let binary = scratch.0.join("original");
    native::link(&[&original, &driver], &binary);
    let input = inputs("bst-lookup");
    let text = input
        .iter()
        .map(|x| format!("{} {} {} {}\n", x[0], x[1], x[2], x[3]))
        .collect::<String>();
    let oracle = input
        .iter()
        .map(|x| reference("bst-lookup", x))
        .collect::<Vec<_>>();
    assert_eq!(native::run(&binary, &text), oracle);
    let module = module_ir::lift_elf(
        &std::fs::read(&binary).unwrap(),
        "fixture",
        LinkedOptions {
            stack_size: SIZE,
            ..Default::default()
        },
    )
    .unwrap();
    let state = module.image.memory_base + STATE as u64;
    let mut expected = Vec::new();
    for (words, reference) in input.iter().zip(&oracle) {
        let mut registers = module.initial_registers();
        registers[x86::RDI] = state;
        let mut memory = module.image.memory.clone();
        for (i, word) in words.iter().enumerate() {
            memory[STATE + i * 8..STATE + i * 8 + 8].copy_from_slice(&word.to_le_bytes());
        }
        let report = module
            .program
            .run(
                &registers,
                module.image.memory_base,
                &memory,
                Limits {
                    instructions: 100_000,
                    imports: 0,
                },
                &mut module_ir::RejectImports,
            )
            .unwrap();
        assert_eq!(report.status, Status::Returned(reference[0]));
        let mut row = vec![report.state.registers[x86::RAX]];
        for i in 0..4 {
            row.push(u64::from_le_bytes(
                report.state.memory[STATE + i * 8..STATE + i * 8 + 8]
                    .try_into()
                    .unwrap(),
            ));
        }
        assert_eq!(&row, reference);
        row.extend([
            report.pc,
            report.state.trace.len() as u64,
            100_000 - report.state.trace.len() as u64,
            0,
            digest(&report.state.memory),
        ]);
        row.extend_from_slice(&report.state.registers);
        expected.push(row);
    }
    let output = nirvana::module_readable::emit_c_with_locals(&module).unwrap();
    assert!(output.report.local_functions > 0);
    let harness = format!(
        r#"
#undef main
#include <inttypes.h>
int main(void) {{
    uint64_t input[4];
    while(scanf("%" SCNu64 " %" SCNu64 " %" SCNu64 " %" SCNu64, &input[0], &input[1], &input[2], &input[3])==4) {{
        struct nv_module *s=nv_create(); if(!s) return 1;
        s->r[7]=UINT64_C({state}); s->instructions_left=100000; s->imports_left=0;
        for(unsigned i=0;i<4;++i) for(unsigned j=0;j<8;++j) s->memory[{STATE}+i*8+j]=(uint8_t)(input[i]>>(j*8));
        if(nv_run(s)!=0) return 2;
        for(unsigned i=0;i<4;++i) {{ input[i]=0; for(unsigned j=0;j<8;++j) input[i]|=(uint64_t)s->memory[{STATE}+i*8+j]<<(j*8); }}
        uint64_t hash=UINT64_C(14695981039346656037);
        for(uint64_t i=0;i<s->size;++i) hash=(hash^s->memory[i])*UINT64_C(1099511628211);
        printf("%" PRIu64 " %" PRIu64 " %" PRIu64 " %" PRIu64 " %" PRIu64 " %" PRIu64 " %" PRIu64 " %" PRIu64 " %" PRIu64 " %" PRIu64,
               s->r[0],input[0],input[1],input[2],input[3],s->pc,s->started,s->instructions_left,s->imports_left,hash);
        for(unsigned i=0;i<80;++i) printf(" %" PRIu64,s->r[i]);
        putchar('\n'); free(s->memory); free(s);
    }}
    return 0;
}}
"#
    );
    let source = scratch.0.join("bst-module.c");
    std::fs::write(
        &source,
        format!(
            "#define main nv_standalone_main\n{}\n{harness}",
            output.code
        ),
    )
    .unwrap();
    for optimization in ["-O0", "-O2"] {
        let object = scratch.0.join(format!("module{optimization}.o"));
        let binary = scratch.0.join(format!("module{optimization}"));
        native::object(&source, &object, optimization, "fixture");
        native::link(&[&object], &binary);
        assert_eq!(
            native::run_fields(&binary, &text, 90),
            expected,
            "BST vector module {optimization}"
        );
    }
    println!(
        "BST O2 module: {} native/model and {} generated-C comparisons, all80 registers/PC/budgets/full-RAM digest",
        input.len(),
        input.len() * 2
    );
}

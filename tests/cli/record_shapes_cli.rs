//! The named existing corpus identifies evaluation cases, never inferred types.

use crate::support::native;

use nirvana::{frontend, reduce, type_infer::TypeAnalysis};
use std::path::Path;
use std::process::Command;

fn validate_shapes(legacy: &str, types: &[u8], script: &str, label: &str) {
    let input = [b"[", legacy.as_bytes(), b",", types, b"]"].concat();
    let result = native::command_output(
        Command::new("python3").args(["-c", script, label]),
        Some(&input),
        std::time::Duration::from_secs(10),
    );
    assert!(
        result.status.success(),
        "{label}: {}",
        String::from_utf8_lossy(&result.stderr)
    );
}

fn object(source: &Path, output: &Path, optimization: &str) {
    // This is the documented standalone ABI setting used by algorithm_fixtures;
    // ordinary O0/O2 and the compiler's vectorization choices are preserved.
    let result = native::compile_output(
        Command::new("cc")
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
            .arg(output),
    );
    assert!(
        result.status.success(),
        "{} {optimization}: {}",
        source.display(),
        String::from_utf8_lossy(&result.stderr)
    );
}

#[test]
fn original_list_and_bst_objects_expose_recursive_candidates_and_compilable_headers() {
    let scratch = native::Scratch::new();
    for (index, (name, optimization)) in [
        ("linked-list", "-O0"),
        ("linked-list", "-O2"),
        ("bst-lookup", "-O0"),
    ]
    .into_iter()
    .enumerate()
    {
        let directory = scratch.0.join(index.to_string());
        std::fs::create_dir(&directory).unwrap();
        let input = directory.join("input.o");
        object(
            &native::fixture_root().join(format!("algorithms/{name}.c")),
            &input,
            optimization,
        );
        // Only the same object bytes and function entry reach these APIs. No
        // source, debug information, algorithm label or expected layout does.
        let bytes = std::fs::read(&input).unwrap();
        let lifted = frontend::lift_elf_auto(&bytes, "fixture").unwrap();
        let reduced = reduce::reduce(&lifted.program).unwrap();
        let legacy = TypeAnalysis::analyze(reduced.program())
            .unwrap()
            .to_json()
            .unwrap();
        let types = Command::new(env!("CARGO_BIN_EXE_nirvana"))
            .arg(&input)
            .args(["--emit", "types"])
            .output()
            .unwrap();
        assert!(
            types.status.success(),
            "{name} {optimization}: {}",
            String::from_utf8_lossy(&types.stderr)
        );
        let script = r#"
import json,sys
old,new=json.load(sys.stdin)
shapes=new.pop('record_shapes')
assert new==old, 'legacy type/value/alias/access/layout report changed'
assert shapes['schema']=='nirvana-record-shapes-v1', shapes
assert shapes['identity']=='ssa', shapes
assert shapes['interpretations']=='tentative', shapes
assert isinstance(shapes['constraints'],list), shapes
records=shapes['records']
assert records, shapes
kind=sys.argv[1]
def field(record,offset,width):
    return [f for f in record['fields'] if f['offset']==offset and f['width']==width and f['reads']]
def self_pointer(record,offset):
    return any(record['id'] in f['pointer_targets'] and f['loaded_values'] for f in field(record,offset,8))
if kind=='linked-list':
    nodes=[r for r in records if field(r,0,8) and field(r,16,4) and self_pointer(r,8)]
else:
    nodes=[r for r in records if field(r,0,8) and self_pointer(r,8) and self_pointer(r,16)]
assert nodes, (kind,shapes)
assert all(r['bases'] and r['values'] for r in nodes), nodes
assert any(c['kind'] in ('phi','select','stack') for c in shapes['constraints']), shapes
"#;
        validate_shapes(&legacy, &types.stdout, script, name);

        let declarations = Command::new(env!("CARGO_BIN_EXE_nirvana"))
            .arg(&input)
            .args(["--emit", "record-types"])
            .output()
            .unwrap();
        assert!(
            declarations.status.success(),
            "{name} {optimization}: {}",
            String::from_utf8_lossy(&declarations.stderr)
        );
        assert!(String::from_utf8_lossy(&declarations.stdout).contains("struct record_"));
        let header = directory.join("candidate.h");
        std::fs::write(&header, &declarations.stdout).unwrap();
        let check = directory.join("check.c");
        std::fs::write(
            &check,
            "#include \"candidate.h\"\nint main(void) { return 0; }\n",
        )
        .unwrap();
        let compilation = native::compile_output(
            Command::new("cc")
                .args([
                    "-std=c11",
                    "-Wall",
                    "-Wextra",
                    "-Werror",
                    "-pedantic",
                    "-fsyntax-only",
                ])
                .arg(&check),
        );
        assert!(
            compilation.status.success(),
            "{name} {optimization}: candidate header: {}",
            String::from_utf8_lossy(&compilation.stderr)
        );
    }
}

#[test]
fn memory_round_trip_merges_record_candidates_and_preserves_native_execution() {
    use nirvana::ir::RunStatus;
    use nirvana::x86::{RDI, RDX, RSI, RSP};
    let scratch = native::Scratch::new();
    let fixture = native::fixture_root().join("types/record-memory.c");
    let input = scratch.0.join("input.o");
    object(&fixture, &input, "-O2");
    let lifted = frontend::lift_elf_auto(&std::fs::read(&input).unwrap(), "fixture").unwrap();
    let reduced = reduce::reduce(&lifted.program).unwrap();
    let legacy = TypeAnalysis::analyze(reduced.program())
        .unwrap()
        .to_json()
        .unwrap();
    let output = native::command_output(
        Command::new(env!("CARGO_BIN_EXE_nirvana"))
            .arg(&input)
            .args(["--emit", "types"]),
        Some(&[]),
        std::time::Duration::from_secs(10),
    );
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    validate_shapes(
        &legacy,
        &output.stdout,
        r#"
import json,sys
old,new=json.load(sys.stdin)
shapes=new.pop('record_shapes')
assert new==old
assert shapes['status']=='available'
assert len(shapes['records'])==2, shapes
assert shapes['memory_flow']=={'status':'available','considered_loads':1,'complete_loads':1}
def field(r,offset,width):
    return [f for f in r['fields'] if f['offset']==offset and f['width']==width]
nodes=[r for r in shapes['records'] if field(r,0,8) and field(r,16,4)]
assert len(nodes)==1, shapes
node=nodes[0]
assert len(node['bases'])==2, node
assert any(node['id'] in f['pointer_targets'] for r in shapes['records'] if r['id']!=node['id'] for f in field(r,0,8)), shapes
assert any(c['kind']=='memory' for c in shapes['constraints']), shapes
"#,
        "memory round trip",
    );

    let rows = [
        (0, 0),
        (42, 7),
        (u64::MAX, u32::MAX as u64),
        (1 << 63, 0x8000_0000),
    ];
    let text: String = rows
        .iter()
        .map(|(value, count)| format!("{value} {count}\n"))
        .collect();
    let mut expected = Vec::new();
    for (value, count) in rows {
        let mut registers = vec![0; lifted.program.register_count()];
        registers[RDI] = 0x2000;
        registers[RSI] = 0x2040;
        registers[RDX] = value;
        registers[RSP] = 0x2300;
        let mut memory = [0u8; 1024];
        memory[80..84].copy_from_slice(&(count as u32).to_le_bytes());
        let report = lifted
            .program
            .run_with_memory(&registers, 0x2000, &memory, 100)
            .unwrap();
        let RunStatus::Returned(result) = report.status else {
            panic!("{:?}", report.status)
        };
        let memory = report.state.memory;
        expected.push(vec![
            result,
            u64::from_le_bytes(memory[64..72].try_into().unwrap()),
            u32::from_le_bytes(memory[80..84].try_into().unwrap()) as u64,
            u64::from(u64::from_le_bytes(memory[..8].try_into().unwrap()) == 0x2040),
        ]);
    }
    let oracle_source = scratch.0.join("oracle.c");
    std::fs::write(&oracle_source, r#"
#include <inttypes.h>
#include <stdio.h>
#include "record-memory.c"
int main(void) {
    uint64_t value, count;
    while(scanf("%" SCNu64 " %" SCNu64, &value, &count)==2) {
        struct holder holder={0}; struct node node={0}; node.count=(uint32_t)count;
        uint64_t result=fixture(&holder,&node,value);
        printf("%" PRIu64 " %" PRIu64 " %" PRIu32 " %u\n",result,node.value,node.count,(unsigned)(holder.current==&node));
    }
    return 0;
}
"#).unwrap();
    let oracle = scratch.0.join("oracle");
    native::compile(
        Command::new("cc")
            .args([
                "-std=c11",
                "-Wall",
                "-Wextra",
                "-Werror",
                "-pedantic",
                "-O2",
            ])
            .arg("-I")
            .arg(fixture.parent().unwrap())
            .arg(&oracle_source)
            .arg("-o")
            .arg(&oracle),
    );
    assert_eq!(native::run_fields(&oracle, &text, 4), expected);

    let declarations = native::command_output(
        Command::new(env!("CARGO_BIN_EXE_nirvana"))
            .arg(&input)
            .args(["--emit", "record-types"]),
        Some(&[]),
        std::time::Duration::from_secs(10),
    );
    assert!(declarations.status.success());
    let mut code = nirvana::emit::emit_c(&lifted.program).unwrap().code;
    code.push_str(std::str::from_utf8(&declarations.stdout).unwrap());
    code.push_str(&format!(r#"
#include <inttypes.h>
#include <stdio.h>
#include <string.h>
int main(void) {{
    uint64_t value, count;
    while(scanf("%" SCNu64 " %" SCNu64, &value, &count)==2) {{
        uint8_t memory[1024]={{0}}; uint64_t r[{registers}]={{0}};
        uint32_t start=(uint32_t)count; memcpy(memory+80,&start,4);
        r[{rdi}]=0x2000; r[{rsi}]=0x2040; r[{rdx}]=value; r[{rsp}]=0x2300;
        uint64_t result=nirvana_fn(r,memory,0x2000,sizeof(memory));
        uint64_t stored, pointer; uint32_t updated;
        memcpy(&stored,memory+64,8); memcpy(&updated,memory+80,4); memcpy(&pointer,memory,8);
        printf("%" PRIu64 " %" PRIu64 " %" PRIu32 " %u\n",result,stored,updated,(unsigned)(pointer==0x2040));
    }}
    return 0;
}}
"#, registers=lifted.program.register_count(), rdi=RDI,rsi=RSI,rdx=RDX,rsp=RSP));
    let generated_source = scratch.0.join("generated.c");
    std::fs::write(&generated_source, code).unwrap();
    let generated = scratch.0.join("generated");
    native::compile_c(
        &generated_source,
        &generated,
        &[
            "-O2",
            "-fsanitize=undefined",
            "-fno-sanitize-recover=undefined",
        ],
    );
    assert_eq!(native::run_fields(&generated, &text, 4), expected);
}

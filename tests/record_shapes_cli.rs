//! The named existing corpus identifies evaluation cases, never inferred types.

#[path = "support/native.rs"]
#[allow(dead_code)]
mod native;

use nirvana::{frontend, reduce, type_infer::TypeAnalysis};
use std::io::Write as _;
use std::path::Path;
use std::process::{Command, Stdio};

fn object(source: &Path, output: &Path, optimization: &str) {
    // This is the documented standalone ABI setting used by algorithm_fixtures;
    // ordinary O0/O2 and the compiler's vectorization choices are preserved.
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
        .expect("record shape corpus tests require the C11 compiler cc");
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
        let mut validator = Command::new("python3")
            .args(["-c", script, name])
            .stdin(Stdio::piped())
            .spawn()
            .unwrap();
        let mut stdin = validator.stdin.take().unwrap();
        stdin.write_all(b"[").unwrap();
        stdin.write_all(legacy.as_bytes()).unwrap();
        stdin.write_all(b",").unwrap();
        stdin.write_all(&types.stdout).unwrap();
        stdin.write_all(b"]").unwrap();
        drop(stdin);
        assert!(
            validator.wait().unwrap().success(),
            "{name} {optimization}: JSON shape assertions"
        );

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
        let compilation = Command::new("cc")
            .args([
                "-std=c11",
                "-Wall",
                "-Wextra",
                "-Werror",
                "-pedantic",
                "-fsyntax-only",
            ])
            .arg(&check)
            .output()
            .unwrap();
        assert!(
            compilation.status.success(),
            "{name} {optimization}: candidate header: {}",
            String::from_utf8_lossy(&compilation.stderr)
        );
    }
}

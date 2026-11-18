#[path = "support/native.rs"]
#[allow(dead_code)]
mod native;
use std::io::Write as _;
use std::process::{Command, Stdio};

#[test]
fn cli_exposes_file_literals_and_opaque_calls_without_changing_executable_modes() {
    let scratch = native::Scratch::new();
    let object = scratch.0.join("hello.o");
    native::object(
        &native::fixture_root().join("references/hello.c"),
        &object,
        "-O2",
        "fixture",
    );
    let output = Command::new(env!("CARGO_BIN_EXE_nirvana"))
        .arg(&object)
        .args(["--emit", "references"])
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let mut python = Command::new("python3")
        .args([
            "-c",
            r#"import json,sys
r=json.load(sys.stdin)
assert r['schema']=='nirvana-object-references-v1'
assert r['call_effects']=='opaque'
assert len(r['calls'])==1
c=r['calls'][0]
assert c['source_hint']=='puts("Hello, world!")'
assert c['target']=={'kind':'external','name':'puts','addend':0}
assert c['integer_argument_registers'][0]['register']==7
l=r['literals'][c['integer_argument_registers'][0]['literal']]
assert bytes(l['bytes'])==b'Hello, world!'
assert l['c_literal']=='"Hello, world!"'
assert all(ref['instruction'] is not None for ref in r['references'])
"#,
        ])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    python
        .stdin
        .take()
        .unwrap()
        .write_all(&output.stdout)
        .unwrap();
    let result = python.wait_with_output().unwrap();
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
    for flags in [
        vec!["--emit", "readable-c"],
        vec!["--emit", "references", "--raw"],
        vec!["--emit", "references", "--run", "0,0,0,0"],
        vec!["--emit", "references", "--base", "0x1000"],
    ] {
        let result = Command::new(env!("CARGO_BIN_EXE_nirvana"))
            .arg(&object)
            .args(flags)
            .output()
            .unwrap();
        assert!(!result.status.success());
        assert!(result.stdout.is_empty());
        assert!(!result.stderr.is_empty());
    }
}

#[test]
fn json_preserves_escaped_names_and_byte_literal_spelling() {
    use nirvana::object_refs::{Literal, ObjectReferences};
    let report = ObjectReferences {
        function: "quoted\"\\\n関数".into(),
        section: 1,
        section_offset: u64::MAX,
        function_size: 1,
        references: vec![],
        calls: vec![],
        literals: vec![Literal {
            section: 2,
            section_name: Some(".rodata\n\"".into()),
            offset: 0,
            bytes: b"??/\"\\\xff9".to_vec(),
        }],
    };
    let text = report.to_json().unwrap();
    let mut python = Command::new("python3")
        .args([
            "-c",
            r#"import json,sys
r=json.load(sys.stdin)
assert r['function']['name']=='quoted"\\\n関数'
assert r['function']['section_offset']==2**64-1
assert bytes(r['literals'][0]['bytes'])==b'??/"\\\xff9'
assert '\\?\\?/' in r['literals'][0]['c_literal']
"#,
        ])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    python
        .stdin
        .take()
        .unwrap()
        .write_all(text.as_bytes())
        .unwrap();
    let result = python.wait_with_output().unwrap();
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
}

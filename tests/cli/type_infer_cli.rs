use crate::support::native;
use std::io::Write as _;
use std::process::{Command, Stdio};
#[test]
fn machine_code_report_exposes_record_pointer_and_element_constraints_as_json() {
    let scratch = native::Scratch::new();
    let object = scratch.0.join("record.o");
    native::object(
        &native::fixture_root().join("types/record-index.c"),
        &object,
        "-O2",
        "fixture",
    );
    let output = Command::new(env!("CARGO_BIN_EXE_nirvana"))
        .arg(&object)
        .args(["--emit", "types"])
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let script = r#"
import json,sys
r=json.load(sys.stdin)
assert r['schema']=='nirvana-type-constraints-v1'
v={x['id']:x for x in r['values']}
records=[x for x in r['layout_candidates'] if any(f['offset']==0 and f['width']==4 for f in x['fields']) and any(f['offset']==8 and f['width']==8 for f in x['fields'])]
assert records,r
record=records[0]
pointers=[i for f in record['fields'] if f['offset']==8 for i in f['loaded_values']]
assert pointers
assert any('address_base' in v[i]['flow_uses'] for i in pointers)
roots={v[i]['alias'] for i in pointers}
arrays=[a for l in r['layout_candidates'] if l['base'] in roots for a in l['arrays'] if a['stride']==4 and a['width']==4]
assert arrays,r
assert any(v[i]['maximum_bits']<=32 for a in arrays for i in a['indices'])
assert r['access_model']=='syntactic-possible'
"#;
    let mut process = Command::new("python3")
        .args(["-c", script])
        .stdin(Stdio::piped())
        .spawn()
        .unwrap();
    process
        .stdin
        .take()
        .unwrap()
        .write_all(&output.stdout)
        .unwrap();
    assert!(process.wait().unwrap().success());
    let readable = Command::new(env!("CARGO_BIN_EXE_nirvana"))
        .arg(&object)
        .args(["--emit", "readable-c"])
        .output()
        .unwrap();
    assert!(readable.status.success());
}

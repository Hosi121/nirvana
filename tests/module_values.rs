#[path = "support/native.rs"]
#[allow(dead_code)]
mod native;

use nirvana::ir::Reg;
use nirvana::linked_elf::LinkedOptions;
use nirvana::module_ir::{self, Module};
use nirvana::module_values::{self, BoundaryKind, FunctionValues, PointRole};
use nirvana::ssa::{Definition, ValueId};
use nirvana::value_liveness::Use;
use std::collections::BTreeSet;
use std::io::Write as _;
use std::path::Path;
use std::process::{Command, Stdio};

fn compile(command: &mut Command) {
    let output = command.output().unwrap();
    assert!(
        output.status.success(),
        "{command:?}: {}",
        String::from_utf8_lossy(&output.stderr)
    );
}
fn lift(binary: &Path, pie: bool) -> Module {
    module_ir::lift_elf(
        &std::fs::read(binary).unwrap(),
        "main",
        LinkedOptions {
            load_bias: if pie { 0x10000 } else { 0 },
            ..Default::default()
        },
    )
    .unwrap()
}
fn points(values: &FunctionValues) -> impl Iterator<Item = &nirvana::ssa::PointValues> {
    values.graph().blocks.iter().flat_map(|b| &b.points)
}
fn roots(values: &FunctionValues, id: ValueId) -> BTreeSet<ValueId> {
    let mut roots = BTreeSet::new();
    let mut visited = BTreeSet::new();
    let mut pending = vec![id];
    while let Some(id) = pending.pop() {
        if !visited.insert(id) {
            continue;
        }
        match &values.graph().values[id.0] {
            Definition::Phi { inputs, .. } => pending.extend(inputs.iter().map(|i| i.value)),
            _ => {
                roots.insert(id);
            }
        }
    }
    roots
}

#[test]
fn overwritten_registers_have_separate_lifetimes_and_calls_produce_unknown_values() {
    let scratch = native::Scratch::new();
    let source = scratch.0.join("values.S");
    let binary = scratch.0.join("values");
    std::fs::write(
        &source,
        r#"
.text
.globl main
.type main,@function
main:
    mov $11,%rax
    mov %rax,%rbx
    mov $22,%rax
    call callee
    add %rbx,%rax
    ret
.size main,.-main
.type callee,@function
callee:
    mov $99,%rbx
    mov $3,%rax
    ret
.size callee,.-callee
.type tail,@function
tail:
    jmp callee
.size tail,.-tail
.type indirect,@function
indirect:
    call *%rdi
    ret
.size indirect,.-indirect
.section .note.GNU-stack,"",@progbits
"#,
    )
    .unwrap();
    compile(
        Command::new("cc")
            .arg("-no-pie")
            .arg(&source)
            .arg("-o")
            .arg(&binary),
    );
    let module = lift(&binary, false);
    let before = module.program.instructions().to_vec();
    let emitted = nirvana::module_readable::emit_c(&module).unwrap().code;
    let analysis = module_values::analyze(&module.program).unwrap();
    let values = analysis
        .functions
        .iter()
        .find(|f| f.function.name == "main")
        .unwrap()
        .result
        .as_ref()
        .unwrap();
    let originals: Vec<_> = points(values)
        .filter(|p| {
            matches!(
                values.roles().get(&p.site),
                Some(PointRole::Assignment { .. })
            )
        })
        .collect();
    let definitions = |register| {
        originals.iter().filter_map(move |p| {
            let value = p.definition?;
            matches!(values.graph().values[value.0], Definition::Assignment { register: r, .. } if r == Reg(register)).then_some(value)
        }).collect::<Vec<_>>()
    };
    // The x86 lifter also writes instruction scratch registers. Select the
    // architectural definitions, and retain every intervening scratch read.
    let rax = definitions(0);
    let first = rax[0];
    let copy = definitions(3)[0];
    let overwrite = rax[1];
    let copy_read = originals
        .iter()
        .find(|p| {
            p.reads
                .iter()
                .any(|r| r.register == Reg(0) && r.value == first)
        })
        .unwrap();
    assert_ne!(first, overwrite);
    assert_eq!(copy_read.reads[0].value, first);
    assert!(
        values.lifetimes().values[first.0]
            .uses
            .contains(&Use::Point {
                site: copy_read.site,
                read: 0
            })
    );
    let copy_life = values
        .lifetimes()
        .blocks
        .iter()
        .flat_map(|b| &b.points)
        .find(|p| p.site == copy_read.site)
        .unwrap();
    assert!(copy_life.before.contains(&first));
    assert!(!copy_life.after.contains(&first));
    assert!(copy_life.after.contains(&copy_read.definition.unwrap()));
    let call = values
        .boundaries()
        .iter()
        .find(|b| matches!(b.kind, BoundaryKind::Call { .. }))
        .unwrap();
    assert_eq!(call.inputs.len(), 80);
    assert_eq!(call.outputs.len(), 80);
    assert_eq!(
        call.inputs
            .iter()
            .find(|v| v.register == Reg(0))
            .unwrap()
            .value,
        overwrite
    );
    assert_eq!(
        call.inputs
            .iter()
            .find(|v| v.register == Reg(3))
            .unwrap()
            .value,
        copy
    );
    let output_rbx = call
        .outputs
        .iter()
        .find(|v| v.register == Reg(3))
        .unwrap()
        .value;
    let add = originals
        .iter()
        .find(|p| p.site.instruction > call.address && p.reads.iter().any(|r| r.register == Reg(3)))
        .unwrap();
    let rbx = add
        .reads
        .iter()
        .find(|r| r.register == Reg(3))
        .unwrap()
        .value;
    assert_eq!(roots(values, rbx), BTreeSet::from([output_rbx]));
    assert!(!roots(values, rbx).contains(&copy));
    for boundary in values.boundaries() {
        assert_eq!(boundary.inputs.len(), module.program.register_count());
        for output in &boundary.outputs {
            let Definition::Assignment { site, register } = values.graph().values[output.value.0]
            else {
                panic!()
            };
            assert_eq!(values.roles()[&site], PointRole::OpaqueOutput { register });
        }
    }
    let tail = analysis
        .functions
        .iter()
        .find(|f| f.function.name == "tail")
        .unwrap()
        .result
        .as_ref()
        .unwrap();
    assert_eq!(tail.boundaries()[0].kind, BoundaryKind::Tail);
    assert!(tail.boundaries()[0].outputs.is_empty());
    let indirect = analysis
        .functions
        .iter()
        .find(|f| f.function.name == "indirect")
        .unwrap()
        .result
        .as_ref()
        .unwrap();
    assert_eq!(indirect.boundaries()[0].target_reads[0].register, Reg(7));
    assert_eq!(module.program.instructions(), before);
    assert_eq!(
        nirvana::module_readable::emit_c(&module).unwrap().code,
        emitted
    );
}

#[test]
fn optimized_c_loops_expose_phi_edges_and_json_reports_definition_use_consistency() {
    let scratch = native::Scratch::new();
    for opt in ["-O0", "-O2"] {
        for pie in [false, true] {
            let binary = scratch.0.join(format!("fixture-{opt}-{pie}"));
            compile(
                Command::new("cc")
                    .args([
                        "-std=c11",
                        "-Wall",
                        "-Wextra",
                        "-Werror",
                        "-pedantic",
                        "-fno-lto",
                        "-fno-stack-protector",
                        opt,
                    ])
                    .args(if pie {
                        ["-fPIE", "-pie"]
                    } else {
                        ["-fno-pie", "-no-pie"]
                    })
                    .arg(native::fixture_root().join("value-lifetimes.c"))
                    .arg("-o")
                    .arg(&binary),
            );
            assert!(Command::new(&binary).status().unwrap().success());
            let module = lift(&binary, pie);
            let analysis = module_values::analyze(&module.program).unwrap();
            for name in ["main", "lifetime_mix", "lifetime_fold"] {
                let function = analysis
                    .functions
                    .iter()
                    .find(|f| f.function.name == name)
                    .unwrap();
                assert!(
                    function.result.is_ok(),
                    "{opt} pie={pie} {name}: {:?}",
                    function.result
                );
            }
            let fold = analysis
                .functions
                .iter()
                .find(|f| f.function.name == "lifetime_fold")
                .unwrap()
                .result
                .as_ref()
                .unwrap();
            assert!(
                fold.graph()
                    .values
                    .iter()
                    .any(|d| matches!(d, Definition::Phi { inputs, .. } if inputs.len() > 1))
            );
            assert!(
                fold.lifetimes()
                    .edges
                    .iter()
                    .any(|e| e.from.is_some_and(|from| e.to <= from))
            );
            assert!(
                fold.boundaries()
                    .iter()
                    .any(|b| matches!(b.kind, BoundaryKind::Call { .. }))
            );
            let output = Command::new(env!("CARGO_BIN_EXE_nirvana"))
                .arg(&binary)
                .args(["--emit", "module-values"])
                .output()
                .unwrap();
            assert!(
                output.status.success(),
                "{}",
                String::from_utf8_lossy(&output.stderr)
            );
            let mut python = Command::new("python3")
                .args(["-c", JSON_CHECK])
                .stdin(Stdio::piped())
                .spawn()
                .unwrap();
            python
                .stdin
                .take()
                .unwrap()
                .write_all(&output.stdout)
                .unwrap();
            assert!(python.wait().unwrap().success());
            // ABI register inputs and all unknown call outputs are visibly
            // distinct from real arithmetic definitions and observation events.
            assert_eq!(analysis.to_json().unwrap().as_bytes(), output.stdout);
        }
    }
}

const JSON_CHECK: &str = r#"
import json,sys
r=json.load(sys.stdin)
assert r['schema']=='nirvana-module-values-v1'
assert r['scope']=='function-entry-and-normal-call-continuations'
for f in r['functions']:
    if f['status']!='analyzed': continue
    v=f['values']; assert [x['id'] for x in v]==list(range(len(v)))
    p={(x['site']['instruction'],x['site']['assignment']):x for b in f['blocks'] for x in b['points']}
    for x in v:
        d=x['definition']
        if d['kind'] in ('assignment','observation','opaque-output'):
            assert p[d['site']['instruction'],d['site']['assignment']]['definition']==x['id']
        for u in x['uses']:
            if u['kind']=='point':
                point=p[u['site']['instruction'],u['site']['assignment']]
                assert point['reads'][u['read']]['value']==x['id']
            else:
                assert any(i['value']==x['id'] and i['predecessor']==u['predecessor'] for i in v[u['value']]['definition']['inputs'])
    for point in p.values():
        for i,read in enumerate(point['reads']):
            assert {'kind':'point','site':point['site'],'read':i} in v[read['value']]['uses']
            assert read['value'] in point['before']
        for key in ('before','after'): assert point[key]==sorted(set(point[key]))
    for b in f['boundaries']:
        assert [x['register'] for x in b['inputs']]==list(range(f['guest_registers']))
        assert len(b['outputs'])==(f['guest_registers'] if b['kind']=='call' else 0)
        assert all(v[x['value']]['definition']['kind']=='opaque-output' for x in b['outputs'])
        assert not ({x['value'] for x in b['inputs']} & {x['value'] for x in b['outputs']})
"#;

#[test]
fn malformed_cli_combinations_are_rejected() {
    let scratch = native::Scratch::new();
    let path = scratch.0.join("empty");
    std::fs::write(&path, []).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_nirvana"))
        .arg(path)
        .args(["--emit", "module-values", "--raw"])
        .output()
        .unwrap();
    assert!(!output.status.success());
    assert!(String::from_utf8_lossy(&output.stderr).contains("module modes require a linked ELF"));
}

#[test]
fn vector_guard_reads_keep_original_assignment_indices_and_limits_are_local() {
    let scratch = native::Scratch::new();
    let source = scratch.0.join("guards.S");
    let binary = scratch.0.join("guards");
    std::fs::write(
        &source,
        r#"
.text
.globl main
.type main,@function
main:
    call leaf
    ret
.size main,.-main
.type leaf,@function
leaf:
    movdqa (%rdi),%xmm0
    movdqa %xmm0,(%rsi)
    ret
.size leaf,.-leaf
.type oversized,@function
oversized:
    .rept 104
    call leaf
    .endr
    ret
.size oversized,.-oversized
.section .note.GNU-stack,"",@progbits
"#,
    )
    .unwrap();
    compile(
        Command::new("cc")
            .arg("-no-pie")
            .arg(&source)
            .arg("-o")
            .arg(&binary),
    );
    let module = lift(&binary, false);
    let analysis = module_values::analyze(&module.program).unwrap();
    let leaf = analysis
        .functions
        .iter()
        .find(|f| f.function.name == "leaf")
        .unwrap()
        .result
        .as_ref()
        .unwrap();
    let guards: Vec<_> = points(leaf)
        .filter(|p| leaf.roles().get(&p.site) == Some(&PointRole::VectorGuard))
        .collect();
    assert_eq!(guards.len(), 2);
    assert_eq!(guards[0].reads[0].register, Reg(7));
    assert_eq!(guards[1].reads[0].register, Reg(6));
    for instruction in module.program.instructions() {
        if let module_ir::Instruction::Vector(vector) = instruction {
            for (original, _) in vector.assignments.iter().enumerate() {
                let site = nirvana::ssa::Site {
                    instruction: vector.address,
                    assignment: Some(original + 1),
                };
                assert_eq!(
                    leaf.roles()[&site],
                    PointRole::VectorAssignment { original }
                );
            }
        }
    }
    let oversized = analysis
        .functions
        .iter()
        .find(|f| f.function.name == "oversized")
        .unwrap();
    assert!(
        oversized
            .result
            .as_ref()
            .unwrap_err()
            .contains("assignment limit")
    );
    assert!(
        analysis
            .to_json()
            .unwrap()
            .contains("\"status\":\"unavailable\"")
    );
}

use crate::support::native;

use nirvana::ir::Reg;
use nirvana::linked_elf::LinkedOptions;
use nirvana::module_ir::{self, Module};
use nirvana::module_values::{self, BoundaryKind, CallContract, FunctionValues, PointRole};
use nirvana::ssa::{Definition, ValueId};
use nirvana::value_liveness::Use;
use std::collections::BTreeSet;
use std::io::Write as _;
use std::path::Path;
use std::process::{Command, Stdio};

use crate::support::native::compile;
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
    assert!(matches!(
        call.call_contract,
        Some(CallContract::Closed { .. })
    ));
    assert!(call.inputs.len() < 80);
    assert!(call.outputs.len() < 80);
    // Preserved identities are retained only when live after this call; flags
    // overwritten by the following ADD need no continuation mapping.
    assert!(call.outputs.len() + call.preserved.len() <= 80);
    let Some(CallContract::Closed { callee }) = call.call_contract else {
        panic!()
    };
    let contract = analysis.call_summaries().at(callee).unwrap();
    assert_eq!(contract.clobbers.len() + contract.preserved.len(), 80);
    assert!(call.preserved.iter().any(|v| v.register == Reg(4)));
    assert!(call.preserved.iter().any(|v| v.register == Reg(7)));
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
        if !matches!(boundary.call_contract, Some(CallContract::Closed { .. })) {
            assert_eq!(boundary.inputs.len(), module.program.register_count());
        }
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
    assert!(matches!(
        indirect.boundaries()[0].call_contract,
        Some(CallContract::Opaque { .. })
    ));
    assert_eq!(indirect.boundaries()[0].inputs.len(), 80);
    assert_eq!(indirect.boundaries()[0].outputs.len(), 80);
    assert!(indirect.boundaries()[0].preserved.is_empty());
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
            // Checked call footprints and remaining unknown outputs are visibly
            // distinct from arithmetic definitions and observation events.
            assert_eq!(analysis.to_json().unwrap().as_bytes(), output.stdout);
        }
    }
}

const JSON_CHECK: &str = r#"
import json,sys
r=json.load(sys.stdin)
assert r['schema']=='nirvana-module-values-v3'
assert r['scope']=='function-entry-and-normal-effect-continuations'
summaries={f['address']:f['call_summary'] for f in r['functions']}
proof=r['call_verification']
assert proof['model']=='nirvana-closed-call-contract-v1' and proof['status']=='checked'
assert proof['scope']=='finite-successful-calls'
assert proof['functions']==len(r['functions'])
assert proof['closed_functions']==sum(s['closed'] for s in summaries.values())
assert proof['call_edges']==sum(len(s['callees']) for s in summaries.values() if s['closed'])
assert proof['reachable_instructions']>=proof['closed_functions']
stack=proof['stack_verification']
assert stack['model']=='nirvana-entry-stack-facts-v1' and stack['status']=='checked'
assert stack['instructions']==proof['reachable_instructions']
assert stack['points']>=stack['instructions'] and stack['known_values']>=proof['closed_functions']
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
        contract=b['call_contract']
        if b['kind']=='divide':
            assert b['width'] in (8,16,32,64) and isinstance(b['signed'],bool)
            assert b['continuation']>b['address'] and contract is None
            expected=[0] if b['width']==8 else [0,2]
            assert [x['register'] for x in b['inputs']]==expected
            assert [x['register'] for x in b['outputs']]==expected
            assert not b['target_reads']
            source=next(point for point in p.values() if point['site']['instruction']==b['address'] and point['role']['kind']=='divide-source')
            assert source['reads']==b['operand_reads']
        elif contract and contract['kind']=='closed':
            summary=summaries[contract['callee']]; assert summary['closed']
            assert [x['register'] for x in b['inputs']]==summary['reads']
            assert [x['register'] for x in b['outputs']]==summary['clobbers']
            assert all(x['register'] in summary['preserved'] for x in b['preserved'])
            block=next(block for block in f['blocks'] if any(p['site']['instruction']==b['address'] for p in block['points']))
            assert all(x['value'] in block['live_out'] for x in b['preserved'])
        else:
            assert [x['register'] for x in b['inputs']]==list(range(f['guest_registers']))
            assert len(b['outputs'])==(f['guest_registers'] if b['kind']=='call' else 0)
            assert not b['preserved']
        assert all(v[x['value']]['definition']['kind']=='opaque-output' for x in b['outputs'])
        assert not ({x['value'] for x in b['inputs']} & {x['value'] for x in b['outputs']})
        assert not ({x['register'] for x in b['preserved']} & {x['register'] for x in b['outputs']})
    recovery=f['local_recovery']
    if recovery['status']=='available':
        mapping=recovery['by_value']; count=recovery['locals']
        assert len(mapping)==len(v) and set(mapping)==set(range(count))
        for value in v:
            if value['definition']['kind'] in ('initial','analysis-scratch'):
                assert mapping.count(mapping[value['id']])==1
        for point in p.values():
            for key in ('before','after'):
                colors=[mapping[i] for i in point[key]]
                assert len(colors)==len(set(colors))
        expected={(None,f['address']):[]}
        for value in v:
            if value['definition']['kind']=='phi':
                destination=mapping[value['id']]
                for item in value['definition']['inputs']:
                    source=mapping[item['value']]
                    if source!=destination: expected.setdefault((item['predecessor'],value['definition']['block']),[]).append([destination,source])
        assert {(e['from'],e['to']) for e in recovery['edges']}==set(expected)
        for edge in recovery['edges']:
            assert edge['parallel']==sorted(expected[edge['from'],edge['to']])
            actual=list(range(count))+[None]; before=list(actual)
            for destination,source in edge['sequential']:
                assert 0<=destination<=count and 0<=source<=count and actual[source] is not None
                actual[destination]=actual[source]
            for destination,source in edge['parallel']: before[destination]=source
            assert actual[:count]==before[:count]
"#;

#[test]
fn division_report_separates_operand_observations_from_unknown_results() {
    let scratch = native::Scratch::new();
    let source = scratch.0.join("division.S");
    let binary = scratch.0.join("division");
    std::fs::write(
        &source,
        r#"
.text
.globl main
.type main,@function
main:
    mov %rax,%rbx
    divb %dl
    idivw %cx
    divl (%rdi)
    idivq %rsi
    add %rbx,%rax
    ret
.size main,.-main
.section .note.GNU-stack,"",@progbits
"#,
    )
    .unwrap();
    compile(
        Command::new("cc")
            .arg("-no-pie")
            .arg(source)
            .arg("-o")
            .arg(&binary),
    );
    let module = lift(&binary, false);
    let values = module_values::analyze(&module.program).unwrap();
    let main = values
        .functions
        .iter()
        .find(|f| f.function.name == "main")
        .unwrap()
        .result
        .as_ref()
        .unwrap();
    assert_eq!(
        main.boundaries()
            .iter()
            .filter(|b| matches!(b.kind, BoundaryKind::Divide { .. }))
            .count(),
        4
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
        .write_all(values.to_json().unwrap().as_bytes())
        .unwrap();
    assert!(python.wait().unwrap().success());
}

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

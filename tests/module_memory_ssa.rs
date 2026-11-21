#[path = "support/native.rs"]
#[allow(dead_code)]
mod native;

use nirvana::ir::AccessKind;
use nirvana::memory_ssa::{Analysis, Definition, EffectKind, Event, Phase};
use nirvana::module_ir::{self, Instruction};
use nirvana::module_values::{self, FunctionValues, PointRole};
use nirvana::type_infer::AddressShape;
use std::io::Write;
use std::process::{Command, Stdio};

fn values<'a>(analysis: &'a module_values::Analysis, name: &str) -> &'a FunctionValues {
    analysis
        .functions
        .iter()
        .find(|f| f.function.name == name)
        .unwrap()
        .result
        .as_ref()
        .unwrap()
}
fn memory(values: &FunctionValues) -> &Analysis {
    values.memory().unwrap().as_ref().unwrap()
}

#[test]
fn calls_string_stores_and_unknown_register_outputs_keep_memory_generations() {
    let scratch = native::Scratch::new();
    let source = scratch.0.join("memory.S");
    let binary = scratch.0.join("memory");
    std::fs::write(
        &source,
        r#"
.text
.globl main
.type main,@function
main: xor %eax,%eax
ret
.size main,.-main
.type callee,@function
callee:
sub $16,%rsp
movq $2,(%rsp)
add $16,%rsp
ret
.size callee,.-callee
.type caller,@function
caller:
movq $1,(%rdi)
movq $2,8(%rdi)
mov (%rdi),%rax
call callee
mov (%rdi),%rax
ret
.size caller,.-caller
.type plt_caller,@function
plt_caller:
call puts@PLT
mov (%rdi),%rax
ret
.size plt_caller,.-plt_caller
.type string_caller,@function
string_caller:
movq $1,(%rdi)
rep stosq
mov (%rdi),%rax
ret
.size string_caller,.-string_caller
.type division_caller,@function
division_caller:
div %rcx
mov (%rax),%rax
ret
.size division_caller,.-division_caller
.section .note.GNU-stack,"",@progbits
"#,
    )
    .unwrap();
    native::compile(
        Command::new("cc")
            .arg("-no-pie")
            .arg(&source)
            .arg("-o")
            .arg(&binary),
    );
    let module = module_ir::lift_elf(
        &std::fs::read(binary).unwrap(),
        "main",
        nirvana::linked_elf::LinkedOptions {
            load_bias: 0,
            ..Default::default()
        },
    )
    .unwrap();
    let original = module.program.instructions().to_vec();
    let analysis = module_values::analyze(&module.program).unwrap();
    assert_eq!(original, module.program.instructions());
    let caller = values(&analysis, "caller");
    let call = caller
        .boundaries()
        .iter()
        .find(|b| matches!(b.kind, module_values::BoundaryKind::Call { .. }))
        .unwrap();
    assert!(matches!(
        call.call_contract,
        Some(module_values::CallContract::Closed { .. })
    ));
    let m = memory(caller);
    let queries = m.queries().as_ref().unwrap();
    let before = &queries[0].candidates;
    assert_eq!(before.len(), 1);
    let store = before[0].definition;
    assert!(matches!(m.definitions()[store.0], Definition::Store { .. }));
    let after = &queries[1].candidates;
    assert!(after.iter().any(|c| c.definition == store));
    assert!(after.iter().any(|c| matches!(m.definitions()[c.definition.0],Definition::Opaque{effect,..} if effect.kind==EffectKind::Call)));
    assert_eq!(
        after.len(),
        2,
        "the disjoint neighboring Store stays excluded"
    );

    for (name, kind) in [
        ("plt_caller", Some(EffectKind::Call)),
        ("string_caller", Some(EffectKind::StringStore)),
        ("division_caller", None),
    ] {
        let v = values(&analysis, name);
        let m = memory(v);
        let load=m.accesses().iter().find(|a| {
            a.source.kind==AccessKind::Read && matches!(a.source.address,AddressShape::Base{base,..} if matches!(&v.graph().values[base.0],nirvana::ssa::Definition::Assignment{site,..} if matches!(v.roles().get(site),Some(PointRole::OpaqueOutput{..}))))
        }).expect("effect output is a fresh SSA atom rather than placeholder zero");
        assert!(matches!(
            load.source.address,
            AddressShape::Base { offset: 0, .. }
        ));
        if let Some(kind) = kind {
            assert!(
                m.definitions()
                    .iter()
                    .any(|d| matches!(d,Definition::Opaque{effect,..} if effect.kind==kind))
            );
        } else {
            assert!(
                m.definitions()
                    .iter()
                    .all(|d| !matches!(d, Definition::Opaque { .. }))
            );
        }
    }
    let plt = memory(values(&analysis, "plt_caller"));
    let call = module
        .program
        .instructions()
        .iter()
        .find(|i| {
            matches!(
                i,
                Instruction::Transfer {
                    target: module_ir::Target::Plt(_),
                    ..
                }
            )
        })
        .unwrap()
        .address();
    let block = plt.blocks().iter().find(|b| b.start == call).unwrap();
    assert!(matches!(
        block.events.as_slice(),
        [Event::Effect(_), Event::Access(_), Event::Effect(_)]
    ));
    if let Event::Effect(id) = block.events[0] {
        assert!(
            matches!(plt.definitions()[id.0],Definition::Opaque{effect,..} if effect.kind==EffectKind::CallStack && effect.phase==Phase::Before)
        );
    }

    // Check all serialized dependency wires independently of construction.
    let mut child=Command::new("python3").args(["-c",r#"
import json,sys
report=json.load(sys.stdin)
checked=0
for function in report['functions']:
    if function['status']!='analyzed': continue
    m=function['memory_ssa']
    assert m['status']=='analyzed',m
    defs=m['definitions']; accesses=m['accesses']
    assert defs[0]['kind']=='initial'
    assert [d['id'] for d in defs]==list(range(len(defs)))
    assert [a['id'] for a in accesses]==list(range(len(accesses)))
    visited=[]
    blocks={b['start']:b for b in m['blocks']}
    for block in blocks.values():
        current=block['entry']; entry=defs[current]
        assert entry['kind']=='phi' and entry['block']==block['start']
        for incoming in entry['inputs']:
            pred=incoming['predecessor']
            assert incoming['memory']==(0 if pred is None else blocks[pred]['exit'])
        for event in block['events']:
            if 'effect' in event:
                i=event['effect']; d=defs[i]
                assert d['kind']=='opaque' and d['previous']==current
                current=i
            else:
                i=event['access']; a=accesses[i]; visited.append(i)
                assert a['incoming']==current
                if a['kind']=='write':
                    current=a['definition']; d=defs[current]
                    assert d['kind']=='store' and d['access']==i and d['previous']==a['incoming']
                else: assert a['definition'] is None
        assert block['exit']==current
    assert sorted(visited)==list(range(len(accesses)))
    assert m['queries']['status']=='analyzed'
    assert [q['access'] for q in m['queries']['reads']]==[a['id'] for a in accesses if a['kind']=='read']
    for query in m['queries']['reads']:
        assert query['candidates']
        assert all(defs[c['definition']]['kind'] in ('initial','store','opaque') for c in query['candidates'])
    checked+=1
assert checked>=6
"#]).stdin(Stdio::piped()).spawn().unwrap();
    child
        .stdin
        .take()
        .unwrap()
        .write_all(analysis.to_json().unwrap().as_bytes())
        .unwrap();
    assert!(child.wait().unwrap().success());
}

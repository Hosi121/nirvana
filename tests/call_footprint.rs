#[path = "support/native.rs"]
#[allow(dead_code)]
mod native;

use nirvana::call_footprint::{self, Analysis, FunctionSummary};
use nirvana::ir::Reg;
use nirvana::linked_elf::LinkedOptions;
use nirvana::module_ir::{self, Module};
use std::process::Command;

fn fixture() -> Module {
    let scratch = native::Scratch::new();
    let source = scratch.0.join("footprints.S");
    let binary = scratch.0.join("footprints");
    std::fs::write(&source, SOURCE).unwrap();
    let output = Command::new("cc")
        .args(["-no-pie", "-fno-pie"])
        .arg(&source)
        .arg("-o")
        .arg(&binary)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    module_ir::lift_elf(
        &std::fs::read(binary).unwrap(),
        "main",
        LinkedOptions {
            load_bias: 0,
            ..Default::default()
        },
    )
    .unwrap()
}

fn summary<'a>(module: &Module, analysis: &'a Analysis, name: &str) -> &'a FunctionSummary {
    let address = module
        .program
        .functions()
        .iter()
        .find(|f| f.name == name)
        .unwrap()
        .address;
    analysis.at(address).unwrap()
}

#[test]
fn closed_leaves_spills_recursion_and_tails_preserve_only_unwritten_registers() {
    let module = fixture();
    let before = module.program.instructions().to_vec();
    let analysis = call_footprint::analyze(&module.program).unwrap();
    for name in [
        "main",
        "leaf",
        "spill",
        "recurse",
        "tail",
        "vector_ok",
        "unreachable_bad",
        "stack_call",
    ] {
        let s = summary(&module, &analysis, name);
        assert!(s.closed, "{name}: {:?}", s.reason);
        assert!(s.reason.is_none());
        assert!(s.preserved.contains(&Reg(nirvana::x86::RSP)));
        assert!(!s.clobbers.contains(&Reg(nirvana::x86::RSP)));
    }
    let leaf = summary(&module, &analysis, "leaf");
    assert!(leaf.clobbers.contains(&Reg(0)));
    assert!(leaf.preserved.contains(&Reg(3)));
    let spill = summary(&module, &analysis, "spill");
    // Even an explicitly restored register remains a conservative clobber.
    assert!(spill.clobbers.contains(&Reg(3)));
    for name in ["main", "tail", "stack_call"] {
        let s = summary(&module, &analysis, name);
        assert!(s.clobbers.contains(&Reg(0)));
        assert!(s.callees.contains(&leaf.address));
    }
    let recursive = summary(&module, &analysis, "recurse");
    assert!(recursive.callees.contains(&recursive.address));
    let vector = summary(&module, &analysis, "vector_ok");
    assert!(vector.reads.contains(&Reg(32)));
    assert!(vector.reads.contains(&Reg(33)));
    for function in &analysis.functions {
        assert!(function.reads.windows(2).all(|w| w[0].0 < w[1].0));
        assert!(function.clobbers.windows(2).all(|w| w[0].0 < w[1].0));
        assert!(function.preserved.windows(2).all(|w| w[0].0 < w[1].0));
        assert!(function.callees.windows(2).all(|w| w[0] < w[1]));
        for register in &function.clobbers {
            assert!(function.reads.contains(register));
        }
    }
    assert!(
        analysis
            .functions
            .windows(2)
            .all(|w| w[0].address < w[1].address)
    );
    assert_eq!(module.program.instructions(), before);
}

#[test]
fn actual_return_slot_memory_and_stack_failures_poison_transitive_recursive_callers() {
    let module = fixture();
    let analysis = call_footprint::analyze(&module.program).unwrap();
    for name in [
        "forged_return",
        "straddles",
        "global_store",
        "positive_store",
        "wrapped_store",
        "vector_bad",
        "loaded_rsp",
        "unbalanced_rsp",
        "extra_pop",
        "indirect",
        "plt_call",
        "bad_tail",
        "positive_call",
        "poison_a",
        "poison_b",
        "poison_outer",
        "unknown_after_call",
        "unknown_is_not_zero",
    ] {
        let s = summary(&module, &analysis, name);
        assert!(!s.closed, "{name}");
        assert!(s.reason.is_some(), "{name}");
        assert_eq!(s.reads, (0..80).map(Reg).collect::<Vec<_>>(), "{name}");
        assert_eq!(s.clobbers, s.reads, "{name}");
        assert!(s.preserved.is_empty(), "{name}");
    }
}

const SOURCE: &str = r#"
.text
.macro function name
.globl \name
.type \name,@function
\name:
.endm
.macro endfunction name
.size \name,.-\name
.endm
function main
    call leaf
    ret
endfunction main
function leaf
    mov $3,%rax
    ret
endfunction leaf
function spill
    push %rbx
    mov $99,%rbx
    pop %rbx
    ret
endfunction spill
function recurse
    test %rdi,%rdi
    jz .Lrecurse_end
    sub $8,%rsp
    sub $1,%rdi
    call recurse
    add $8,%rsp
.Lrecurse_end:
    ret
endfunction recurse
function tail
    jmp leaf
endfunction tail
function stack_call
    sub $16,%rsp
    call leaf
    add $16,%rsp
    ret
endfunction stack_call
function vector_ok
    movdqu %xmm0,-16(%rsp)
    ret
endfunction vector_ok
function unreachable_bad
    ret
    mov %rax,(%rsp)
endfunction unreachable_bad
function forged_return
    movabs $0x401234,%rax
    mov %rax,(%rsp)
    ret
endfunction forged_return
function straddles
    mov %rax,-4(%rsp)
    ret
endfunction straddles
function global_store
    mov %rax,(%rdi)
    ret
endfunction global_store
function positive_store
    mov %rax,8(%rsp)
    ret
endfunction positive_store
function wrapped_store
    movabs $0x8000000000000000,%r11
    add %rsp,%r11
    mov %rax,(%r11)
    ret
endfunction wrapped_store
function vector_bad
    movdqu %xmm0,-8(%rsp)
    ret
endfunction vector_bad
function loaded_rsp
    mov (%rdi),%rsp
    ret
endfunction loaded_rsp
function unbalanced_rsp
    sub $8,%rsp
    ret
endfunction unbalanced_rsp
function extra_pop
    ret $8
endfunction extra_pop
function indirect
    call *%rdi
    ret
endfunction indirect
function plt_call
    call puts@PLT
    ret
endfunction plt_call
function bad_tail
    sub $8,%rsp
    jmp leaf
endfunction bad_tail
function positive_call
    add $8,%rsp
    call leaf
    sub $8,%rsp
    ret
endfunction positive_call
function poison_a
    call poison_b
    ret
endfunction poison_a
function poison_b
    call poison_a
    call forged_return
    ret
endfunction poison_b
function poison_outer
    call poison_a
    ret
endfunction poison_outer
function unknown_after_call
    mov %rsp,%rbx
    call leaf
    mov %rax,-8(%rbx)
    ret
endfunction unknown_after_call
function unknown_is_not_zero
    call leaf
    add %rsp,%rbx
    mov %rax,-8(%rbx)
    ret
endfunction unknown_is_not_zero
.section .note.GNU-stack,"",@progbits
"#;

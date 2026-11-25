use crate::support::native;

use nirvana::call_footprint::{self, Analysis, FunctionSummary};
use nirvana::ir::Reg;
use nirvana::linked_elf::LinkedOptions;
use nirvana::module_ir::{self, Module};
use std::process::Command;

fn fixture() -> Module {
    fixture_source(SOURCE)
}

fn fixture_source(assembly: &str) -> Module {
    let scratch = native::Scratch::new();
    let source = scratch.0.join("footprints.S");
    let binary = scratch.0.join("footprints");
    std::fs::write(&source, assembly).unwrap();
    let output = native::compile_output(
        Command::new("cc")
            .args(["-no-pie", "-fno-pie"])
            .arg(&source)
            .arg("-o")
            .arg(&binary),
    );
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

#[test]
fn source_checker_rejects_missing_and_forged_summary_members() {
    let module = fixture();
    let original = call_footprint::analyze(&module.program).unwrap();
    let evidence = call_footprint::validate(&module.program, &original).unwrap();
    assert_eq!(evidence.functions, original.functions.len());
    assert_eq!(
        evidence.closed_functions,
        original.functions.iter().filter(|s| s.closed).count()
    );
    assert!(evidence.reachable_instructions > evidence.closed_functions);
    assert!(evidence.call_edges >= 4);
    let leaf = original
        .functions
        .iter()
        .position(|s| s.address == summary(&module, &original, "leaf").address)
        .unwrap();
    let main = original
        .functions
        .iter()
        .position(|s| s.address == summary(&module, &original, "main").address)
        .unwrap();
    for change in [
        "function",
        "function-order",
        "read",
        "clobber",
        "callee",
        "extra-callee",
        "nonentry-callee",
        "preserved",
        "register-range",
        "duplicate-register",
        "reason",
        "opaque",
    ] {
        let mut candidate = original.clone();
        match change {
            "function" => {
                candidate.functions.pop();
            }
            "function-order" => candidate.functions.swap(0, 1),
            "read" => {
                candidate.functions[leaf].reads.pop();
            }
            "clobber" => {
                candidate.functions[leaf].clobbers.retain(|r| r.0 != 0);
                candidate.functions[leaf].preserved.push(Reg(0));
                candidate.functions[leaf].preserved.sort_by_key(|r| r.0);
            }
            "callee" => candidate.functions[main].callees.clear(),
            "extra-callee" => {
                candidate.functions[main]
                    .callees
                    .push(summary(&module, &original, "spill").address);
                candidate.functions[main].callees.sort_unstable();
            }
            "nonentry-callee" => candidate.functions[main].callees[0] += 1,
            "preserved" => candidate.functions[leaf].preserved.clear(),
            "register-range" => candidate.functions[leaf].reads.push(Reg(80)),
            "duplicate-register" => {
                let first = candidate.functions[leaf].reads[0];
                candidate.functions[leaf].reads.insert(0, first);
            }
            "reason" => candidate.functions[leaf].reason = Some("unproved".into()),
            "opaque" => {
                candidate
                    .functions
                    .iter_mut()
                    .find(|s| !s.closed)
                    .unwrap()
                    .preserved
                    .push(Reg(0));
            }
            _ => unreachable!(),
        }
        assert!(
            call_footprint::validate(&module.program, &candidate).is_err(),
            "{change}"
        );
    }
}

fn forge_closed(summary: &mut FunctionSummary) {
    summary.closed = true;
    summary.reason = None;
    summary.reads = (0..80).map(Reg).collect();
    summary.clobbers = (0..80)
        .filter(|r| *r != nirvana::x86::RSP)
        .map(Reg)
        .collect();
    summary.preserved = vec![Reg(nirvana::x86::RSP)];
}

#[test]
fn forged_closed_claims_fail_at_the_original_return_slot_obligation() {
    let module = fixture();
    let original = call_footprint::analyze(&module.program).unwrap();
    for (name, reason) in [
        ("forged_return", "store touches return slot"),
        ("straddles", "store touches return slot"),
        ("global_store", "store touches return slot"),
        ("positive_store", "store touches return slot"),
        ("wrapped_store", "store touches return slot"),
        ("vector_bad", "store touches return slot"),
        ("loaded_rsp", "return stack"),
        ("unbalanced_rsp", "return stack"),
        ("extra_pop", "return stack"),
        ("indirect", "unknown call target"),
        ("plt_call", "unknown call target"),
        ("bad_tail", "call link/stack"),
        ("positive_call", "call link/stack"),
        ("poison_a", "open callee"),
        ("poison_b", "open callee"),
    ] {
        let address = summary(&module, &original, name).address;
        let mut candidate = original.clone();
        forge_closed(
            candidate
                .functions
                .iter_mut()
                .find(|s| s.address == address)
                .unwrap(),
        );
        let error = call_footprint::validate(&module.program, &candidate).unwrap_err();
        assert!(error.contains(reason), "{name}: {error}");
    }
}

#[test]
fn recursive_equations_allow_sound_extra_clobbers_and_opaque_fallback() {
    let module = fixture();
    let mut candidate = call_footprint::analyze(&module.program).unwrap();
    let address = summary(&module, &candidate, "recurse").address;
    let recursive = candidate
        .functions
        .iter_mut()
        .find(|s| s.address == address)
        .unwrap();
    for registers in [&mut recursive.reads, &mut recursive.clobbers] {
        assert!(!registers.contains(&Reg(79)));
        registers.push(Reg(79));
    }
    recursive.preserved.retain(|r| r.0 != 79);
    call_footprint::validate(&module.program, &candidate).unwrap();
    for summary in &mut candidate.functions {
        summary.closed = false;
        summary.reason = Some("conservative fallback".into());
        summary.reads = (0..80).map(Reg).collect();
        summary.clobbers = summary.reads.clone();
        summary.preserved.clear();
    }
    let evidence = call_footprint::validate(&module.program, &candidate).unwrap();
    assert_eq!(evidence.closed_functions, 0);
    assert_eq!(evidence.call_edges, 0);
}

#[test]
fn entry_backedges_unknown_results_and_recursive_tail_effects_are_checked() {
    let module = fixture_source(&format!("{SOURCE}\n{VALIDATOR_SOURCE}"));
    let original = call_footprint::analyze(&module.program).unwrap();
    for name in ["byte_stack", "pointer_callee", "mutual_a", "mutual_b"] {
        assert!(summary(&module, &original, name).closed, "{name}");
    }
    for (name, reason) in [
        ("entry_backedge", "return stack"),
        ("divide_stack", "return stack"),
        ("call_pointer", "store touches return slot"),
    ] {
        assert!(!summary(&module, &original, name).closed, "{name}");
        let address = summary(&module, &original, name).address;
        let mut candidate = original.clone();
        forge_closed(
            candidate
                .functions
                .iter_mut()
                .find(|s| s.address == address)
                .unwrap(),
        );
        assert!(
            call_footprint::validate(&module.program, &candidate)
                .unwrap_err()
                .contains(reason),
            "{name}"
        );
    }
    for name in ["mutual_a", "mutual_b"] {
        let address = summary(&module, &original, name).address;
        let mut candidate = original.clone();
        let changed = candidate
            .functions
            .iter_mut()
            .find(|s| s.address == address)
            .unwrap();
        assert!(changed.clobbers.contains(&Reg(11)));
        changed.clobbers.retain(|r| r.0 != 11);
        changed.preserved.push(Reg(11));
        changed.preserved.sort_by_key(|r| r.0);
        assert!(
            call_footprint::validate(&module.program, &candidate)
                .unwrap_err()
                .contains("register equations"),
            "{name}"
        );
    }
}

const VALIDATOR_SOURCE: &str = r#"
.text
function entry_backedge
    test %rdi,%rdi
    jz .Lentry_done
    add $8,%rsp
    sub $1,%rdi
    jmp entry_backedge
.Lentry_done:
    ret
endfunction entry_backedge
function divide_stack
    mov %rsp,%rdx
    div %rcx
    mov %rdx,%rsp
    ret
endfunction divide_stack
function byte_stack
    mov %rsp,%rdx
    div %cl
    mov %rdx,%rsp
    ret
endfunction byte_stack
function call_pointer
    lea -8(%rsp),%r11
    call pointer_callee
    mov %rax,(%r11)
    ret
endfunction call_pointer
function pointer_callee
    lea 8(%rsp),%r11
    ret
endfunction pointer_callee
function mutual_a
    test %rdi,%rdi
    jz .Lmutual_done
    sub $8,%rsp
    sub $1,%rdi
    call mutual_b
    add $8,%rsp
.Lmutual_done:
    ret
endfunction mutual_a
function mutual_b
    mov $42,%r11
    jmp mutual_a
endfunction mutual_b
"#;

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

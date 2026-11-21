use crate::support::native;
use nirvana::linked_elf::LinkedOptions;
use nirvana::module_ir::{self, Limits, RejectImports, Status};
use std::process::Command;

fn module(assembly: &str) -> module_ir::Module {
    let scratch = native::Scratch::new();
    let source = scratch.0.join("input.S");
    let binary = scratch.0.join("input");
    std::fs::write(
        &source,
        format!("{assembly}\n.section .note.GNU-stack,\"\",@progbits\n"),
    )
    .unwrap();
    let result = native::compile_output(
        Command::new("cc")
            .args(["-no-pie", "-Wl,--build-id=none"])
            .arg(&source)
            .arg("-o")
            .arg(&binary),
    );
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
    module_ir::lift_elf(
        &std::fs::read(binary).unwrap(),
        "main",
        LinkedOptions {
            load_bias: 0,
            stack_size: 4096,
        },
    )
    .unwrap()
}

#[test]
fn proposed_case_entries_have_no_inherited_flag_assumptions() {
    let m = module(
        r#"
.text
.globl main
.type main,@function
main:
    cmp $1,%edi
    ja done
    lea table(%rip),%rdx
    movslq (%rdx,%rdi,4),%rax
    add %rdx,%rax
    notrack jmp *%rax
case0:
    adc $1,%eax
    ret
case1:
    adc $2,%eax
    ret
done:
    xor %eax,%eax
    ret
.size main,.-main
.section .rodata
table:
    .long case0-table,case1-table
"#,
    );
    assert!(m.jump_tables.is_empty());
    assert!(
        m.jump_table_diagnostics
            .iter()
            .any(|(_, reason)| reason.contains("unavailable flags"))
    );
    let report = m
        .program
        .run(
            &m.initial_registers(),
            m.image.memory_base,
            &m.image.memory,
            Limits {
                instructions: 100,
                imports: 0,
            },
            &mut RejectImports,
        )
        .unwrap();
    assert!(matches!(report.status, Status::UnknownTarget(_)));
}

#[test]
fn an_overlapping_proposed_stream_retains_the_original_dynamic_transfer() {
    let m = module(
        r#"
.text
.globl main
.type main,@function
main:
    lea table(%rip),%rdx
    notrack jmp *(%rdx,%rdi,8)
    ret
.size main,.-main
.section .rodata
table:
    .quad main+1,main+2
"#,
    );
    assert!(m.jump_tables.is_empty());
    assert_eq!(m.jump_table_diagnostics.len(), 1);
    assert!(m.jump_table_diagnostics[0].1.contains("instruction"));
    let report = m
        .program
        .run(
            &m.initial_registers(),
            m.image.memory_base,
            &m.image.memory,
            Limits {
                instructions: 100,
                imports: 0,
            },
            &mut RejectImports,
        )
        .unwrap();
    assert!(matches!(report.status, Status::UnknownTarget(_)));
}

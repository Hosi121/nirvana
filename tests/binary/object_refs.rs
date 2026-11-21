use crate::support::native;
use nirvana::object_refs::{Literal, ObjectReferences, ReferenceUse, Target};
use std::process::Command;

fn assemble(body: &str, data: &str) -> Vec<u8> {
    let scratch = native::Scratch::new();
    let source = scratch.0.join("fixture.s");
    let object = source.with_extension("o");
    std::fs::write(&source,format!(".text\n.space 32,0x90\n.globl fixture\n.type fixture,@function\nfixture:\n{body}\n.size fixture,.-fixture\n{data}\n.section .note.GNU-stack,\"\",@progbits\n")).unwrap();
    let output = native::compile_output(
        Command::new("cc")
            .arg("-c")
            .arg(&source)
            .arg("-o")
            .arg(&object),
    );
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    std::fs::read(object).unwrap()
}
fn strings() -> &'static str {
    ".section .rodata,\"a\",@progbits\n.Lone: .asciz \"first\"\n.Ltwo: .asciz \"second\"\n"
}
fn analyze(body: &str) -> ObjectReferences {
    ObjectReferences::analyze(&assemble(body, strings()), "fixture").unwrap()
}
fn hint(report: &ObjectReferences, index: usize) -> Option<String> {
    report.call_hint(&report.calls[index])
}

#[test]
fn compiler_strings_bind_calls_across_optimizations_relocations_and_link_placements() {
    let scratch = native::Scratch::new();
    let mut observations = 0;
    for opt in ["-O0", "-O2"] {
        for (mode, flags) in [
            ("pie", vec![]),
            ("absolute", vec!["-fno-pie"]),
            ("got", vec!["-fno-plt"]),
            ("sections", vec!["-ffunction-sections", "-fdata-sections"]),
        ] {
            let object = scratch.0.join(format!("hello{opt}-{mode}.o"));
            let output = native::compile_output(
                Command::new("cc")
                    .args([
                        "-std=c11",
                        "-Wall",
                        "-Wextra",
                        "-Werror",
                        "-pedantic",
                        opt,
                        "-c",
                    ])
                    .args(flags)
                    .arg(native::fixture_root().join("references/hello.c"))
                    .arg("-o")
                    .arg(&object),
            );
            assert!(
                output.status.success(),
                "{}",
                String::from_utf8_lossy(&output.stderr)
            );
            let bytes = std::fs::read(&object).unwrap();
            let original = bytes.clone();
            let report = ObjectReferences::analyze(&bytes, "fixture").unwrap();
            assert_eq!(bytes, original);
            assert_eq!(report.calls.len(), 1, "{opt}/{mode}");
            assert_eq!(
                hint(&report, 0).as_deref(),
                Some("puts(\"Hello, world!\")"),
                "{opt}/{mode}"
            );
            assert_eq!(report.literals[0].bytes, b"Hello, world!");
            assert!(report.references.iter().all(|r| r.instruction.is_some()));
            if mode == "got" {
                assert!(
                    report
                        .references
                        .iter()
                        .any(|r| r.usage == Some(ReferenceUse::GotCall))
                );
            }
            if mode == "absolute" {
                assert!(report.references.iter().any(|r| r.relocation.kind == 10));
            }
            // The real system linker places the same object at two bases. A
            // puts interposer observes the actual argument bytes and return.
            let helper = scratch.0.join("oracle.c");
            std::fs::write(
                &helper,
                r#"#include <stdio.h>
#include <string.h>
int fixture(void);
int puts(const char *message) { fwrite(message,1,strlen(message),stdout); putchar('|'); return 37; }
int main(void) { int result=fixture(); printf("%d\n",result); return 0; }
"#,
            )
            .unwrap();
            for base in ["0x400000", "0x800000"] {
                let bin = scratch.0.join(format!("linked{opt}-{mode}-{base}"));
                let output = native::compile_output(
                    Command::new("cc")
                        .args(["-std=c11", "-fno-builtin", "-no-pie"])
                        .arg(format!("-Wl,-Ttext-segment={base}"))
                        .arg(&object)
                        .arg(&helper)
                        .arg("-o")
                        .arg(&bin),
                );
                assert!(
                    output.status.success(),
                    "{}",
                    String::from_utf8_lossy(&output.stderr)
                );
                let result = Command::new(bin).output().unwrap();
                assert!(result.status.success());
                assert_eq!(result.stdout, b"Hello, world!|37\n");
                observations += 1;
            }
        }
    }
    assert_eq!(observations, 16);
}

#[test]
fn section_symbol_addends_suffixes_and_register_copies_retain_exact_bytes() {
    let object = assemble(
        "lea .Ltwo+1(%rip),%rax\nmov %rax,%rdi\ncall puts@PLT\nret",
        strings(),
    );
    let original = nirvana::elf::read_function(&object, "fixture").unwrap();
    let report = ObjectReferences::analyze(&object, "fixture").unwrap();
    assert_eq!(report.section_offset, 32);
    assert_eq!(hint(&report, 0).as_deref(), Some("puts(\"econd\")"));
    assert_eq!(report.literals[0].offset, 7);
    assert!(matches!(
        report.calls[0].target,
        Some(Target::External { addend: 0, .. })
    ));
    assert_eq!(
        nirvana::elf::read_function(&object, "fixture").unwrap(),
        original
    );
}

#[test]
fn cfg_merges_keep_equal_addresses_and_decline_conflicting_arguments() {
    for second in [".Lone", ".Ltwo"] {
        let body = format!(
            "test %edi,%edi\nje .Lalt\nlea .Lone(%rip),%rdi\njmp .Ljoin\n.Lalt:\nlea {second}(%rip),%rdi\n.Ljoin:\ncall puts@PLT\nret"
        );
        let report = analyze(&body);
        assert_eq!(
            hint(&report, 0),
            if second == ".Lone" {
                Some("puts(\"first\")".into())
            } else {
                None
            }
        );
    }
    let scratch = native::Scratch::new();
    for opt in ["-O0", "-O2"] {
        let object = scratch.0.join(format!("choice{opt}.o"));
        native::object(
            &native::fixture_root().join("references/choice.c"),
            &object,
            opt,
            "fixture",
        );
        let report = ObjectReferences::analyze(&std::fs::read(object).unwrap(), "fixture").unwrap();
        assert_eq!(report.calls.len(), 1);
        assert!(hint(&report, 0).is_none());
        assert!(report.literals.iter().any(|l| l.bytes == b"first"));
        assert!(report.literals.iter().any(|l| l.bytes == b"second"));
    }
}

#[test]
fn loop_facts_converge_before_call_arguments_are_reported() {
    for update in ["nop", "xor %edi,%edi"] {
        let report = analyze(&format!(
            "lea .Lone(%rip),%rdi\n.Lloop:\ntest %esi,%esi\nje .Ldone\n{update}\ndec %esi\njmp .Lloop\n.Ldone:\ncall puts@PLT\nret"
        ));
        assert_eq!(
            hint(&report, 0),
            if update == "nop" {
                Some("puts(\"first\")".into())
            } else {
                None
            }
        );
    }
}

#[test]
fn calls_clobber_sysv_volatile_registers_and_preserve_saved_registers() {
    let report = analyze("lea .Lone(%rip),%rdi\ncall other@PLT\ncall puts@PLT\nret");
    assert_eq!(report.calls.len(), 2);
    assert!(hint(&report, 1).is_none());
    assert!(
        report.calls[0].integer_argument_registers[0]
            .literal
            .is_some()
    );
    let report = analyze("lea .Lone(%rip),%rbx\ncall other@PLT\nmov %rbx,%rdi\ncall puts@PLT\nret");
    assert_eq!(hint(&report, 1).as_deref(), Some("puts(\"first\")"));
}

#[test]
fn partial_register_writes_and_address_truncation_decline() {
    for update in [
        "movb $0,%dil",
        "movw $0,%di",
        "movl %edi,%edi",
        "add $0,%rdi",
        "mov .Ltwo(%rip),%rdi",
        "cmovz %rax,%rdi",
    ] {
        let report = analyze(&format!(
            "lea .Lone(%rip),%rdi\n{update}\ncall puts@PLT\nret"
        ));
        assert!(hint(&report, 0).is_none(), "{update}");
    }
}

#[test]
fn loading_data_is_distinct_from_taking_its_address() {
    let report = analyze("mov .Lone(%rip),%rdi\ncall puts@PLT\nret");
    assert!(hint(&report, 0).is_none());
    assert!(report.literals.is_empty());
    assert!(report.references.iter().any(|r| r.instruction.is_none()));
}

#[test]
fn writable_unterminated_and_overlong_data_keep_symbolic_addresses_only() {
    for data in [
        ".data\n.Lone:.asciz \"mutable\"".to_owned(),
        ".section .rodata,\"a\",@progbits\n.Lone:.ascii \"unterminated\"".to_owned(),
        ".section .rodata,\"a\",@progbits\n.Lone:.fill 4097,1,65\n.byte 0".to_owned(),
    ] {
        let report = ObjectReferences::analyze(
            &assemble("lea .Lone(%rip),%rdi\ncall puts@PLT\nret", &data),
            "fixture",
        )
        .unwrap();
        assert!(report.literals.is_empty());
        assert!(hint(&report, 0).is_none());
        assert!(
            report.calls[0].integer_argument_registers[0]
                .target
                .is_some()
        );
    }
}

#[test]
fn distinct_calls_keep_their_own_literals_and_tail_call_kind() {
    let scratch = native::Scratch::new();
    for opt in ["-O0", "-O2"] {
        let obj = scratch.0.join(format!("two{opt}.o"));
        native::object(
            &native::fixture_root().join("references/two-calls.c"),
            &obj,
            opt,
            "fixture",
        );
        let report = ObjectReferences::analyze(&std::fs::read(obj).unwrap(), "fixture").unwrap();
        assert_eq!(report.calls.len(), 2);
        assert_eq!(hint(&report, 0).as_deref(), Some("puts(\"first\")"));
        assert_eq!(hint(&report, 1).as_deref(), Some("puts(\"second\")"));
        assert!(!report.calls[0].tail);
        assert_eq!(report.calls[1].tail, opt == "-O2");
    }
}

#[test]
fn c_literal_spelling_round_trips_all_nonzero_byte_values_with_strict_c11() {
    let scratch = native::Scratch::new();
    let bytes: Vec<_> = (1..=255).collect();
    let literal = Literal {
        section: 1,
        section_name: None,
        offset: 0,
        bytes: bytes.clone(),
    };
    let source = scratch.0.join("literal.c");
    let object = source.with_extension("o");
    let bin = source.with_extension("bin");
    std::fs::write(&source,format!("#include <stdio.h>\nstatic const unsigned char value[]={};\nint main(void){{return fwrite(value,1,sizeof(value)-1,stdout)==sizeof(value)-1?0:1;}}\n",literal.c_literal())).unwrap();
    native::object(&source, &object, "-O2", "fixture");
    native::link(&[&object], &bin);
    let output = Command::new(bin).output().unwrap();
    assert!(output.status.success());
    assert_eq!(output.stdout, bytes);
    let trigraph = Literal {
        bytes: b"??/??=\"\\\n\r\t\xff9".to_vec(),
        ..literal
    };
    assert!(trigraph.c_literal().contains("\\?\\?/"));
}

fn u64_at(b: &[u8], o: usize) -> u64 {
    u64::from_le_bytes(b[o..o + 8].try_into().unwrap())
}
fn put64(b: &mut [u8], o: usize, n: u64) {
    b[o..o + 8].copy_from_slice(&n.to_le_bytes());
}
fn rela(b: &[u8]) -> (usize, usize) {
    let sh = u64_at(b, 40) as usize;
    let count = u16::from_le_bytes(b[60..62].try_into().unwrap()) as usize;
    for h in (sh..sh + count * 64).step_by(64) {
        if u32::from_le_bytes(b[h + 4..h + 8].try_into().unwrap()) == 4 && u64_at(b, h + 32) > 0 {
            return (h, u64_at(b, h + 24) as usize);
        }
    }
    panic!("missing RELA")
}

#[test]
fn relocation_bias_and_field_identity_are_checked_before_naming_a_call() {
    let original = assemble("lea .Lone(%rip),%rdi\ncall puts@PLT\nnop\nret", strings());
    let (_, table) = rela(&original);
    let mut changed = original.clone();
    put64(&mut changed, table + 24 + 16, (-3i64) as u64);
    let report = ObjectReferences::analyze(&changed, "fixture").unwrap();
    assert!(hint(&report, 0).is_none());
    assert!(matches!(
        report.calls[0].target,
        Some(Target::External { addend: 1, .. })
    ));
    let mut changed = original.clone();
    let field = u64_at(&changed, table);
    put64(&mut changed, table, field + 1);
    let report = ObjectReferences::analyze(&changed, "fixture").unwrap();
    assert!(hint(&report, 0).is_none());
    let mut changed = original;
    let info = u64_at(&changed, table + 8);
    put64(&mut changed, table + 8, (info & !0xffff_ffff) | 4);
    let report = ObjectReferences::analyze(&changed, "fixture").unwrap();
    assert!(hint(&report, 0).is_none());
}

#[test]
fn implicit_rel_addends_and_unknown_widths_are_conservative() {
    let original = assemble("call puts@PLT\nret", strings());
    let (header, table) = rela(&original);
    let mut changed = original.clone();
    changed[header + 4..header + 8].copy_from_slice(&9u32.to_le_bytes());
    put64(&mut changed, header + 32, 16);
    put64(&mut changed, header + 56, 16);
    let report = ObjectReferences::analyze(&changed, "fixture").unwrap();
    assert!(report.calls[0].target.is_none());
    assert_eq!(report.references[0].relocation.addend, None);
    let mut changed = original;
    let info = u64_at(&changed, table + 8);
    put64(&mut changed, table + 8, (info & !0xffff_ffff) | 0xffff);
    assert!(ObjectReferences::analyze(&changed, "fixture").is_err());
}

#[test]
fn unreachable_relocations_do_not_produce_reachable_call_facts() {
    let report = analyze("ret\nlea .Lone(%rip),%rdi\ncall puts@PLT\nret");
    assert_eq!(report.references.len(), 2);
    assert!(report.calls.is_empty());
    assert!(report.literals.is_empty());
}

#[test]
fn malformed_objects_and_single_byte_mutations_are_panic_free() {
    let original = assemble("lea .Lone(%rip),%rdi\ncall puts@PLT\nret", strings());
    for n in 0..original.len() {
        assert!(ObjectReferences::analyze(&original[..n], "fixture").is_err());
    }
    for n in 0..original.len() {
        for value in [0, 255] {
            let mut data = original.clone();
            data[n] = value;
            let _ = ObjectReferences::analyze(&data, "fixture");
        }
    }
}

#[test]
fn opcode_and_real_field_width_prevent_prefix_and_opcode_relocation_forgery() {
    let object = assemble(
        ".byte 0x66,0x66,0x66,0xeb,0\n.reloc fixture+1,R_X86_64_PC32,puts-4\nret",
        strings(),
    );
    assert!(ObjectReferences::analyze(&object, "fixture").is_err());
    let object = assemble(
        ".byte 0x66,0x66,0x66,0x48,0xc7,0xc7,0,0,0,0\n.reloc fixture+2,R_X86_64_64,.Lone\ncall puts@PLT\nret",
        strings(),
    );
    let report = ObjectReferences::analyze(&object, "fixture").unwrap();
    assert!(hint(&report, 0).is_none());
    assert!(report.references.iter().any(|r| r.usage.is_none()));
}

#[test]
fn got_slot_addends_are_distinct_from_offsets_into_the_callee() {
    let object = assemble("call *puts@GOTPCREL+8(%rip)\nret", strings());
    let report = ObjectReferences::analyze(&object, "fixture").unwrap();
    assert!(report.calls[0].target.is_none());
    assert!(report.references[0].usage.is_none());
}

#[test]
fn failed_literal_scans_and_repeated_symbol_output_obey_work_budget() {
    let object = assemble(
        ".set n,0\n.rept 2100\nlea .Lbytes+n(%rip),%rdi\n.set n,n+1\n.endr\nret",
        ".section .rodata,\"a\",@progbits\n.Lbytes:.fill 6200,1,65",
    );
    assert!(matches!(
        ObjectReferences::analyze(&object, "fixture"),
        Err(nirvana::object_refs::ReferenceError::Limit(_))
    ));
    let name = "long".repeat(256);
    let object = assemble(
        &format!("movabs ${name},%rbx\n.rept 10000\ncall *%rbx\n.endr\nret"),
        strings(),
    );
    assert!(matches!(
        ObjectReferences::analyze(&object, "fixture"),
        Err(nirvana::object_refs::ReferenceError::Limit(_))
    ));
}

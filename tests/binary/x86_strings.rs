//! String stores keep partial progress, flags and the original instruction PC.
use crate::support::module_fixture;
use crate::support::native;
use module_fixture::{
    Case, check_generated_with_state, compile, expected_with_state, state_address,
};
use nirvana::{
    ir::Width,
    linked_elf::LinkedOptions,
    module_ir::{self, Status},
    x86::{self, StringOperation},
};
use std::{process::Command, time::Duration};

#[test]
fn canonical_stores_direction_and_rejected_prefixes_are_explicit() {
    for (bytes, width, repeat) in [
        (&[0xaa][..], Width::U8, false),
        (&[0xab][..], Width::U32, false),
        (&[0x66, 0xab][..], Width::U16, false),
        (&[0x48, 0xab][..], Width::U64, false),
        (&[0xf3, 0xaa][..], Width::U8, true),
        (&[0xf3, 0x66, 0xab][..], Width::U16, true),
        (&[0x66, 0xf3, 0xab][..], Width::U16, true),
        (&[0xf3, 0xab][..], Width::U32, true),
        (&[0xf3, 0x48, 0xab][..], Width::U64, true),
    ] {
        let i = x86::decode_string_at(bytes, 0x1000).unwrap();
        assert_eq!(i.size as usize, bytes.len());
        assert_eq!(i.operation, StringOperation::Store { width, repeat });
        assert!(x86::decode_at(bytes, 0x1000).is_err());
    }
    assert_eq!(
        x86::decode_string_at(&[0xfc], 0).unwrap().operation,
        StringOperation::Direction(false)
    );
    assert_eq!(
        x86::decode_string_at(&[0xfd], 0).unwrap().operation,
        StringOperation::Direction(true)
    );
    for bytes in [
        &[][..],
        &[0xf3],
        &[0xf3, 0x48],
        &[0x67, 0xf3, 0xab],
        &[0xf2, 0xab],
        &[0xf0, 0xab],
        &[0xf3, 0xf3, 0xab],
        &[0x48, 0xf3, 0xab],
        &[0xf2, 0xa4],
    ] {
        assert!(x86::decode_string_at(bytes, 0).is_err());
    }
    assert!(x86::decode_string_at(&[0xaa], u64::MAX).is_err());
}

#[test]
fn repeated_stores_preserve_prefix_faults_budgets_and_all_checked_state() {
    let scratch = native::Scratch::new();
    for (name, code, width, repeat) in [
        ("qword", "rep stosq", 8, true),
        ("byte", "std\nstosb\ncld", 1, false),
        (
            "loop",
            "mov %rcx,%r9\ntest %r9,%r9\njz .Ldone\n.Lmore:\nmov $1,%ecx\nrep stosq\nsub $1,%r9\njnz .Lmore\n.Ldone:",
            8,
            true,
        ),
    ] {
        let dir = scratch.0.join(name);
        std::fs::create_dir(&dir).unwrap();
        let source = dir.join("source.S");
        let binary = dir.join("source");
        std::fs::write(
            &source,
            format!(
                r#"
.text
.globl fixture
.type fixture,@function
fixture:
    mov %rdi,%r8
    mov (%r8),%rcx
    mov 8(%r8),%rdi
    mov 16(%r8),%rax
    {code}
    mov %rcx,(%r8)
    mov %rdi,8(%r8)
    ret
.size fixture,.-fixture
.globl main
.type main,@function
main: xor %eax,%eax
ret
.size main,.-main
.section .note.GNU-stack,"",@progbits
"#
            ),
        )
        .unwrap();
        compile(
            Command::new("cc")
                .args(["-fno-pie", "-no-pie"])
                .arg(&source)
                .arg("-o")
                .arg(&binary),
        );
        let module = module_ir::lift_elf(
            &std::fs::read(binary).unwrap(),
            "fixture",
            LinkedOptions {
                load_bias: 0,
                stack_size: 4096,
            },
        )
        .unwrap();
        assert!(
            module
                .program
                .instructions()
                .iter()
                .any(|i| matches!(i, module_ir::Instruction::StoreString { .. }))
        );
        let values = nirvana::module_values::analyze(&module.program).unwrap();
        let function = values
            .functions
            .iter()
            .find(|f| f.function.address == module.program.entry())
            .unwrap()
            .result
            .as_ref()
            .unwrap();
        let boundary = function
            .boundaries()
            .iter()
            .find(|b| {
                matches!(
                    b.kind,
                    nirvana::module_values::BoundaryKind::StoreString { .. }
                )
            })
            .unwrap();
        assert_eq!(boundary.inputs.len(), if repeat { 4 } else { 3 });
        assert_eq!(
            boundary
                .outputs
                .iter()
                .map(|v| v.register.0)
                .collect::<Vec<_>>(),
            if repeat {
                vec![x86::RDI, x86::RCX]
            } else {
                vec![x86::RDI]
            }
        );
        for &register in if name == "byte" {
            &[x86::RAX][..]
        } else {
            &[x86::RAX, x86::DF][..]
        } {
            assert_eq!(
                boundary
                    .inputs
                    .iter()
                    .find(|v| v.register.0 == register)
                    .unwrap()
                    .value,
                boundary
                    .preserved
                    .iter()
                    .find(|v| v.register.0 == register)
                    .unwrap()
                    .value
            );
        }
        let output = nirvana::module_readable::emit_c_with_locals(&module).unwrap();
        assert_eq!(
            output.report.local_fallback_functions,
            0,
            "{}",
            output
                .code
                .lines()
                .filter(|s| s.contains("fallback"))
                .collect::<Vec<_>>()
                .join("\n")
        );
        let mut registers = module.initial_registers();
        for (i, v) in registers.iter_mut().enumerate() {
            if i != x86::RSP {
                *v = if (16..=21).contains(&i) {
                    (i & 1) as u64
                } else {
                    0x123456789abcdef0_u64.wrapping_mul(i as u64 + 1)
                };
            }
        }
        let end = module.image.memory_base + module.image.memory.len() as u64;
        for backwards in [0, 1] {
            registers[x86::DF] = backwards;
            let mut cases = Vec::new();
            let mut rows = Vec::new();
            for count in [0, 1, 2, 3, u64::MAX] {
                for target in [
                    state_address(&module) + 64,
                    end - 2 * width,
                    module.image.memory_base + width,
                    u64::MAX,
                ] {
                    let case = Case {
                        input: [count, target, 0x0123456789abcdef, 19],
                        pc: module.program.entry(),
                        budget: 100,
                        patch: None,
                    };
                    let (row, status) = expected_with_state(&module, &case, Some(&registers));
                    if repeat && count == 0 {
                        assert!(matches!(status, Status::Returned(_)));
                        assert_eq!(row[1], 0);
                        assert_eq!(row[2], target);
                    }
                    if repeat && count == 3 && target == end - 16 && backwards == 0 {
                        assert!(matches!(status,Status::Fault(f)if f.address==end));
                        assert_eq!(row[1], 3);
                        assert_eq!(row[14], 1);
                        assert_eq!(row[20], end);
                    }
                    rows.push(row);
                    cases.push(case);
                }
            }
            for instruction in module.program.instructions() {
                for budget in [0, 1, 2, 8, 64] {
                    let case = Case {
                        input: [2, state_address(&module) + 64, 37, 19],
                        pc: instruction.address(),
                        budget,
                        patch: None,
                    };
                    rows.push(expected_with_state(&module, &case, Some(&registers)).0);
                    cases.push(case);
                }
            }
            let nested = dir.join(format!("df-{backwards}"));
            std::fs::create_dir(&nested).unwrap();
            check_generated_with_state(
                &module,
                &cases,
                &rows,
                &nested,
                true,
                &[1, 64],
                Some(&registers),
            );
        }
    }
}

#[test]
fn native_stos_widths_direction_flags_and_page_fault_progress() {
    let scratch = native::Scratch::new();
    let source = scratch.0.join("native.c");
    std::fs::write(&source, include_str!("../fixtures/stos-native.c")).unwrap();
    for opt in ["-O0", "-O2"] {
        let binary = scratch.0.join(opt);
        native::compile_c(&source, &binary, &[opt, "-mno-red-zone"]);
        let result = native::run_output(&binary, Some(""), Duration::from_secs(5));
        assert!(
            result.status.success(),
            "{opt}: {}",
            String::from_utf8_lossy(&result.stderr)
        );
    }
}

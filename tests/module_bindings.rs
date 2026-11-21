#[path = "support/module_fixture.rs"]
#[allow(dead_code)]
mod module_fixture;
#[path = "support/native.rs"]
#[allow(dead_code)]
mod native;

use module_fixture::{Case, check_generated_with_state, compile, expected_with_state};
use nirvana::{
    linked_elf::LinkedOptions,
    module_ir::{self, Status},
    x86,
};
use std::process::Command;

fn lift(path: &std::path::Path, pie: bool) -> module_ir::Module {
    module_ir::lift_elf(
        &std::fs::read(path).unwrap(),
        "fixture",
        LinkedOptions {
            load_bias: if pie { 0x230000 } else { 0 },
            stack_size: 4096,
        },
    )
    .unwrap()
}

#[test]
fn stream_aliases_and_tls_guard_changes_match_all_checked_backends() {
    let scratch = native::Scratch::new();
    for pie in [false, true] {
        for operation in ["xor", "sub"] {
            let directory = scratch.0.join(format!("{pie}-{operation}"));
            std::fs::create_dir(&directory).unwrap();
            let source = directory.join("source.S");
            let binary = directory.join("source");
            std::fs::write(
                &source,
                format!(
                    r#"
.text
.globl fixture
.type fixture,@function
fixture:
    push %rbx
    sub $16,%rsp
    mov %fs:0x28,%rax
    mov %rax,8(%rsp)
    mov stdin(%rip),%r10
    mov stderr(%rip),%r11
    mov stdout@GOTPCREL(%rip),%rcx
    mov 0(%rdi),%r8
    mov %r8,(%rcx)
    mov stdout(%rip),%rax
    mov %rax,8(%rdi)
    mov 24(%rdi),%rsi
    test %rsi,%rsi
    jz .Lkeep
    mov %r8,(%rsi)
.Lkeep:
    mov 16(%rdi),%rdx
    xor %rdx,8(%rsp)
    mov 8(%rsp),%rax
    {operation} %fs:0x28,%rax
    jne .Lbad
    mov $1,%eax
    jmp .Lend
.Lbad:
    mov $0,%eax
.Lend:
    add $16,%rsp
    pop %rbx
    ret
.size fixture,.-fixture
.globl main
.type main,@function
main:
    ret
.size main,.-main
.section .note.GNU-stack,"",@progbits
"#
                ),
            )
            .unwrap();
            compile(
                Command::new("cc")
                    .arg("-Wl,--no-relax")
                    .args(if pie {
                        ["-fPIE", "-pie"]
                    } else {
                        ["-fno-pie", "-no-pie"]
                    })
                    .arg(&source)
                    .arg("-o")
                    .arg(&binary),
            );
            let module = lift(&binary, pie);
            assert_eq!(module.image.external_data.len(), 3);
            let tls = module.image.thread_local.as_ref().unwrap();
            let guard = tls.base + x86::FS_GUARD_OFFSET;
            let offset = (guard - module.image.memory_base) as usize;
            let original_guard =
                u64::from_le_bytes(module.image.memory[offset..offset + 8].try_into().unwrap());
            let mut registers = module.initial_registers();
            for (r, value) in registers.iter_mut().enumerate() {
                if r != x86::RSP {
                    *value = if (16..=20).contains(&r) {
                        (r & 1) as u64
                    } else {
                        0x7193_a5b7_c9db_e0f2_u64.wrapping_mul(r as u64 + 1)
                    };
                }
            }
            let mut cases = Vec::new();
            let mut rows = Vec::new();
            for value in [0, 1, original_guard, u64::MAX] {
                for flip in [0, 1, u64::MAX] {
                    for pointer in [0, guard, module.image.memory_base.wrapping_sub(8)] {
                        let case = Case {
                            input: [value, 19, flip, pointer],
                            pc: module.program.entry(),
                            budget: 200,
                            patch: None,
                        };
                        let (row, status) = expected_with_state(&module, &case, Some(&registers));
                        if pointer == 0 || pointer == guard {
                            assert!(matches!(status, Status::Returned(_)));
                            let compared_guard = if pointer == guard {
                                value
                            } else {
                                original_guard
                            };
                            assert_eq!(row[0], u64::from(original_guard ^ flip == compared_guard));
                            assert_eq!(row[2], value, "GOT store must reach direct COPY load");
                        } else {
                            assert!(matches!(status, Status::Fault(_)));
                        }
                        rows.push(row);
                        cases.push(case);
                    }
                }
            }
            for instruction in module.program.instructions() {
                for budget in [0, 1, 2, 8, 64] {
                    let case = Case {
                        input: [13, 19, 1, guard],
                        pc: instruction.address(),
                        budget,
                        patch: None,
                    };
                    rows.push(expected_with_state(&module, &case, Some(&registers)).0);
                    cases.push(case);
                }
            }
            let output = nirvana::module_readable::emit_c_with_locals(&module).unwrap();
            assert_eq!(output.report.local_fallback_functions, 0);
            check_generated_with_state(
                &module,
                &cases,
                &rows,
                &directory,
                true,
                &[64],
                Some(&registers),
            );
        }
    }
}

#[test]
fn compiler_stack_protection_at_o0_and_o2_preserves_native_results_and_resumption() {
    let scratch = native::Scratch::new();
    for pie in [false, true] {
        for opt in ["-O0", "-O2"] {
            let directory = scratch.0.join(format!("compiler-{pie}-{opt}"));
            std::fs::create_dir(&directory).unwrap();
            let binary = directory.join("source");
            compile(
                Command::new("cc")
                    .args(["-std=c11", "-fstack-protector-all", opt])
                    .args(if pie {
                        ["-fPIE", "-pie"]
                    } else {
                        ["-fno-pie", "-no-pie"]
                    })
                    .arg(native::fixture_root().join("stack-guard.c"))
                    .arg(native::fixture_root().join("harness.c"))
                    .arg("-o")
                    .arg(&binary),
            );
            let module = lift(&binary, pie);
            let inputs = [0, 1, 127, 255, 256, 0x8000_0000, 1u64 << 63, u64::MAX];
            let text: String = inputs.iter().map(|v| format!("{v} 17 19 23\n")).collect();
            let native_rows = native::run(&binary, &text);
            let mut cases = Vec::new();
            let mut rows = Vec::new();
            for (&value, original) in inputs.iter().zip(native_rows) {
                let case = Case {
                    input: [value, 17, 19, 23],
                    pc: module.program.entry(),
                    budget: 1000,
                    patch: None,
                };
                let (row, status) = expected_with_state(&module, &case, None);
                assert!(matches!(status, Status::Returned(_)));
                assert_eq!(&row[..5], original);
                rows.push(row);
                cases.push(case);
            }
            let tls = module.image.thread_local.as_ref().unwrap();
            for cookie in [0, 1, u64::MAX] {
                let case = Case {
                    input: [123, 17, 19, 23],
                    pc: module.program.entry(),
                    budget: 1000,
                    patch: Some((tls.base + x86::FS_GUARD_OFFSET, cookie, 8)),
                };
                let (row, status) = expected_with_state(&module, &case, None);
                assert!(matches!(status, Status::Returned(126)));
                rows.push(row);
                cases.push(case);
            }
            for instruction in module.program.instructions() {
                for budget in [0, 1, 7] {
                    let case = Case {
                        input: [123, 17, 19, 23],
                        pc: instruction.address(),
                        budget,
                        patch: None,
                    };
                    let status = expected_with_state(&module, &case, None);
                    // Resuming directly at an import CALL can exhaust its
                    // separate import budget; the shared oracle records that.
                    rows.push(status.0);
                    cases.push(case);
                }
            }
            check_generated_with_state(&module, &cases, &rows, &directory, true, &[1, 2, 64], None);
        }
    }
}

#[test]
fn final_call_keeps_its_real_return_pc_for_known_and_unknown_continuations() {
    let scratch = native::Scratch::new();
    for gap in [false, true] {
        let directory = scratch.0.join(format!("final-call-{gap}"));
        std::fs::create_dir(&directory).unwrap();
        let source = directory.join("source.S");
        let binary = directory.join("source");
        std::fs::write(
            &source,
            format!(
                r#"
.text
.globl fixture
.type fixture,@function
fixture:
    call leaf
.size fixture,.-fixture
{}
.type leaf,@function
leaf:
    addq $1,0(%rdi)
    mov 0(%rdi),%rax
    ret
.size leaf,.-leaf
.section .note.GNU-stack,"",@progbits
"#,
                if gap { ".byte 0xcc" } else { "" }
            ),
        )
        .unwrap();
        compile(
            Command::new("cc")
                .arg("-no-pie")
                .arg(&source)
                .arg(native::fixture_root().join("harness.c"))
                .arg("-o")
                .arg(&binary),
        );
        let module = lift(&binary, false);
        let entry = module
            .program
            .functions()
            .iter()
            .find(|f| f.name == "fixture")
            .unwrap();
        let next = entry.address + entry.size;
        let mut cases = Vec::new();
        let mut rows = Vec::new();
        let case = Case {
            input: [5, 17, 19, 23],
            pc: module.program.entry(),
            budget: 200,
            patch: None,
        };
        let (row, status) = expected_with_state(&module, &case, None);
        if gap {
            assert_eq!(status, Status::UnknownTarget(next));
            assert_eq!(row[0], 6);
        } else {
            assert_eq!(status, Status::Returned(7));
            assert_eq!(native::run(&binary, "5 17 19 23\n")[0], row[..5]);
        }
        rows.push(row);
        cases.push(case);
        for instruction in module.program.instructions() {
            for budget in [0, 1, 2, 7] {
                let case = Case {
                    input: [5, 17, 19, 23],
                    pc: instruction.address(),
                    budget,
                    patch: None,
                };
                rows.push(expected_with_state(&module, &case, None).0);
                cases.push(case);
            }
        }
        check_generated_with_state(&module, &cases, &rows, &directory, true, &[1, 2, 64], None);
    }
}

#[test]
fn puts_observes_stdout_alias_changes_and_declines_unknown_stream_handles() {
    let scratch = native::Scratch::new();
    for pie in [false, true] {
        for route in ["stdout", "stderr", "unknown"] {
            let directory = scratch.0.join(format!("puts-{pie}-{route}"));
            std::fs::create_dir(&directory).unwrap();
            let source = directory.join("source.S");
            let binary = directory.join("original");
            let value = match route {
                "stdout" => "mov stdout(%rip),%rax",
                "stderr" => "mov stderr(%rip),%rax",
                _ => "xor %eax,%eax",
            };
            std::fs::write(
                &source,
                format!(
                    r#"
.text
.globl main
.type main,@function
main:
    sub $8,%rsp
    mov stderr(%rip),%r10
    {value}
    mov stdout@GOTPCREL(%rip),%rcx
    mov %rax,(%rcx)
    lea msg(%rip),%rdi
    call puts@PLT
    add $8,%rsp
    ret
.size main,.-main
.section .rodata
msg: .asciz "stream-effect"
.section .note.GNU-stack,"",@progbits
"#
                ),
            )
            .unwrap();
            compile(
                Command::new("cc")
                    .arg("-Wl,--no-relax")
                    .args(if pie {
                        ["-fPIE", "-pie"]
                    } else {
                        ["-fno-pie", "-no-pie"]
                    })
                    .arg(&source)
                    .arg("-o")
                    .arg(&binary),
            );
            let module = module_ir::lift_elf(
                &std::fs::read(&binary).unwrap(),
                "main",
                LinkedOptions {
                    load_bias: if pie { 0x230000 } else { 0 },
                    stack_size: 4096,
                },
            )
            .unwrap();
            let original = if route == "unknown" {
                None
            } else {
                Some(Command::new(&binary).output().unwrap())
            };
            for (name, code) in [
                ("flat", nirvana::module_emit::emit_c(&module).unwrap()),
                (
                    "readable",
                    nirvana::module_readable::emit_c(&module).unwrap().code,
                ),
                (
                    "locals",
                    nirvana::module_readable::emit_c_with_locals(&module)
                        .unwrap()
                        .code,
                ),
            ] {
                let source = directory.join(format!("{name}.c"));
                std::fs::write(&source, code).unwrap();
                for opt in ["-O0", "-O2"] {
                    let executable = directory.join(format!("{name}-{opt}"));
                    compile(
                        Command::new("cc")
                            .args([
                                "-std=c11",
                                "-Wall",
                                "-Wextra",
                                "-Werror",
                                "-pedantic",
                                "-fsanitize=undefined",
                                "-fno-sanitize-recover=all",
                                opt,
                            ])
                            .arg(&source)
                            .arg("-o")
                            .arg(&executable),
                    );
                    let actual = Command::new(executable).output().unwrap();
                    if let Some(expected) = &original {
                        assert_eq!(actual.status.code(), expected.status.code());
                        assert_eq!(actual.stdout, expected.stdout);
                        assert_eq!(actual.stderr, expected.stderr);
                        assert_eq!(actual.status.code(), Some(14));
                    } else {
                        assert_eq!(actual.status.code(), Some(3));
                        assert!(actual.stdout.is_empty());
                        assert!(String::from_utf8_lossy(&actual.stderr).contains("status=3"));
                        assert!(!String::from_utf8_lossy(&actual.stderr).contains("stream-effect"));
                    }
                }
            }
        }
    }
}

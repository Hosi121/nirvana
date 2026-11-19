//! Machine-code fixtures exercise module control flow and checked C state.
//! Assembly here is only compiler input; the emitter receives decoded ELF.
#[path = "support/native.rs"]
#[allow(dead_code)]
mod native;

use nirvana::linked_elf::LinkedOptions;
use nirvana::module_ir::{self, Instruction, Module, Target};
use std::path::Path;
use std::process::Command;

fn module(scratch: &native::Scratch, assembly: &str) -> Module {
    let source = scratch.0.join("module.S");
    let executable = scratch.0.join("original");
    std::fs::write(
        &source,
        format!("{assembly}\n.section .note.GNU-stack,\"\",@progbits\n"),
    )
    .unwrap();
    let output = Command::new("cc")
        .args(["-no-pie", "-Wl,--build-id=none"])
        .arg(&source)
        .arg("-o")
        .arg(&executable)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    module_ir::lift_elf(
        &std::fs::read(executable).unwrap(),
        "main",
        LinkedOptions {
            load_bias: 0,
            ..LinkedOptions::default()
        },
    )
    .unwrap()
}

fn compile(scratch: &native::Scratch, code: &str, optimization: &str) -> std::path::PathBuf {
    let source = scratch.0.join("generated.c");
    let executable = scratch.0.join(format!("generated{}", optimization));
    std::fs::write(&source, code).unwrap();
    let output = Command::new("cc")
        .args([
            "-std=c11",
            "-Wall",
            "-Wextra",
            "-Werror",
            "-pedantic",
            optimization,
        ])
        .arg(&source)
        .arg("-o")
        .arg(&executable)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    executable
}

fn run(executable: &Path) -> std::process::Output {
    Command::new(executable).output().unwrap()
}

fn harness(code: &str, body: &str) -> String {
    format!(
        "#define main nv_standalone_main\n{code}\n#undef main\n#include <assert.h>\nint main(void) {{\n{body}\nreturn 0;\n}}\n"
    )
}

fn for_optimizations(scratch: &native::Scratch, code: &str) {
    for optimization in ["-O0", "-O2"] {
        let executable = compile(scratch, code, optimization);
        let output = run(&executable);
        assert!(
            output.status.success(),
            "{optimization}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
    }
}

#[test]
fn standalone_internal_recursion_indirect_tail_and_modified_return_slot() {
    let scratch = native::Scratch::new();
    let module = module(
        &scratch,
        r#"
.text
.globl main
.type main,@function
main:
    mov $5,%edi
    call factorial
    cmp $120,%eax
    jne bad
    lea tail(%rip),%rax
    call *%rax
    cmp $17,%eax
    jne bad
    call altered
    mov $99,%eax
    ret
bad:
    mov $98,%eax
    ret
.size main,.-main
.type factorial,@function
factorial:
    cmp $1,%edi
    jbe base
    push %rdi
    sub $1,%edi
    call factorial
    pop %rdi
    imul %edi,%eax
    ret
base:
    mov $1,%eax
    ret
.size factorial,.-factorial
.type tail,@function
tail:
    jmp leaf
.size tail,.-tail
.type leaf,@function
leaf:
    mov $17,%eax
    ret
.size leaf,.-leaf
.type altered,@function
altered:
    lea answer(%rip),%rax
    mov %rax,(%rsp)
    ret
.size altered,.-altered
.type answer,@function
answer:
    mov $42,%eax
    ret
.size answer,.-answer
"#,
    );
    assert_eq!(run(&scratch.0.join("original")).status.code(), Some(42));
    let code = nirvana::module_emit::emit_c(&module).unwrap();
    assert!(code.starts_with("#define _POSIX_C_SOURCE 200809L\n"));
    assert_eq!(code.matches("static unsigned nv_run(").count(), 1);
    for optimization in ["-O0", "-O2"] {
        let executable = compile(&scratch, &code, optimization);
        let output = run(&executable);
        assert_eq!(
            output.status.code(),
            Some(42),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert!(output.stderr.is_empty());
    }
}

#[test]
fn instruction_budget_precedes_effects_and_ret_uses_checked_slot() {
    let scratch = native::Scratch::new();
    let module = module(
        &scratch,
        ".text\n.globl main\n.type main,@function\nmain: mov $19,%eax\nret\n.size main,.-main",
    );
    let code = nirvana::module_emit::emit_c(&module).unwrap();
    let ret_address = module
        .program
        .instructions()
        .iter()
        .find_map(|instruction| match instruction {
            Instruction::Return { address, .. } => Some(*address),
            _ => None,
        })
        .unwrap();
    for_optimizations(
        &scratch,
        &harness(
            &code,
            &format!(
                r#"
    struct nv_module *s=nv_create(); assert(s);
    s->r[0]=77; s->instructions_left=0;
    assert(nv_run(s)==4 && s->started==0 && s->r[0]==77);
    s->status=0; s->instructions_left=1; s->pc=UINT64_C({ret_address});
    s->r[4]=s->base+s->size-4;
    uint64_t original_sp=s->r[4];
    assert(nv_run(s)==1 && s->started==1 && s->r[4]==original_sp);
    assert(s->fault_address==original_sp && s->fault_width==8 && s->fault_access==1);
    /* Empty host ranges permit exactly the one-past address. */
    assert(nv_check(s,s->base+s->size,0,1)==s->size);
    free(s->memory); free(s);
"#
            ),
        ),
    );
}

#[test]
fn indirect_call_operand_is_read_before_guest_stack_push() {
    let scratch = native::Scratch::new();
    let module = module(
        &scratch,
        ".text\n.globl main\n.type main,@function\nmain: call *(%rsp)\nret\n.size main,.-main",
    );
    let code = nirvana::module_emit::emit_c(&module).unwrap();
    for_optimizations(
        &scratch,
        &harness(
            &code,
            r#"
    struct nv_module *s=nv_create(); assert(s);
    uint64_t original_sp=s->r[4];
    assert(nv_run(s)==0 && s->started==1 && s->r[4]==original_sp-8);
    assert(s->pc==UINT64_MAX);
    free(s->memory); free(s);
"#,
        ),
    );
}

#[test]
fn plt_slot_is_read_after_push_and_import_budget_precedes_adapter() {
    let scratch = native::Scratch::new();
    let module = module(
        &scratch,
        ".text\n.globl main\n.type main,@function\nmain: call puts@PLT\nret\n.size main,.-main",
    );
    let (slot, link) = module
        .program
        .instructions()
        .iter()
        .find_map(|instruction| match instruction {
            Instruction::Transfer {
                target: Target::Plt(slot),
                link: Some(link),
                ..
            } => Some((*slot, *link)),
            _ => None,
        })
        .unwrap();
    let code = nirvana::module_emit::emit_c(&module).unwrap();
    for_optimizations(
        &scratch,
        &harness(
            &code,
            &format!(
                r#"
    struct nv_module *s=nv_create(); assert(s);
    s->r[4]=UINT64_C({slot})+8; s->instructions_left=1;
    assert(nv_run(s)==4 && s->started==1 && s->pc==UINT64_C({link}));
    assert(s->imports_left==NV_IMPORT_LIMIT);
    free(s->memory); free(s);
    s=nv_create(); assert(s); s->imports_left=0;
    assert(nv_run(s)==5 && s->started==1 && s->imports_left==0);
    free(s->memory); free(s);
"#
            ),
        ),
    );
}

#[test]
fn vector_guards_precede_all_lane_effects_and_instruction_budget_precedes_guard() {
    for (opcode, alignment_fault) in [("movups", false), ("movaps", true)] {
        let scratch = native::Scratch::new();
        let module = module(
            &scratch,
            &format!(
                ".text\n.globl main\n.type main,@function\nmain: {opcode} (%rdi),%xmm0\nret\n.size main,.-main"
            ),
        );
        let code = nirvana::module_emit::emit_c(&module).unwrap();
        let alignment_case = if alignment_fault {
            r#"
    s->status=0; s->instructions_left=1; s->started=0; s->pc=entry;
    s->r[7]=s->base+1;
    assert(nv_run(s)==9 && s->started==1 && s->r[32]==111 && s->r[33]==222);
    assert(s->fault_width==16 && s->fault_access==1);
"#
        } else {
            ""
        };
        for_optimizations(
            &scratch,
            &harness(
                &code,
                &format!(
                    r#"
    struct nv_module *s=nv_create(); assert(s); uint64_t entry=s->pc;
    s->r[32]=111; s->r[33]=222; s->r[7]=s->base+s->size-8;
    assert(nv_run(s)==1 && s->started==1 && s->r[32]==111 && s->r[33]==222);
    assert(s->fault_width==16 && s->fault_access==1);
    s->status=0; s->instructions_left=0; s->started=0; s->pc=entry;
    s->fault_width=0;
    assert(nv_run(s)==4 && s->started==0 && s->fault_width==0);
    assert(s->r[32]==111 && s->r[33]==222);
    {alignment_case}
    free(s->memory); free(s);
"#
                ),
            ),
        );
    }
    let scratch = native::Scratch::new();
    let module = module(
        &scratch,
        ".text\n.globl main\n.type main,@function\nmain: movups %xmm0,(%rdi)\nret\n.size main,.-main",
    );
    let code = nirvana::module_emit::emit_c(&module).unwrap();
    for_optimizations(
        &scratch,
        &harness(
            &code,
            r#"
    struct nv_module *s=nv_create(); assert(s);
    s->r[7]=s->base+s->size-8; s->r[32]=111; s->r[33]=222;
    memset(s->memory+s->size-8,0x5a,8);
    assert(nv_run(s)==1 && s->started==1 && s->fault_width==16 && s->fault_access==2);
    for(unsigned i=0;i<8;++i) assert(s->memory[s->size-8+i]==0x5a);
    free(s->memory); free(s);
"#,
        ),
    );
}

#[test]
fn vector_lane_snapshots_match_interpreter_registers_and_complete_memory() {
    let scratch = native::Scratch::new();
    let mut module = module(
        &scratch,
        r#"
.text
.globl main
.type main,@function
main:
    movups (%rdi),%xmm0
    movq %rsi,%xmm1
    punpcklqdq %xmm1,%xmm0
    movups %xmm0,(%rdx)
    ret
.size main,.-main
"#,
    );
    let low = 0x1122334455667788u64;
    let high = 0xaabbccddeeff0011u64;
    module.image.memory[..8].copy_from_slice(&low.to_le_bytes());
    module.image.memory[8..16].copy_from_slice(&0x9999888877776666u64.to_le_bytes());
    let mut registers = module.initial_registers();
    registers[7] = module.image.memory_base;
    registers[6] = high;
    registers[2] = module.image.memory_base + 32;
    let report = module
        .program
        .run(
            &registers,
            module.image.memory_base,
            &module.image.memory,
            module_ir::Limits::default(),
            &mut module_ir::RejectImports,
        )
        .unwrap();
    assert_eq!(report.status, module_ir::Status::Returned(0));
    assert_eq!(report.state.registers[32..36], [low, high, high, 0]);
    assert_eq!(&report.state.memory[32..40], &low.to_le_bytes());
    assert_eq!(&report.state.memory[40..48], &high.to_le_bytes());
    let code = nirvana::module_emit::emit_c(&module).unwrap();
    let code = harness(
        &code,
        &format!(
            r#"
    struct nv_module *s=nv_create(); assert(s);
    s->r[7]=s->base; s->r[6]=UINT64_C({high}); s->r[2]=s->base+32;
    assert(nv_run(s)==0 && s->started==UINT64_C({}));
    assert(fwrite(s->r,sizeof(s->r),1,stdout)==1);
    assert(fwrite(s->memory,(size_t)s->size,1,stdout)==1);
    free(s->memory); free(s);
"#,
            report.state.trace.len()
        ),
    );
    let expected_registers: Vec<_> = report
        .state
        .registers
        .iter()
        .flat_map(|value| value.to_le_bytes())
        .collect();
    for optimization in ["-O0", "-O2"] {
        let output = run(&compile(&scratch, &code, optimization));
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(
            output.stdout.len(),
            expected_registers.len() + report.state.memory.len()
        );
        assert_eq!(
            &output.stdout[..expected_registers.len()],
            expected_registers
        );
        let mismatch = output.stdout[expected_registers.len()..]
            .iter()
            .zip(&report.state.memory)
            .position(|(actual, expected)| actual != expected);
        assert_eq!(
            mismatch, None,
            "C/interpreter memory differ at offset {mismatch:?}"
        );
    }
}

#[test]
fn unusual_function_symbol_cannot_break_emitted_c_comment() {
    let scratch = native::Scratch::new();
    let module = module(
        &scratch,
        r#"
.text
.globl main
.type main,@function
main:
    jmp "function*/??/name"
.size main,.-main
.type "function*/??/name",@function
"function*/??/name":
    xor %eax,%eax
    ret
.size "function*/??/name",.-"function*/??/name"
"#,
    );
    let code = nirvana::module_emit::emit_c(&module).unwrap();
    assert!(!code.contains("function*/??/name"));
    for_optimizations(&scratch, &code);
}

#[test]
fn initial_ram_including_root_slot_and_errno_is_preserved_exactly() {
    let scratch = native::Scratch::new();
    let mut module = module(
        &scratch,
        r#"
.text
.globl main
.type main,@function
main:
    xor %eax,%eax
    ret
.size main,.-main
"#,
    );
    let errno = (module.program.errno_address() - module.image.memory_base) as usize;
    module.image.memory[errno..errno + 4].copy_from_slice(&0x12345678u32.to_le_bytes());
    for valid_return in [true, false] {
        if !valid_return {
            let root = (module.image.stack_pointer - 16 - module.image.memory_base) as usize;
            module.image.memory[root..root + 8].fill(0);
        }
        let report = module
            .program
            .run(
                &module.initial_registers(),
                module.image.memory_base,
                &module.image.memory,
                module_ir::Limits::default(),
                &mut module_ir::RejectImports,
            )
            .unwrap();
        assert_eq!(
            &report.state.memory[errno..errno + 4],
            &0x12345678u32.to_le_bytes()
        );
        assert_eq!(
            report.status,
            if valid_return {
                module_ir::Status::Returned(0)
            } else {
                module_ir::Status::UnknownTarget(0)
            }
        );
        let body = format!(
            r#"
    struct nv_module *s=nv_create();assert(s);
    assert(nv_read(s,s->errno_address,4)==UINT32_C(0x12345678));
    assert(nv_run(s)=={});
    assert(s->pc==UINT64_C({}));
    assert(s->r[4]==UINT64_C({}));
    assert(nv_read(s,s->errno_address,4)==UINT32_C(0x12345678));
    free(s->memory);free(s);
"#,
            if valid_return { 0 } else { 2 },
            report.pc,
            report.state.registers[4]
        );
        for_optimizations(
            &scratch,
            &harness(&nirvana::module_emit::emit_c(&module).unwrap(), &body),
        );
    }
}

#[test]
fn direct_calls_need_original_code_identity_instead_of_synthetic_import_collision() {
    let scratch = native::Scratch::new();
    let module = module(
        &scratch,
        r#"
.text
.globl main
.type main,@function
main:
    call callee
    ret
.size main,.-main
.type callee,@function
callee:
    xor %eax,%eax
    ret
.size callee,.-callee
.type unused_import,@function
unused_import:
    call puts@PLT
    ret
.size unused_import,.-unused_import
"#,
    );
    let mut bytes = std::fs::read(scratch.0.join("original")).unwrap();
    let original = &module.image.function.bytes;
    assert_eq!(original[0], 0xe8);
    let matches: Vec<_> = bytes
        .windows(original.len())
        .enumerate()
        .filter_map(|(i, word)| (word == original).then_some(i))
        .collect();
    assert_eq!(matches.len(), 1);
    let displacement = i32::try_from(
        i128::from(module.image.puts_address) - i128::from(module.image.function.address + 5),
    )
    .unwrap();
    bytes[matches[0] + 1..matches[0] + 5].copy_from_slice(&displacement.to_le_bytes());
    let error = module_ir::lift_elf(
        &bytes,
        "main",
        LinkedOptions {
            load_bias: 0,
            ..Default::default()
        },
    )
    .unwrap_err()
    .to_string();
    assert!(error.contains("unsupported direct target"), "{error}");
}

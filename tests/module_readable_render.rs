//! Renderer contracts: portable C, actual named calls, and original checked state.
#[path = "support/native.rs"]
#[allow(dead_code)]
mod native;

use nirvana::linked_elf::LinkedOptions;
use nirvana::module_ir::{self, Limits, Module, Status};
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
        .arg(source)
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

fn compile(scratch: &native::Scratch, code: &str, opt: &str, depth: u32) -> std::path::PathBuf {
    let source = scratch.0.join("generated.c");
    let binary = scratch.0.join(format!("generated-{opt}-{depth}"));
    std::fs::write(&source, code).unwrap();
    let output = Command::new("cc")
        .args(["-std=c11", "-Wall", "-Wextra", "-Werror", "-pedantic", opt])
        .arg(format!("-DNV_HOST_DEPTH_LIMIT={depth}"))
        .arg(source)
        .arg("-o")
        .arg(&binary)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{opt} depth {depth}: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    binary
}

fn harness(code: &str, body: &str) -> String {
    format!(
        "#define main nv_standalone_main\n{code}\n#undef main\n#include <assert.h>\nint main(void) {{\n{body}\nreturn 0;\n}}\n"
    )
}

fn run(binary: &std::path::Path) -> std::process::Output {
    // The guest instruction budget bounds execution; this also catches an
    // accidental host-only dispatch cycle without leaving a test process alive.
    Command::new("timeout")
        .arg("15s")
        .arg(binary)
        .output()
        .unwrap()
}

fn state_harness(code: &str, module: &Module, budget: usize) -> String {
    let mut body = String::from("    struct nv_module *s=nv_create(); assert(s);\n");
    let mut registers = module.initial_registers();
    for (index, register) in registers.iter_mut().enumerate() {
        if index != 4 {
            *register = 0x83bd_2a01_0000_0000u64 + index as u64;
        }
    }
    for (index, value) in registers.iter().enumerate() {
        body.push_str(&format!("    s->r[{index}]=UINT64_C({value});\n"));
    }
    body.push_str(&format!(
        "    s->instructions_left=UINT64_C({budget}); s->imports_left=7;\n"
    ));
    body.push_str("    unsigned status=nv_run(s);\n    uint64_t metadata[]={status,s->pc,s->started,s->instructions_left,s->imports_left,s->fault_address,s->fault_width,s->fault_access};\n    assert(fwrite(metadata,sizeof(metadata),1,stdout)==1);\n    assert(fwrite(s->r,sizeof(s->r),1,stdout)==1);\n    assert(fwrite(s->memory,(size_t)s->size,1,stdout)==1);\n    free(s->memory); free(s);\n");
    harness(code, &body)
}

fn compare(module: &Module, scratch: &native::Scratch) -> nirvana::module_readable::COutput {
    let output = nirvana::module_readable::emit_c(module).unwrap();
    let mut registers = module.initial_registers();
    for (index, register) in registers.iter_mut().enumerate() {
        if index != 4 {
            *register = 0x83bd_2a01_0000_0000u64 + index as u64;
        }
    }
    let budget = 2000;
    let report = module
        .program
        .run(
            &registers,
            module.image.memory_base,
            &module.image.memory,
            Limits {
                instructions: budget,
                imports: 7,
            },
            &mut module_ir::RejectImports,
        )
        .unwrap();
    let (status, fault, width, access) = match report.status {
        Status::Returned(_) => (0, 0, 0, 0),
        Status::UnknownTarget(_) => (2, 0, 0, 0),
        Status::Suspended(module_ir::Limit::Instructions) => (4, 0, 0, 0),
        Status::Fault(fault) => (
            1,
            fault.address,
            fault.width,
            if fault.access == nirvana::ir::AccessKind::Read {
                1
            } else {
                2
            },
        ),
        ref other => panic!("unexpected interpreter outcome: {other:?}"),
    };
    let metadata = [
        status,
        report.pc,
        report.state.trace.len() as u64,
        (budget - report.state.trace.len()) as u64,
        7 - report.imports as u64,
        fault,
        width,
        access,
    ];
    let mut expected: Vec<u8> = metadata.iter().flat_map(|v| v.to_le_bytes()).collect();
    expected.extend(report.state.registers.iter().flat_map(|v| v.to_le_bytes()));
    expected.extend(&report.state.memory);
    for opt in ["-O0", "-O2"] {
        let flat = state_harness(
            &nirvana::module_emit::emit_c(module).unwrap(),
            module,
            budget,
        );
        let actual = run(&compile(scratch, &flat, opt, 64));
        assert!(
            actual.status.success(),
            "{}",
            String::from_utf8_lossy(&actual.stderr)
        );
        assert_eq!(actual.stdout, expected, "flat C versus Rust at {opt}");
        for depth in [1, 2, 64] {
            let code = state_harness(&output.code, module, budget);
            let actual = run(&compile(scratch, &code, opt, depth));
            assert!(
                actual.status.success(),
                "{opt} depth {depth}: {}",
                String::from_utf8_lossy(&actual.stderr)
            );
            assert_eq!(actual.stdout.len(), expected.len());
            let first = actual
                .stdout
                .iter()
                .zip(&expected)
                .position(|(a, b)| a != b);
            assert_eq!(
                first, None,
                "structured C versus Rust at {opt}, depth {depth}, byte {first:?}"
            );
        }
    }
    output
}

#[test]
fn named_calls_loops_indirect_tails_and_modified_returns_preserve_full_state() {
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
    mov $3,%ecx
again:
    add $2,%eax
    sub $1,%ecx
    jne again
    lea tail(%rip),%rax
    call *%rax
    call altered
    mov $99,%eax
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
    let output = compare(&module, &scratch);
    assert!(output.report.structured_functions >= 6);
    assert!(output.report.direct_calls >= 3);
    assert!(output.report.indirect_calls >= 1);
    assert!(output.code.contains("while (1)"));
    let plan = nirvana::module_outline::recover(&module.program).unwrap();
    let factorial = plan
        .functions
        .iter()
        .find(|f| f.function.name == "factorial")
        .unwrap();
    assert!(
        output
            .code
            .matches(&format!("{}(f);", factorial.c_name))
            .count()
            >= 3
    );
    let dispatch = output
        .code
        .split("static void nv_dispatch(struct nv_frame *f) {")
        .nth(1)
        .unwrap()
        .split("static unsigned nv_run")
        .next()
        .unwrap();
    assert!(!dispatch.contains("switch"));
    assert!(!dispatch.contains("nv_step("));
}

#[test]
fn irreducible_function_uses_one_local_goto_body_and_safe_symbol_names() {
    let scratch = native::Scratch::new();
    let module = module(
        &scratch,
        r#"
.text
.globl main
.type main,@function
main:
    mov $3,%ecx
    test %edi,%edi
    jz right
left:
    add $1,%eax
    jmp join
right:
    add $2,%eax
join:
    sub $1,%ecx
    jz done
    test %eax,%eax
    jnz left
    jmp right
done:
    jmp "function*/??/name"
.size main,.-main
.type "function*/??/name",@function
"function*/??/name":
    xor %eax,%eax
    ret
.size "function*/??/name",.-"function*/??/name"
"#,
    );
    let output = compare(&module, &scratch);
    assert!(output.report.goto_functions >= 1);
    assert!(output.code.contains("goto fallback"));
    assert!(!output.code.contains("function*/??/name"));
    assert!(!output.code.contains("??/"));
}

#[test]
fn depth_yield_has_no_guest_effects_and_new_runs_clear_stale_status() {
    let scratch = native::Scratch::new();
    let module = module(
        &scratch,
        ".text\n.globl main\n.type main,@function\nmain: mov $19,%eax\nret\n.size main,.-main",
    );
    let output = nirvana::module_readable::emit_c(&module).unwrap();
    let plan = nirvana::module_outline::recover(&module.program).unwrap();
    let name = &plan
        .functions
        .iter()
        .find(|f| f.function.address == module.program.entry())
        .unwrap()
        .c_name;
    let code = harness(
        &output.code,
        &format!(
            r#"
    struct nv_module *s=nv_create(); assert(s);
    struct nv_frame frame={{s,NV_HOST_DEPTH_LIMIT,0}};
    uint64_t before_registers[80]; memcpy(before_registers,s->r,sizeof(before_registers));
    uint8_t *before_memory=malloc((size_t)s->size); assert(before_memory);
    memcpy(before_memory,s->memory,(size_t)s->size);
    uint64_t before_pc=s->pc,before_instructions=s->instructions_left,before_imports=s->imports_left;
    {name}(&frame);
    assert(frame.depth==NV_HOST_DEPTH_LIMIT && frame.yielded==1);
    assert(s->pc==before_pc && s->instructions_left==before_instructions && s->imports_left==before_imports);
    assert(s->started==0 && s->status==0);
    assert(memcmp(before_registers,s->r,sizeof(before_registers))==0);
    assert(memcmp(before_memory,s->memory,(size_t)s->size)==0);
    s->status=4; assert(nv_run(s)==0 && s->r[0]==19 && s->started==2);
    free(before_memory); free(s->memory); free(s);
"#
        ),
    );
    for opt in ["-O0", "-O2"] {
        for depth in [1, 2, 64] {
            let actual = run(&compile(&scratch, &code, opt, depth));
            assert!(
                actual.status.success(),
                "{}",
                String::from_utf8_lossy(&actual.stderr)
            );
        }
    }
    for depth in [0, 257] {
        let source = scratch.0.join("invalid-depth.c");
        std::fs::write(&source, &output.code).unwrap();
        let compiled = Command::new("cc")
            .args(["-std=c11", "-c"])
            .arg(format!("-DNV_HOST_DEPTH_LIMIT={depth}"))
            .arg(source)
            .arg("-o")
            .arg(scratch.0.join("invalid-depth.o"))
            .output()
            .unwrap();
        assert!(!compiled.status.success());
        assert!(
            String::from_utf8_lossy(&compiled.stderr)
                .contains("NV_HOST_DEPTH_LIMIT_must_be_between_1_and_256")
        );
    }
}

#[test]
fn plt_import_specialization_keeps_a_runtime_target_guard() {
    let scratch = native::Scratch::new();
    let module = module(
        &scratch,
        r#"
.text
.globl main
.type main,@function
main:
    lea message(%rip),%rdi
    call puts@PLT
    xor %eax,%eax
    ret
.size main,.-main
.section .rodata
message: .asciz "named import"
"#,
    );
    let output = nirvana::module_readable::emit_c(&module).unwrap();
    let plan = nirvana::module_outline::recover(&module.program).unwrap();
    let puts = plan
        .imports
        .iter()
        .find(|i| i.import.name == "puts")
        .unwrap();
    assert!(output.report.import_calls >= 1);
    assert!(output.code.contains(&format!(
        "if(nv_target==UINT64_C({})) {}(f);",
        puts.import.address, puts.c_name
    )));
    for opt in ["-O0", "-O2"] {
        let actual = run(&compile(&scratch, &output.code, opt, 1));
        assert!(
            actual.status.success(),
            "{}",
            String::from_utf8_lossy(&actual.stderr)
        );
        assert_eq!(actual.stdout, b"named import\n");
    }
}

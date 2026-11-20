//! Independent machine-state comparisons. Fixtures are assembled to ELF first;
//! neither backend nor its recovered syntax is used to construct the oracle.
#[path = "support/native.rs"]
#[allow(dead_code)]
mod native;

use nirvana::ir::AccessKind;
use nirvana::linked_elf::LinkedOptions;
use nirvana::module_ir::{
    self, Environment, ExternalContext, Instruction, Limits, Module, Status, Target,
};
use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{Duration, Instant};

fn module(scratch: &native::Scratch, assembly: &str) -> Module {
    let source = scratch.0.join("fixture.S");
    let executable = scratch.0.join("fixture");
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
            stack_size: 4096,
        },
    )
    .unwrap()
}

#[derive(Clone)]
struct Case {
    name: String,
    pc: u64,
    registers: Vec<u64>,
    instructions: usize,
    imports: usize,
    resume_instructions: Option<usize>,
    patches: Vec<(usize, Vec<u8>)>,
}
impl Case {
    fn new(module: &Module, pc: u64, seed: u64, instructions: usize) -> Self {
        let mut registers = (0..80)
            .map(|r| seed.wrapping_mul(0x9e3779b97f4a7c15).rotate_left(r) ^ (r as u64 * 131))
            .collect::<Vec<_>>();
        registers[4] = module.initial_registers()[4];
        // Small counters exercise both sides while bounding nested loops.
        registers[1] = seed % 4;
        registers[2] = seed % 3;
        registers[6] = seed % 5;
        registers[7] = seed % 7;
        Self {
            name: format!("pc={pc:#x}/seed={seed}/budget={instructions}"),
            pc,
            registers,
            instructions,
            imports: 8,
            resume_instructions: None,
            patches: vec![],
        }
    }
    fn patch_u64(&mut self, module: &Module, address: u64, value: u64) {
        let offset = usize::try_from(address - module.image.memory_base).unwrap();
        assert!(offset + 8 <= module.image.memory.len());
        self.patches.push((offset, value.to_le_bytes().to_vec()));
    }
}

fn func_address(module: &Module, name: &str) -> u64 {
    module
        .program
        .functions()
        .iter()
        .find(|f| f.name == name)
        .unwrap_or_else(|| panic!("missing function {name}"))
        .address
}

// Only deterministic adapters used by this fixture. Unsupported imports use
// RejectImports; successful conversion calls share the documented ABI clobber.
struct Deterministic;
impl Environment for Deterministic {
    fn call(&mut self, name: &str, context: &mut ExternalContext<'_>) -> Result<(), Status> {
        let input = context.registers()[7];
        let value = match name {
            "htons" | "ntohs" => u64::from((input as u16).swap_bytes()),
            "htonl" | "ntohl" => u64::from((input as u32).swap_bytes()),
            "__errno_location" => context.errno_address(),
            _ => return module_ir::RejectImports.call(name, context),
        };
        context.return_bits(value);
        Ok(())
    }
}

fn put(output: &mut impl Write, value: u64) {
    output.write_all(&value.to_le_bytes()).unwrap();
}

const HARNESS: &str = r#"
#undef main
#include <assert.h>
static uint64_t test_read(FILE *file) {
    uint64_t value; assert(fread(&value,8,1,file)==1); return value;
}
int main(int argc,char **argv) {
    assert(argc==3);
    FILE *input=fopen(argv[1],"rb"), *output=fopen(argv[2],"wb"); assert(input && output);
    uint64_t count=test_read(input);
    for(uint64_t i=0;i<count;++i) {
        struct nv_module *s=nv_create(); assert(s);
        s->pc=test_read(input); s->instructions_left=test_read(input); s->imports_left=test_read(input);
        uint64_t resume_instructions=test_read(input);
        assert(fread(s->r,sizeof(s->r),1,input)==1);
        uint64_t patches=test_read(input);
        for(uint64_t j=0;j<patches;++j) {
            uint64_t offset=test_read(input), length=test_read(input);
            assert(offset<=s->size && length<=s->size-offset);
            assert(fread(s->memory+offset,(size_t)length,1,input)==1);
        }
        unsigned status=nv_run(s);
        if(resume_instructions!=UINT64_MAX) {
            s->instructions_left=resume_instructions;
            status=nv_run(s);
        }
        uint64_t fields[8]={status,s->pc,s->started,s->instructions_left,s->imports_left,
                            s->fault_address,s->fault_width,s->fault_access};
        assert(fwrite(fields,sizeof(fields),1,output)==1);
        assert(fwrite(s->r,sizeof(s->r),1,output)==1);
        assert(fwrite(s->memory,(size_t)s->size,1,output)==1);
        free(s->memory); free(s);
    }
    assert(fgetc(input)==EOF); assert(fclose(input)==0); assert(fclose(output)==0); return 0;
}
"#;

fn compile(
    scratch: &native::Scratch,
    code: &str,
    name: &str,
    optimization: &str,
    depth: usize,
) -> PathBuf {
    let source = scratch.0.join(format!("{name}.c"));
    let executable = scratch
        .0
        .join(format!("{name}-{}-{depth}", &optimization[1..]));
    // Feature selection must precede the main macro and all system headers.
    std::fs::write(
        &source,
        format!(
            "#define _POSIX_C_SOURCE 200809L\n#define main nv_standalone_main\n{code}\n{HARNESS}"
        ),
    )
    .unwrap();
    let result = Command::new("cc")
        .args([
            "-std=c11",
            "-Wall",
            "-Wextra",
            "-Werror",
            "-pedantic",
            optimization,
        ])
        .arg(format!("-DNV_HOST_DEPTH_LIMIT={depth}"))
        .arg(&source)
        .arg("-o")
        .arg(&executable)
        .output()
        .unwrap();
    assert!(
        result.status.success(),
        "{name}/{optimization}/depth={depth}: {}",
        String::from_utf8_lossy(&result.stderr)
    );
    executable
}

fn execute(binary: &Path, input: &Path, output: &Path) {
    let mut process = Command::new(binary)
        .arg(input)
        .arg(output)
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .unwrap();
    let deadline = Instant::now() + Duration::from_secs(20);
    loop {
        if let Some(status) = process.try_wait().unwrap() {
            let mut stderr = String::new();
            process
                .stderr
                .take()
                .unwrap()
                .read_to_string(&mut stderr)
                .unwrap();
            assert!(status.success(), "{}: {status}: {stderr}", binary.display());
            return;
        }
        if Instant::now() >= deadline {
            process.kill().unwrap();
            process.wait().unwrap();
            panic!("{} exceeded 20 seconds", binary.display());
        }
        std::thread::sleep(Duration::from_millis(5));
    }
}

fn expected(module: &Module, case: &Case) -> Vec<u8> {
    let mut memory = module.image.memory.clone();
    for (offset, bytes) in &case.patches {
        memory[*offset..*offset + bytes.len()].copy_from_slice(bytes);
    }
    let mut report = module
        .program
        .run_from(
            case.pc,
            &case.registers,
            module.image.memory_base,
            &memory,
            Limits {
                instructions: case.instructions,
                imports: case.imports,
            },
            &mut Deterministic,
        )
        .unwrap();
    // nv_run clears status but retains the last fault's metadata in the same
    // allocation. A resumed fault may replace it; a later stop does not.
    let fault_fields = |status: &Status| match status {
        Status::Fault(f) | Status::Alignment(f) => Some([
            f.address,
            f.width,
            if f.access == AccessKind::Read { 1 } else { 2 },
        ]),
        _ => None,
    };
    let mut fault = fault_fields(&report.status).unwrap_or([0; 3]);
    let mut prior_started = 0;
    let mut prior_imports = 0;
    let mut instruction_limit = case.instructions;
    if let Some(budget) = case.resume_instructions {
        prior_started = report.state.trace.len();
        prior_imports = report.imports;
        instruction_limit = budget;
        report = module
            .program
            .run_from(
                report.pc,
                &report.state.registers,
                module.image.memory_base,
                &report.state.memory,
                Limits {
                    instructions: budget,
                    imports: case.imports - prior_imports,
                },
                &mut Deterministic,
            )
            .unwrap();
    }
    if let Some(fields) = fault_fields(&report.status) {
        fault = fields;
    }
    let status = match &report.status {
        Status::Returned(_) => 0,
        Status::Fault(_) | Status::Alignment(_) => {
            if matches!(report.status, Status::Alignment(_)) {
                9
            } else {
                1
            }
        }
        Status::UnknownTarget(_) => 2,
        Status::UnsupportedImport(_) => 3,
        Status::Suspended(module_ir::Limit::Instructions) => 4,
        Status::Suspended(module_ir::Limit::Imports) => 5,
        Status::Environment(message) => panic!("unexpected environment error: {message}"),
    };
    let started = (prior_started + report.state.trace.len()) as u64;
    let mut output = vec![];
    for value in [
        status,
        report.pc,
        started,
        (instruction_limit - report.state.trace.len()) as u64,
        (case.imports - prior_imports - report.imports) as u64,
        fault[0],
        fault[1],
        fault[2],
    ] {
        put(&mut output, value);
    }
    for value in report.state.registers {
        put(&mut output, value);
    }
    output.extend_from_slice(&report.state.memory);
    output
}

fn compare(module: &Module, cases: &[Case], scratch: &native::Scratch) {
    let input = scratch.0.join("states.bin");
    let mut file = std::io::BufWriter::new(std::fs::File::create(&input).unwrap());
    put(&mut file, cases.len() as u64);
    for case in cases {
        for value in [
            case.pc,
            case.instructions as u64,
            case.imports as u64,
            case.resume_instructions
                .map(|n| n as u64)
                .unwrap_or(u64::MAX),
        ] {
            put(&mut file, value);
        }
        for value in &case.registers {
            put(&mut file, *value);
        }
        put(&mut file, case.patches.len() as u64);
        for (offset, bytes) in &case.patches {
            put(&mut file, *offset as u64);
            put(&mut file, bytes.len() as u64);
            file.write_all(bytes).unwrap();
        }
    }
    file.flush().unwrap();
    let stride = 8 * (8 + 80) + module.image.memory.len();
    let expected = cases
        .iter()
        .map(|c| expected(module, c))
        .collect::<Vec<_>>();
    let old = nirvana::module_emit::emit_c(module).unwrap();
    let new = nirvana::module_readable::emit_c(module).unwrap();
    let locals = nirvana::module_readable::emit_c_with_locals(module).unwrap();
    assert!(
        new.report.structured_functions > 0,
        "fixture must exercise structured emission"
    );
    assert!(
        locals.report.local_functions > 0,
        "fixture must exercise local-value emission"
    );
    assert!(
        locals.code.contains("uint64_t v_"),
        "locals output must declare named uint64_t values"
    );
    eprintln!(
        "{} states x 14 variants = {} comparisons, {} instructions, {} structured / {} goto / {} local functions, {} direct / {} indirect / {} import call sites",
        cases.len(),
        cases.len() * 14,
        module.program.instructions().len(),
        new.report.structured_functions,
        new.report.goto_functions,
        locals.report.local_functions,
        new.report.direct_calls,
        new.report.indirect_calls,
        new.report.import_calls
    );
    for optimization in ["-O0", "-O2"] {
        for (name, code, depths) in [
            ("flat", old.as_str(), &[64][..]),
            ("structured", new.code.as_str(), &[1, 2, 64][..]),
            ("locals", locals.code.as_str(), &[1, 2, 64][..]),
        ] {
            for depth in depths {
                let binary = compile(scratch, code, name, optimization, *depth);
                let output = scratch.0.join("result.bin");
                execute(&binary, &input, &output);
                let mut file = std::io::BufReader::new(std::fs::File::open(output).unwrap());
                let mut actual = vec![0; stride];
                for (case, expected) in cases.iter().zip(&expected) {
                    file.read_exact(&mut actual).unwrap();
                    if let Some(index) = actual.iter().zip(expected).position(|(a, b)| a != b) {
                        let field = if index < 64 {
                            format!("metadata[{}]", index / 8)
                        } else if index < 704 {
                            format!("register[{}]", (index - 64) / 8)
                        } else {
                            format!("RAM[{:#x}]", index - 704)
                        };
                        panic!(
                            "{name}/{optimization}/depth={depth}: {} differs at {field} byte {index}: actual={} expected={}",
                            case.name, actual[index], expected[index]
                        );
                    }
                }
                assert_eq!(
                    file.read(&mut actual[..1]).unwrap(),
                    0,
                    "unexpected extra states"
                );
            }
        }
    }
}

fn every_pc(module: &Module) -> Vec<Case> {
    let mut result = vec![];
    for instruction in module.program.instructions() {
        for (seed, budget) in [(0, 0), (1, 1), (2, 2), (3, 7), (4, 31), (5, 113)] {
            result.push(Case::new(module, instruction.address(), seed, budget));
        }
    }
    for pc in [
        0,
        module.image.memory_base,
        module.program.entry() + 1,
        module.image.memory_base + module.image.memory.len() as u64 - 1,
        u64::MAX - 1,
        u64::MAX,
    ] {
        result.push(Case::new(module, pc, 17, 5));
    }
    result
}

const CONTROL: &str = r#"
.text
.globl main
.type main,@function
main:
    call branchy
    call duplicated
    call nested
    call recursive
    lea leaf(%rip),%rax
    call indirect
    call altered
    ret
.size main,.-main
.type branchy,@function
branchy:
    test $1,%edi
    jz branch_even
    add $7,%eax
    test $2,%edi
    jz branch_join
    add $11,%eax
    jmp branch_join
branch_even:
    sub $5,%eax
    test $2,%edi
    jnz branch_join
    xor $19,%eax
branch_join:
    add %edi,%eax
    ret
.size branchy,.-branchy
.type nested,@function
nested:
    xor %eax,%eax
    xor %ecx,%ecx
outer:
    cmp %edi,%ecx
    jae loops_done
    xor %edx,%edx
inner:
    cmp $4,%edx
    jae outer_continue
    add $1,%edx
    cmp $2,%edx
    je inner
    cmp $3,%ecx
    je loops_done
    cmp $1,%ecx
    je outer_continue
    add %edx,%eax
    jmp inner
outer_continue:
    add $1,%ecx
    jmp outer
loops_done:
    ret
.size nested,.-nested
.type duplicated,@function
duplicated:
    endbr64
    push %rbp
    mov %rsp,%rbp
    mov %edi,-4(%rbp)
    cmpl $9,-4(%rbp)
    je duplicate_yes
    cmpl $31,-4(%rbp)
    jbe duplicate_no
    cmpl $126,-4(%rbp)
    ja duplicate_no
duplicate_yes:
    mov $1,%eax
    jmp duplicate_tail
duplicate_no:
    mov $0,%eax
duplicate_tail:
    pop %rbp
    ret
.size duplicated,.-duplicated
.type irreducible,@function
irreducible:
    test %edi,%edi
    jz irreducible_a
irreducible_b:
    add $1,%ecx
    cmp $5,%ecx
    jb irreducible_a
    ret
irreducible_a:
    add $1,%edx
    cmp $5,%edx
    jb irreducible_b
    ret
.size irreducible,.-irreducible
.type recursive,@function
recursive:
    test %edi,%edi
    jz recur_done
    sub $1,%edi
    call recursive
    add $1,%eax
recur_done:
    ret
.size recursive,.-recursive
.type indirect,@function
indirect:
    call *%rax
    ret
.size indirect,.-indirect
.type stack_call,@function
stack_call:
    call *(%rsp)
    ret
.size stack_call,.-stack_call
.type push_alias_call,@function
push_alias_call:
    call *-8(%rsp)
    ret
.size push_alias_call,.-push_alias_call
.type rsp_call,@function
rsp_call:
    call *%rsp
    ret
.size rsp_call,.-rsp_call
.type altered,@function
altered:
    lea landing(%rip),%rax
    mov %rax,(%rsp)
    ret
.size altered,.-altered
.type landing,@function
landing:
    add $23,%eax
    ret
.size landing,.-landing
.type leaf,@function
leaf:
    add $17,%eax
    ret
.size leaf,.-leaf
.type tail_a,@function
tail_a:
    add $1,%r12
    jmp tail_b
.size tail_a,.-tail_a
.type tail_b,@function
tail_b:
    add $1,%r13
    jmp tail_a
.size tail_b,.-tail_b
.type cycle,@function
cycle:
    add $1,%eax
    jmp cycle
.size cycle,.-cycle
.type fault_after,@function
fault_after:
    call leaf
    mov (%rdi),%rax
    ret
.size fault_after,.-fault_after
.type fault_callee,@function
fault_callee:
    call fault_after
    ret
.size fault_callee,.-fault_callee
.type ret_extra,@function
ret_extra:
    ret $24
.size ret_extra,.-ret_extra
.type vector_load,@function
vector_load:
    movaps (%rdi),%xmm0
    ret
.size vector_load,.-vector_load
.type vector_store,@function
vector_store:
    movups %xmm0,(%rdi)
    ret
.size vector_store,.-vector_store
"#;

#[test]
fn full_state_at_every_pc_in_branch_loop_call_and_fault_fixtures() {
    let scratch = native::Scratch::new();
    let module = module(&scratch, CONTROL);
    for name in [
        "main",
        "branchy",
        "nested",
        "recursive",
        "stack_call",
        "rsp_call",
        "altered",
        "tail_a",
        "cycle",
        "fault_callee",
        "ret_extra",
        "vector_load",
        "vector_store",
    ] {
        let _ = func_address(&module, name);
    }
    let plan = nirvana::module_outline::recover(&module.program).unwrap();
    let duplicate = plan
        .functions
        .iter()
        .find(|f| f.function.name == "duplicated")
        .unwrap();
    assert!(duplicate.structured.is_some());
    assert!(
        duplicate.sites.len() > duplicate.resumes.len(),
        "fixture must retain duplicated AST steps"
    );
    assert!(
        plan.functions
            .iter()
            .any(|f| f.function.name == "irreducible" && f.structured.is_none()),
        "fixture must exercise per-function goto fallback"
    );
    let mut cases = every_pc(&module);
    let sp = module.initial_registers()[4];
    for name in ["main", "branchy", "nested", "recursive"] {
        for seed in 0..8 {
            cases.push(Case::new(&module, func_address(&module, name), seed, 701));
        }
    }
    for name in ["tail_a", "cycle"] {
        let mut case = Case::new(&module, func_address(&module, name), 9, 50_003);
        case.name = format!("long bounded {name}");
        cases.push(case);
    }
    let mut recursive = Case::new(&module, func_address(&module, "recursive"), 1, 5000);
    recursive.name = "recursion exceeding 64 host frames".into();
    recursive.registers[7] = 137;
    cases.push(recursive);
    for target in [
        module_ir::ROOT_RETURN,
        func_address(&module, "leaf"),
        func_address(&module, "branchy") + 1,
        func_address(&module, "nested"),
        0,
    ] {
        let mut case = Case::new(&module, func_address(&module, "stack_call"), 3, 127);
        case.name = format!("stack operand target={target:#x}");
        case.patch_u64(&module, sp, target);
        cases.push(case);
        let mut case = Case::new(&module, func_address(&module, "indirect"), 3, 127);
        case.name = format!("register operand target={target:#x}");
        case.registers[0] = target;
        cases.push(case);
        let mut case = Case::new(&module, func_address(&module, "leaf"), 3, 127);
        case.name = format!("overwritten return target={target:#x}");
        case.patch_u64(&module, sp, target);
        cases.push(case);
    }
    for target in [module_ir::ROOT_RETURN, func_address(&module, "leaf"), 0] {
        let mut case = Case::new(&module, func_address(&module, "push_alias_call"), 3, 127);
        case.name = format!("call memory operand aliases pushed slot target={target:#x}");
        case.patch_u64(&module, sp - 8, target);
        cases.push(case);
    }
    // A forged return enters every internal instruction, including the second
    // arm of a diamond and loop bodies, after a real callee has set flags.
    for instruction in module.program.instructions() {
        let target = instruction.address();
        let mut case = Case::new(&module, func_address(&module, "leaf"), 4, 113);
        case.name = format!("forged return enters internal pc={target:#x}");
        case.patch_u64(&module, sp, target);
        cases.push(case);
    }
    let mut case = Case::new(&module, func_address(&module, "rsp_call"), 3, 53);
    case.name = "call target RSP must be captured before decrement".into();
    case.registers[4] = func_address(&module, "leaf");
    cases.push(case);
    let mut case = Case::new(&module, func_address(&module, "stack_call"), 3, 2);
    case.name = "valid target read before faulting push".into();
    case.registers[4] = module.image.memory_base;
    case.patch_u64(&module, module.image.memory_base, module_ir::ROOT_RETURN);
    cases.push(case);
    for name in ["fault_after", "fault_callee", "vector_load", "vector_store"] {
        for pointer in [
            module.image.memory_base + 32,
            module.image.memory_base + 33,
            module.image.memory_base - 1,
            module.image.memory_base + module.image.memory.len() as u64 - 8,
            u64::MAX - 3,
        ] {
            for budget in [0, 1, 2, 3, 7, 19] {
                let mut case = Case::new(&module, func_address(&module, name), 2, budget);
                case.name = format!("{name}/pointer={pointer:#x}/budget={budget}");
                case.registers[7] = pointer;
                cases.push(case);
            }
        }
    }
    for instruction in module
        .program
        .instructions()
        .iter()
        .filter(|i| matches!(i, Instruction::Return { .. } | Instruction::Transfer { .. }))
    {
        for pointer in [
            module.image.memory_base - 1,
            module.image.memory_base,
            module.image.memory_base + module.image.memory.len() as u64 - 4,
            u64::MAX - 3,
        ] {
            let mut case = Case::new(&module, instruction.address(), 2, 7);
            case.name = format!(
                "call/ret invalid stack pc={:#x}/sp={pointer:#x}",
                instruction.address()
            );
            case.registers[4] = pointer;
            cases.push(case);
        }
    }
    // Reuse the same C allocation across a suspended call/loop and its resume.
    // The Rust oracle composes two runs and includes accumulated started/imports.
    for name in ["main", "nested", "recursive"] {
        for budget in [0, 1, 2, 3, 7, 11, 19, 31, 47, 67, 89] {
            let mut case = Case::new(&module, func_address(&module, name), 6, budget);
            case.name = format!("same-state suspension/resume {name}/budget={budget}");
            case.resume_instructions = Some(1000);
            if name == "recursive" {
                case.registers[7] = 137;
            }
            cases.push(case);
        }
    }
    compare(&module, &cases, &scratch);
}

#[test]
fn import_budget_and_plt_stack_aliases_match_full_state() {
    let scratch = native::Scratch::new();
    let module = module(
        &scratch,
        r#"
.text
.globl main
.type main,@function
main:
    call htons@PLT
    mov %rax,%r12
    call htonl@PLT
    mov %rax,%r13
    call __errno_location@PLT
    movl $31337,(%rax)
    call getpid@PLT
    ret
.size main,.-main
.type leaf,@function
leaf:
    add $29,%eax
    ret
.size leaf,.-leaf
"#,
    );
    let mut cases = every_pc(&module);
    for seed in [0, 1, 0x12345678, u64::MAX] {
        for imports in [0, 1, 2, 3, 4, 8] {
            let mut case = Case::new(&module, module.program.entry(), seed, 127);
            case.registers[7] = seed;
            case.imports = imports;
            case.name = format!("conversion imports seed={seed}/budget={imports}");
            cases.push(case);
        }
    }
    for import in module.program.imports() {
        for budget in [0, 1, 8] {
            let mut case = Case::new(&module, import.address, 17, 0);
            case.imports = budget;
            case.name = format!("import entry {}/budget={budget}", import.name);
            cases.push(case);
        }
    }
    for instruction in module.program.instructions() {
        if let Instruction::Transfer {
            address,
            target: Target::Plt(slot),
            link: Some(link),
            ..
        } = instruction
        {
            for budget in [0, 1, 2, 19] {
                let mut case = Case::new(&module, *address, 2, budget);
                case.name = format!(
                    "GOT aliases pushed return at pc={address:#x}/link={link:#x}/budget={budget}"
                );
                case.registers[4] = slot + 8;
                cases.push(case);
            }
            for target in [
                module_ir::ROOT_RETURN,
                func_address(&module, "leaf"),
                module.program.entry(),
                0,
            ] {
                let mut case = Case::new(&module, *address, 2, 41);
                case.name = format!("modified GOT at pc={address:#x}/target={target:#x}");
                case.patch_u64(&module, *slot, target);
                cases.push(case);
            }
        }
    }
    for budget in 0..10 {
        let mut case = Case::new(&module, module.program.entry(), 3, budget);
        case.name = format!("same-state import suspension/resume budget={budget}");
        case.resume_instructions = Some(67);
        cases.push(case);
    }
    compare(&module, &cases, &scratch);
}

#[test]
fn restored_caller_value_and_partial_instruction_reentry_match_full_state() {
    let scratch = native::Scratch::new();
    let module = module(
        &scratch,
        r#"
.text
.globl main
.type main,@function
main:
    mov $17,%r12
    lea -16(%rsp),%rdi
    call saves_r12
    add %r12,%rax
    ret
.size main,.-main
.type saves_r12,@function
saves_r12:
    push %r12
    call overwrite_saved
    pop %r12
    ret
.size saves_r12,.-saves_r12
.type overwrite_saved,@function
overwrite_saved:
    movabs $0x1122334455667788,%rax
    mov %rax,(%rdi)
    ret
.size overwrite_saved,.-overwrite_saved
.type partial_push,@function
partial_push:
    push %rbp
    ret
.size partial_push,.-partial_push
"#,
    );
    let mut cases = every_pc(&module);
    let value = 0x1122_3344_5566_7788_u64;
    for seed in [0, 1, 0x1234_5678, u64::MAX] {
        let mut case = Case::new(&module, module.program.entry(), seed, 127);
        case.name = format!("callee restores aliased saved R12/seed={seed}");
        let result = expected(&module, &case);
        let word =
            |index: usize| u64::from_le_bytes(result[index * 8..index * 8 + 8].try_into().unwrap());
        assert_eq!(word(0), 0, "fixture must return normally");
        assert_eq!(word(8 + 12), value, "callee must restore the changed slot");
        assert_eq!(word(8), value.wrapping_add(value));
        cases.push(case);
    }
    // Stop before and after every effect on the normal nested-call path. In
    // particular, the saved R12 slot is overwritten before the pop restores it.
    for budget in 0..=13 {
        let mut case = Case::new(&module, module.program.entry(), 3, budget);
        case.name = format!("saved-register alias suspension/resume budget={budget}");
        case.resume_instructions = Some(127);
        cases.push(case);
    }
    let push = func_address(&module, "partial_push");
    for pointer in [
        module.image.memory_base,
        module.image.memory_base + 7,
        u64::MAX - 3,
    ] {
        for budget in [0, 1] {
            for resume_budget in [0, 1, 2, 7] {
                let mut case = Case::new(&module, push, 4, budget);
                case.registers[4] = pointer;
                case.resume_instructions = Some(resume_budget);
                case.name = format!(
                    "push fault retains partial RSP before reentry/sp={pointer:#x}/budget={budget}/{resume_budget}"
                );
                let result = expected(&module, &case);
                let word = |index: usize| {
                    u64::from_le_bytes(result[index * 8..index * 8 + 8].try_into().unwrap())
                };
                let pushes = u64::from(budget != 0) + u64::from(resume_budget != 0);
                let sp = pointer.wrapping_sub(8 * pushes);
                assert_eq!(word(8 + 4), sp, "fault must retain prior RSP writes");
                if pushes != 0 {
                    assert_eq!(word(5), sp, "last fault must use the current RSP");
                    assert_eq!(word(6), 8);
                    assert_eq!(word(7), 2);
                }
                assert_eq!(word(1), push, "a failed push must retain its PC");
                cases.push(case);
            }
        }
    }
    compare(&module, &cases, &scratch);
}

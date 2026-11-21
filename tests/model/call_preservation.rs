//! Execute the actual module machine independently of the summary projection.
use crate::support::native;

use nirvana::call_footprint;
use nirvana::ir::Reg;
use nirvana::linked_elf::LinkedOptions;
use nirvana::module_ir::{self, Limits, Module, RejectImports, Status};
use std::process::Command;

fn module(scratch: &native::Scratch) -> Module {
    let source = scratch.0.join("preservation.S");
    let binary = scratch.0.join("preservation");
    std::fs::write(&source, ASSEMBLY).unwrap();
    let output = native::compile_output(
        Command::new("cc")
            .arg("-no-pie")
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
        &std::fs::read(&binary).unwrap(),
        "main",
        LinkedOptions {
            load_bias: 0,
            ..Default::default()
        },
    )
    .unwrap()
}

fn random(seed: &mut u64) -> u64 {
    *seed ^= *seed << 13;
    *seed ^= *seed >> 7;
    *seed ^= *seed << 17;
    *seed
}

#[test]
fn actual_returns_preserve_reported_registers_for_arbitrary_initial_bits_and_ram() {
    let scratch = native::Scratch::new();
    let module = module(&scratch);
    let summary = call_footprint::analyze(&module.program).unwrap();
    let mut seed = 0x1618_0339_8874_9894;
    let caller_sp = module.image.stack_pointer - 0x1000;
    let entry_sp = caller_sp - 8;
    let slot = (entry_sp - module.image.memory_base) as usize;
    let mut compared = 0usize;
    for name in [
        "leaf", "branch", "spill", "recurse", "mutual_a", "mutual_b", "vector", "chain", "main",
    ] {
        let function = module
            .program
            .functions()
            .iter()
            .find(|f| f.name == name)
            .unwrap();
        let facts = summary.at(function.address).unwrap();
        assert!(facts.closed, "{name}: {:?}", facts.reason);
        assert!(facts.preserved.contains(&Reg(4)), "{name}: net RSP");
        for case in 0..64 {
            let mut before: Vec<_> = (0..80).map(|_| random(&mut seed)).collect();
            before[4] = caller_sp;
            before[7] = case % 9;
            let mut registers = before.clone();
            registers[4] = entry_sp;
            let mut memory = module.image.memory.clone();
            for byte in &mut memory[slot - 512..slot] {
                *byte = random(&mut seed) as u8;
            }
            memory[slot..slot + 8].copy_from_slice(&module_ir::ROOT_RETURN.to_le_bytes());
            let report = module
                .program
                .run_from(
                    function.address,
                    &registers,
                    module.image.memory_base,
                    &memory,
                    Limits {
                        instructions: 10_000,
                        imports: 0,
                    },
                    &mut RejectImports,
                )
                .unwrap();
            assert!(
                matches!(report.status, Status::Returned(_)),
                "{name} {case}: {:?}",
                report.status
            );
            assert_eq!(report.pc, module_ir::ROOT_RETURN);
            for &register in &facts.preserved {
                assert_eq!(
                    report.state.registers[register.0], before[register.0],
                    "{name} case={case} r{}",
                    register.0
                );
            }
            assert_eq!(
                &report.state.memory[slot..slot + 8],
                &module_ir::ROOT_RETURN.to_le_bytes()
            );
            for (register, &value) in before.iter().enumerate() {
                if report.state.registers[register] != value {
                    assert!(
                        facts.clobbers.contains(&Reg(register)),
                        "{name} case={case}: undeclared r{register} change"
                    );
                }
            }
            compared += 1;
        }
    }
    assert_eq!(compared, 576);
    println!("{compared} completed calls checked against actual guest register/RAM state");
}

#[test]
fn values_reported_as_unread_do_not_affect_other_registers_or_memory() {
    let scratch = native::Scratch::new();
    let module = module(&scratch);
    let summary = call_footprint::analyze(&module.program).unwrap();
    let caller_sp = module.image.stack_pointer - 0x1000;
    let entry_sp = caller_sp - 8;
    let slot = (entry_sp - module.image.memory_base) as usize;
    let mut seed = 0x2718_2818_2845_9045;
    let mut compared = 0;
    for name in ["leaf", "spill", "recurse", "mutual_a", "vector", "chain"] {
        let function = module
            .program
            .functions()
            .iter()
            .find(|f| f.name == name)
            .unwrap();
        let facts = summary.at(function.address).unwrap();
        assert!(facts.closed);
        let mut memory = module.image.memory.clone();
        memory[slot..slot + 8].copy_from_slice(&module_ir::ROOT_RETURN.to_le_bytes());
        let mut input: Vec<_> = (0..80).map(|_| random(&mut seed)).collect();
        input[4] = entry_sp;
        input[7] = 7;
        let run = |input: &[u64]| {
            module
                .program
                .run_from(
                    function.address,
                    input,
                    module.image.memory_base,
                    &memory,
                    Limits {
                        instructions: 10_000,
                        imports: 0,
                    },
                    &mut RejectImports,
                )
                .unwrap()
        };
        let original = run(&input);
        assert!(matches!(original.status, Status::Returned(_)));
        for register in 0..80 {
            if facts.reads.contains(&Reg(register)) {
                continue;
            }
            let mut changed = input.clone();
            changed[register] ^= 0xdead_beef_0123_4567;
            let report = run(&changed);
            // ROOT_RETURN exposes RAX as a result; perturbing a preserved RAX
            // changes that same register's observation, not any other output.
            assert!(
                matches!(report.status, Status::Returned(_)),
                "{name} r{register}"
            );
            if register != nirvana::x86::RAX {
                assert_eq!(report.status, original.status, "{name} r{register}");
            }
            assert_eq!(report.pc, original.pc);
            assert_eq!(
                report.state.trace, original.state.trace,
                "{name} r{register}"
            );
            assert_eq!(
                report.state.memory, original.state.memory,
                "{name} r{register}"
            );
            for other in 0..80 {
                if other != register {
                    assert_eq!(
                        report.state.registers[other], original.state.registers[other],
                        "{name} input r{register} output r{other}"
                    );
                }
            }
            assert_eq!(report.state.registers[register], changed[register]);
            compared += 1;
        }
    }
    assert!(compared > 200);
    println!(
        "{compared} unread-register perturbations compared over all other registers and full RAM"
    );
}

const ASSEMBLY: &str = r#"
.text
.globl main
.type main,@function
main:
    call chain
    ret
.size main,.-main
.type leaf,@function
leaf:
    lea 13(%rdi,%rdi,4),%rax
    ret
.size leaf,.-leaf
.type branch,@function
branch:
    test $1,%edi
    jz .Lbranch_even
    lea 3(%rdi),%rax
    ret
.Lbranch_even:
    lea 9(%rdi),%rax
    ret
.size branch,.-branch
.type spill,@function
spill:
    push %rbx
    sub $16,%rsp
    mov %rdi,%rbx
    mov %rdi,8(%rsp)
    mov 8(%rsp),%rax
    add %rbx,%rax
    add $16,%rsp
    pop %rbx
    ret
.size spill,.-spill
.type recurse,@function
recurse:
    test %rdi,%rdi
    jz .Lrecurse_base
    sub $16,%rsp
    sub $1,%rdi
    call recurse
    add $1,%rax
    add $16,%rsp
    ret
.Lrecurse_base:
    xor %eax,%eax
    ret
.size recurse,.-recurse
.type mutual_a,@function
mutual_a:
    test %rdi,%rdi
    jz .Lmutual_base_a
    sub $1,%rdi
    jmp mutual_b
.Lmutual_base_a:
    mov $1,%eax
    ret
.size mutual_a,.-mutual_a
.type mutual_b,@function
mutual_b:
    test %rdi,%rdi
    jz .Lmutual_base_b
    sub $1,%rdi
    jmp mutual_a
.Lmutual_base_b:
    mov $2,%eax
    ret
.size mutual_b,.-mutual_b
.type vector,@function
vector:
    movdqu -32(%rsp),%xmm0
    movdqu %xmm0,-16(%rsp)
    ret
.size vector,.-vector
.type chain,@function
chain:
    sub $16,%rsp
    call leaf
    call branch
    call spill
    call recurse
    call mutual_a
    call vector
    add $16,%rsp
    ret
.size chain,.-chain
.section .note.GNU-stack,"",@progbits
"#;

use crate::support::native;

use nirvana::effects::{CallTarget, Instruction, Limits, PutsOutcome, Status};
use nirvana::frontend::{EffectFrontendError, lift_elf_effects};
use nirvana::loader::LoadOptions;
use nirvana::x86::{self, RAX, RDI, REGISTER_COUNT, RSP};
use std::process::Command;

fn assemble(body: &str, data: &str) -> Vec<u8> {
    let scratch = native::Scratch::new();
    let source = scratch.0.join("effects.s");
    let object = source.with_extension("o");
    std::fs::write(&source, format!(
        ".text\n.space 32,0x90\n.globl fixture\n.type fixture,@function\nfixture:\n{body}\n.size fixture,.-fixture\n{data}\n.section .note.GNU-stack,\"\",@progbits\n"
    )).unwrap();
    let result = native::compile_output(
        Command::new("cc")
            .arg("-c")
            .arg(&source)
            .arg("-o")
            .arg(&object),
    );
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
    std::fs::read(object).unwrap()
}

fn string_data() -> &'static str {
    ".section .rodata,\"a\",@progbits\n.Lmessage: .asciz \"hello\"\n"
}

fn direct_call(base: u64, puts: u64, suffix: &[u8]) -> Vec<u8> {
    let relative = i32::try_from(i128::from(puts) - i128::from(base + 5)).unwrap();
    let mut bytes = vec![0xe8];
    bytes.extend(relative.to_le_bytes());
    bytes.extend(suffix);
    bytes
}

#[test]
fn opt_in_call_flags_feed_the_same_core_lifter_without_relaxing_legacy_policy() {
    let base = 0x4000;
    let puts = 0x5000;
    // call puts; jz yes; mov $1,%eax; ret; yes: mov $2,%eax; ret
    let bytes = direct_call(
        base,
        puts,
        &[0x74, 6, 0xb8, 1, 0, 0, 0, 0xc3, 0xb8, 2, 0, 0, 0, 0xc3],
    );
    assert!(x86::decode_at(&bytes, base).is_err());
    assert!(x86::lift(&bytes, base, base).is_err());
    let program = x86::lift_effects(&bytes, base, base, puts).unwrap();
    let mut input = vec![0; REGISTER_COUNT];
    input[RSP] = 0x1080;
    input[RDI] = 0x1010;
    let mut memory = vec![0; 256];
    memory[16..19].copy_from_slice(b"ok\0");
    let mut outcome = PutsOutcome::success(0x1234);
    outcome.registers[10] = 1; // explicit modeled ZF
    let report = program
        .run(&input, 0x1000, &memory, &[outcome], Limits::default())
        .unwrap();
    assert_eq!(report.status, Status::Returned(2));
    assert_eq!(report.output, b"ok\n");
    assert_eq!(report.state.registers[RSP], input[RSP] + 8);
    // A conditional before any call still cannot use unavailable entry flags.
    let mut invalid = vec![0x74, 0];
    invalid.extend(direct_call(base + 2, puts, &[0xc3]));
    assert!(matches!(
        x86::lift_effects(&invalid, base, base, puts),
        Err(x86::EffectLiftError::Core(
            x86::LiftError::UndefinedFlags { .. }
        ))
    ));
}

#[test]
fn effect_discovery_rejects_unknown_calls_dynamic_addresses_and_broken_cfgs() {
    let base = 0x4000;
    let puts = 0x5000;
    for bytes in [
        direct_call(base, puts + 1, &[0xc3]),
        direct_call(base, base + 5, &[0xc3]),
        vec![0xff, 0x14, 0x24, 0xc3], // call *(%rsp), not a fixed RIP target
        vec![0xff, 0x24, 0x8f],       // dynamic SIB jump
        vec![0x74, 0x01, 0x48, 0x89, 0xc0, 0xc3], // branch into mov
        vec![0x74, 0x01, 0x48, 0xc3], // reverse discovered overlap
        vec![0xe9, 0x00, 0x20, 0, 0], // unknown external tail jump
        vec![0xe8, 0, 0, 0],          // truncated call
        vec![0x90],                   // fallthrough outside function
        vec![0x74, 0x7f, 0xc3],       // conditional target outside function
    ] {
        assert!(
            x86::lift_effects(&bytes, base, base, puts).is_err(),
            "{bytes:x?}"
        );
    }
    assert!(x86::lift_effects(&[0xc3], u64::MAX, u64::MAX, puts).is_err());
    assert!(x86::lift_effects(&[0xc3], base, base + 1, puts).is_err());
    assert!(matches!(
        x86::lift_effects(&vec![0x90; 1_048_577], base, base, puts),
        Err(x86::EffectLiftError::Limit(_))
    ));
    let mut many = vec![0x90; 16_384];
    many.push(0xc3);
    assert!(matches!(
        x86::lift_effects(&many, base, base, puts),
        Err(x86::EffectLiftError::Limit(_))
    ));
}

#[test]
fn got_call_load_is_explicit_and_mutated_slot_is_checked_at_runtime() {
    let object = assemble(
        "lea .Lmessage(%rip),%rdi\ncall *puts@GOTPCREL(%rip)\nret",
        string_data(),
    );
    let lifted = lift_elf_effects(&object, "fixture", LoadOptions::default()).unwrap();
    let call = lifted
        .program
        .instructions()
        .iter()
        .find_map(|instruction| match instruction {
            Instruction::Call(call) => Some(call),
            _ => None,
        })
        .unwrap();
    let CallTarget::Memory(slot) = call.target else {
        panic!("GOT call was folded to a constant")
    };
    let mut memory = lifted.image.memory.clone();
    let offset = usize::try_from(slot - lifted.image.memory_base).unwrap();
    memory[offset..offset + 8].copy_from_slice(&0xdead_beef_u64.to_le_bytes());
    let mut input = vec![0; REGISTER_COUNT];
    input[RSP] = lifted.image.stack_pointer;
    let report = lifted
        .program
        .run(
            &input,
            lifted.image.memory_base,
            &memory,
            &[PutsOutcome::success(8)],
            Limits::default(),
        )
        .unwrap();
    assert_eq!(report.status, Status::UnknownTarget(0xdead_beef));
    assert!(report.output.is_empty());
    assert_eq!(report.consumed, 0);
    assert_eq!(report.state.registers[RSP], input[RSP] - 8);
}

#[test]
fn source_proof_rejects_internal_unknown_and_adjusted_external_calls_before_linking() {
    for body in [
        "call helper\nret",
        "call .Linside\nret\n.Linside: ret",
        "call *%rax\nret",
        "call puts+1\nret",
        "jmp puts+1",
    ] {
        let object = assemble(body, "");
        assert!(
            matches!(
                lift_elf_effects(&object, "fixture", LoadOptions::default()),
                Err(EffectFrontendError::UnprovenCall { .. })
            ),
            "{body}"
        );
    }
}

#[test]
fn proven_register_call_keeps_register_target_and_caller_chosen_return() {
    let object = assemble(
        "lea .Lmessage(%rip),%rdi\nmovabs $puts,%rax\ncall *%rax\nret",
        string_data(),
    );
    let lifted = lift_elf_effects(&object, "fixture", LoadOptions::default()).unwrap();
    assert!(lifted.program.instructions().iter().any(|instruction|
        matches!(instruction, Instruction::Call(call) if call.target == CallTarget::Register(nirvana::ir::Reg(RAX)))));
    let mut input = vec![0; REGISTER_COUNT];
    input[RSP] = lifted.image.stack_pointer;
    let result = 0x9876_5432_0000_002a;
    let report = lifted
        .program
        .run(
            &input,
            lifted.image.memory_base,
            &lifted.image.memory,
            &[PutsOutcome::success(result)],
            Limits::default(),
        )
        .unwrap();
    assert_eq!(report.status, Status::Returned(result));
    assert_eq!(report.output, b"hello\n");
}

#[test]
fn optimized_objects_cover_direct_got_tail_and_two_calls_at_relocated_bases() {
    let scratch = native::Scratch::new();
    for (name, expected, count) in [
        ("hello", &b"Hello, world!\n"[..], 1),
        ("two-calls", &b"first\nsecond\n"[..], 2),
    ] {
        for opt in ["-O0", "-O2"] {
            for got in [false, true] {
                let object_path = scratch.0.join(format!("{name}-{opt}-{got}.o"));
                let mut compiler = Command::new("cc");
                compiler.args([
                    "-std=c11",
                    "-Wall",
                    "-Wextra",
                    "-Werror",
                    "-pedantic",
                    "-fno-lto",
                    opt,
                    "-c",
                ]);
                if got {
                    compiler.arg("-fno-plt");
                }
                let compilation = native::compile_output(
                    compiler
                        .arg(native::fixture_root().join(format!("references/{name}.c")))
                        .arg("-o")
                        .arg(&object_path),
                );
                assert!(
                    compilation.status.success(),
                    "{}",
                    String::from_utf8_lossy(&compilation.stderr)
                );
                let object = std::fs::read(object_path).unwrap();
                let original = object.clone();
                for base in [0x10000, 0x70000] {
                    let lifted = lift_elf_effects(
                        &object,
                        "fixture",
                        LoadOptions {
                            base,
                            ..LoadOptions::default()
                        },
                    )
                    .unwrap();
                    let mut input = vec![0; REGISTER_COUNT];
                    input[RSP] = lifted.image.stack_pointer;
                    let outcomes = vec![PutsOutcome::success(0x55); count];
                    let report = lifted
                        .program
                        .run(
                            &input,
                            lifted.image.memory_base,
                            &lifted.image.memory,
                            &outcomes,
                            Limits::default(),
                        )
                        .unwrap();
                    // GCC preserves its int return contract through a tail
                    // call at O2, and explicit callee returns are kept intact.
                    assert_eq!(
                        report.status,
                        Status::Returned(0x55),
                        "{name}/{opt}/{got}/{base:x}"
                    );
                    assert_eq!(report.output, expected);
                    assert_eq!(report.consumed, count);
                    assert_eq!(object, original);
                }
            }
        }
    }
}

#[test]
fn conditional_message_selection_survives_linking_and_core_execution() {
    let object = assemble(
        "test %edi,%edi\nlea .Lfirst(%rip),%rdi\njne .Lcall\nlea .Lsecond(%rip),%rdi\n.Lcall: jmp puts",
        ".section .rodata,\"a\",@progbits\n.Lfirst: .asciz \"first\"\n.Lsecond: .asciz \"second\"",
    );
    let lifted = lift_elf_effects(&object, "fixture", LoadOptions::default()).unwrap();
    for (choice, expected) in [(0, &b"second\n"[..]), (1, &b"first\n"[..])] {
        let mut input = vec![0; REGISTER_COUNT];
        input[RSP] = lifted.image.stack_pointer;
        input[RDI] = choice;
        let report = lifted
            .program
            .run(
                &input,
                lifted.image.memory_base,
                &lifted.image.memory,
                &[PutsOutcome::success(1)],
                Limits::default(),
            )
            .unwrap();
        assert_eq!(report.status, Status::Returned(1));
        assert_eq!(report.output, expected);
    }
}

//! Sparse images retain ordinary guest addresses while storing only mapped bytes.
use crate::support::module_fixture;
use crate::support::native;
use module_fixture::{Case, check_generated_with_state, compile, expected_with_state};
use nirvana::{
    ir::AccessKind,
    linked_elf::LinkedOptions,
    module_ir::{self, Status},
};
use std::process::Command;

#[test]
fn distant_segments_holes_and_permissions_match_full_state_in_checked_backends() {
    let scratch = native::Scratch::new();
    for pie in [false, true] {
        let dir = scratch.0.join(format!("{pie}"));
        std::fs::create_dir(&dir).unwrap();
        let source = dir.join("source.S");
        let original = dir.join("original");
        std::fs::write(&source, ASSEMBLY).unwrap();
        compile(
            Command::new("cc")
                .args(if pie {
                    ["-fPIE", "-pie"]
                } else {
                    ["-fno-pie", "-no-pie"]
                })
                .args([
                    "-Wl,--section-start=.far=0x13370000",
                    "-Wl,--section-start=.rofar=0x23370000",
                    "-Wl,--section-start=.denied=0x33370000",
                ])
                .arg(&source)
                .arg("-o")
                .arg(&original),
        );
        assert_eq!(
            native::run_output(&original, Some(""), std::time::Duration::from_secs(5))
                .status
                .code(),
            Some(42)
        );
        let mut object = std::fs::read(&original).unwrap();
        let phoff = u64::from_le_bytes(object[32..40].try_into().unwrap()) as usize;
        let count = u16::from_le_bytes(object[56..58].try_into().unwrap()) as usize;
        for i in 0..count {
            let header = phoff + i * 56;
            let address = u64::from_le_bytes(object[header + 16..header + 24].try_into().unwrap());
            if address == 0x33370000 {
                object[header + 4..header + 8].copy_from_slice(&0u32.to_le_bytes());
            }
        }
        let bias = if pie { 0x10000 } else { 0 };
        let module = module_ir::lift_elf(
            &object,
            "fixture",
            LinkedOptions {
                load_bias: bias,
                stack_size: 4096,
            },
        )
        .unwrap();
        let layout = module.image.memory_layout.as_ref().unwrap();
        assert!(layout.size() < 65536);
        assert_eq!(module.program.model_id(), module_ir::SPARSE_MODEL_ID);
        assert_eq!(
            layout.regions().iter().map(|r| r.size).sum::<u64>(),
            module.image.memory.len() as u64
        );
        let mut cases = Vec::new();
        let mut rows = Vec::new();
        let registers = module.initial_registers();
        for address in [
            0x13370000,
            0x13370008,
            0x13370018,
            0x1337001c,
            0x23370000,
            0x33370000,
            0x1336ffff,
            0x20000000,
            u64::MAX - 3,
        ] {
            for mode in [0, 1] {
                let case = Case {
                    input: [address.wrapping_add(bias), mode, 0xfedcba9876543210, 19],
                    pc: module.program.entry(),
                    budget: 100,
                    patch: None,
                };
                let (row, status) = expected_with_state(&module, &case, Some(&registers));
                let success = (0x13370000..=0x13370018).contains(&address)
                    || (address == 0x23370000 && mode == 0);
                if success {
                    assert!(matches!(status, Status::Returned(_)));
                } else {
                    assert!(
                        matches!(status,Status::Fault(f)if f.address==address.wrapping_add(bias) && f.width==8 && f.access==if mode==0{AccessKind::Read}else{AccessKind::Write})
                    );
                }
                cases.push(case);
                rows.push(row);
            }
        }
        for instruction in module.program.instructions() {
            for budget in [0, 1, 2, 8, 64] {
                let case = Case {
                    input: [0x13370000 + bias, 0, 7, 19],
                    pc: instruction.address(),
                    budget,
                    patch: None,
                };
                rows.push(expected_with_state(&module, &case, Some(&registers)).0);
                cases.push(case);
            }
        }
        check_generated_with_state(
            &module,
            &cases,
            &rows,
            &dir,
            true,
            &[1, 64],
            Some(&registers),
        );
        assert!(
            module
                .program
                .run(
                    &registers,
                    module.image.memory_base,
                    &module.image.memory[..8],
                    module_ir::Limits::default(),
                    &mut module_ir::RejectImports
                )
                .is_err()
        );
    }
}

const ASSEMBLY: &str = r#"
.text
.globl fixture
.type fixture,@function
fixture:
    mov (%rdi),%rsi
    cmpq $0,8(%rdi)
    je .Lread
    mov 16(%rdi),%rax
    mov %rax,(%rsi)
    jmp .Lsave
.Lread:
    mov (%rsi),%rax
.Lsave:
    mov %rax,24(%rdi)
    ret
.size fixture,.-fixture
.globl main
.type main,@function
main:
    lea far_data(%rip),%rax
    mov (%rax),%eax
    ret
.size main,.-main
.section .far,"aw",@progbits
far_data: .quad 42,17,19,23
.section .rofar,"a",@progbits
.quad 37,41
.section .denied,"aw",@progbits
.quad 43,47
.section .note.GNU-stack,"",@progbits
"#;

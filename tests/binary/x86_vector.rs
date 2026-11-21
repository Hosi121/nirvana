//! Opt-in SSE decoding and native assembler/oracle checks.
use nirvana::ir::{
    AccessKind, Control, Execution, Expr, IrInstruction, Place, Program, Reg, RunStatus,
};
use nirvana::x86::{self, VectorInstruction};

use crate::support::native;

const COUNT: usize = 80;
const BASE: u64 = 0x1000;

fn evaluate(expression: Expr, registers: &[u64]) -> u64 {
    Program::new(
        0,
        COUNT,
        vec![IrInstruction {
            address: 0,
            size: 1,
            assignments: vec![],
            control: Control::Return(expression),
        }],
    )
    .unwrap()
    .execute(registers, 1)
    .unwrap()
    .value
}

fn program(instruction: &VectorInstruction) -> Program {
    Program::new(
        instruction.address,
        COUNT,
        vec![IrInstruction {
            address: instruction.address,
            size: instruction.size,
            assignments: instruction.assignments.clone(),
            control: Control::Return(Expr::Const(0)),
        }],
    )
    .unwrap()
}

// A small contract consumer: guards are outside the scalar IR, so perform the
// declared check before executing it. The integrated module runner separately
// checks instruction charging and structured fault reports.
fn guarded(
    instruction: &VectorInstruction,
    registers: &[u64],
    base: u64,
    memory: &[u8],
) -> Result<Execution, u32> {
    if let Some(guard) = &instruction.memory {
        let address = evaluate(guard.address.clone(), registers);
        if !address.is_multiple_of(u64::from(guard.alignment)) {
            return Err(9);
        }
        let valid = address
            .checked_sub(base)
            .and_then(|offset| offset.checked_add(u64::from(guard.width)))
            .is_some_and(|end| end <= memory.len() as u64)
            && address.checked_add(u64::from(guard.width) - 1).is_some();
        if !valid {
            return Err(1);
        }
    }
    Ok(program(instruction)
        .execute_with_memory(registers, base, memory, 1)
        .unwrap())
}

fn register_code(prefix: Option<u8>, opcode: u8, destination: u8, source: u8) -> Vec<u8> {
    let mut bytes: Vec<_> = prefix.into_iter().collect();
    let rex = 0x40 | ((destination >> 3) << 2) | (source >> 3);
    if rex != 0x40 {
        bytes.push(rex);
    }
    bytes.extend([0x0f, opcode, 0xc0 | ((destination & 7) << 3) | (source & 7)]);
    bytes
}

#[test]
fn all_register_codes_and_aliases_use_only_reserved_vector_registers() {
    for (prefix, opcode) in [
        (None, 0x10),
        (None, 0x11),
        (None, 0x28),
        (None, 0x29),
        (Some(0x66), 0x6f),
        (Some(0x66), 0x7f),
        (Some(0xf3), 0x6f),
        (Some(0xf3), 0x7f),
        (None, 0x57),
        (Some(0x66), 0xef),
        (Some(0x66), 0x6c),
    ] {
        for destination in 0..16 {
            for source in 0..16 {
                let bytes = register_code(prefix, opcode, destination, source);
                let instruction = x86::decode_vector_at(&bytes, 0x2000).unwrap();
                assert_eq!(instruction.size as usize, bytes.len());
                assert!(instruction.memory.is_none());
                for assignment in &instruction.assignments {
                    let Place::Register(Reg(register)) = assignment.destination else {
                        panic!("register form produced a memory store");
                    };
                    assert!((32..COUNT).contains(&register));
                }
                let mut registers = [0_u64; COUNT];
                for (index, value) in registers.iter_mut().enumerate() {
                    *value =
                        0x1020_3040_5060_7080 ^ (index as u64).wrapping_mul(0x0101_0101_0101_0101);
                }
                let actual = guarded(&instruction, &registers, 0, &[]).unwrap();
                assert_eq!(actual.registers[..32], registers[..32]);
                let destination_low = 32 + destination as usize * 2;
                let source_low = 32 + source as usize * 2;
                let mut expected = registers;
                match opcode {
                    0x11 | 0x29 | 0x7f => {
                        expected[source_low..source_low + 2]
                            .copy_from_slice(&registers[destination_low..destination_low + 2]);
                    }
                    0x57 | 0xef => {
                        expected[destination_low] ^= registers[source_low];
                        expected[destination_low + 1] ^= registers[source_low + 1];
                    }
                    0x6c => expected[destination_low + 1] = registers[source_low],
                    _ => expected[destination_low..destination_low + 2]
                        .copy_from_slice(&registers[source_low..source_low + 2]),
                }
                assert_eq!(actual.registers[..64], expected[..64]);
                // REX.W and REX.X are ignored for these register SSE forms.
                let mut rex_bytes: Vec<_> = prefix.into_iter().collect();
                rex_bytes.push(0x4a | ((destination >> 3) << 2) | (source >> 3));
                rex_bytes.extend(&bytes[bytes.len() - 3..]);
                let with_rex = x86::decode_vector_at(&rex_bytes, 0x2000).unwrap();
                let rex_actual = guarded(&with_rex, &registers, 0, &[]).unwrap();
                assert_eq!(rex_actual.registers, actual.registers);
            }
        }
    }
}

#[test]
fn movq_all_gpr_xmm_codes_clears_high_lane_without_clobbering_gp_or_flags() {
    for destination in 0..16 {
        for source in 0..16 {
            let bytes = [
                0x66,
                0x48 | ((destination >> 3) << 2) | (source >> 3),
                0x0f,
                0x6e,
                0xc0 | ((destination & 7) << 3) | (source & 7),
            ];
            let instruction = x86::decode_vector_at(&bytes, 0).unwrap();
            let mut registers = [u64::MAX; COUNT];
            registers[source as usize] = 0xfeed_face_cafe_beef;
            let result = guarded(&instruction, &registers, 0, &[]).unwrap();
            assert_eq!(result.registers[..32], registers[..32]);
            assert_eq!(
                result.registers[32 + destination as usize * 2],
                0xfeed_face_cafe_beef
            );
            assert_eq!(result.registers[33 + destination as usize * 2], 0);
        }
    }
}

#[test]
fn sib_rip_relative_absolute_and_signed_displacements() {
    let mut registers = [0_u64; COUNT];
    for (index, value) in registers[..16].iter_mut().enumerate() {
        *value = 0x2000 + index as u64 * 16;
    }
    for base in 0_u8..16 {
        for index in 0_u8..16 {
            for (scale_bits, scale) in [(0, 1), (1, 2), (2, 4), (3, 8)] {
                let bytes = [
                    0x43 | ((base >> 3) & 1) | ((index >> 3) << 1),
                    0x0f,
                    0x10,
                    0x44,
                    (scale_bits << 6) | ((index & 7) << 3) | (base & 7),
                    0xe0,
                ];
                // Override only B/X; the neutral REX must not extend low codes.
                let mut bytes = bytes;
                bytes[0] = 0x40 | (base >> 3) | ((index >> 3) << 1);
                let instruction = x86::decode_vector_at(&bytes, 0x8000).unwrap();
                let guard = instruction.memory.unwrap();
                let expected = registers[base as usize].wrapping_sub(32)
                    + if index == 4 {
                        0
                    } else {
                        registers[index as usize] * scale
                    };
                assert_eq!(evaluate(guard.address, &registers), expected);
            }
        }
    }
    for (bytes, expected) in [
        (&[0x0f, 0x10, 0x05, 0xf9, 0xff, 0xff, 0xff][..], 0x8000),
        (&[0x41, 0x0f, 0x10, 0x05, 0xf8, 0xff, 0xff, 0xff], 0x8000),
        // Mod00 SIB base5 is displacement-only, even with REX.B set.
        (
            &[0x41, 0x0f, 0x10, 0x04, 0x25, 0x00, 0x80, 0xff, 0xff],
            u64::MAX - 0x7fff,
        ),
        (
            &[0x0f, 0x10, 0x80, 0x00, 0x80, 0xff, 0xff],
            registers[0].wrapping_sub(0x8000),
        ),
    ] {
        let instruction = x86::decode_vector_at(bytes, 0x8000).unwrap();
        assert_eq!(
            evaluate(instruction.memory.unwrap().address, &registers),
            expected
        );
    }
}

#[test]
fn guards_cover_full_memory_operand_and_alignment_before_any_assignment() {
    let mut registers = [0xfeed_face_cafe_beef; COUNT];
    registers[x86::RDI] = BASE;
    for (bytes, access, alignment) in [
        (&[0x0f, 0x10, 0x07][..], AccessKind::Read, 1),
        (&[0x0f, 0x11, 0x07], AccessKind::Write, 1),
        (&[0x0f, 0x28, 0x07], AccessKind::Read, 16),
        (&[0x0f, 0x29, 0x07], AccessKind::Write, 16),
        (&[0x66, 0x0f, 0x6f, 0x07], AccessKind::Read, 16),
        (&[0x66, 0x0f, 0x7f, 0x07], AccessKind::Write, 16),
        (&[0xf3, 0x0f, 0x6f, 0x07], AccessKind::Read, 1),
        (&[0xf3, 0x0f, 0x7f, 0x07], AccessKind::Write, 1),
        (&[0x66, 0x0f, 0xef, 0x07], AccessKind::Read, 16),
        (&[0x0f, 0x57, 0x07], AccessKind::Read, 16),
        (&[0x66, 0x0f, 0x6c, 0x07], AccessKind::Read, 16),
    ] {
        let instruction = x86::decode_vector_at(bytes, 0).unwrap();
        let guard = instruction.memory.as_ref().unwrap();
        assert_eq!(
            (guard.width, guard.access, guard.alignment),
            (16, access, alignment)
        );
        // Only the first lane is in range; a store must not commit it.
        for length in [0, 1, 7, 8, 9, 15] {
            let memory = vec![0x5a; length];
            assert_eq!(
                guarded(&instruction, &registers, BASE, &memory).unwrap_err(),
                1
            );
            assert_eq!(memory, vec![0x5a; length]);
        }
        assert!(guarded(&instruction, &registers, BASE, &[0x5a; 16]).is_ok());
        let mut unaligned = registers;
        unaligned[x86::RDI] += 1;
        let result = guarded(&instruction, &unaligned, BASE, &[0x5a; 17]);
        if alignment == 16 {
            assert_eq!(result.unwrap_err(), 9);
        } else {
            assert!(result.is_ok());
        }
        let mut overflow = registers;
        overflow[x86::RDI] = u64::MAX - 7;
        assert!(guarded(&instruction, &overflow, u64::MAX - 7, &[0x5a; 16]).is_err());
    }
    // MOVHPS reads exactly m64 and preserves the low lane.
    let instruction = x86::decode_vector_at(&[0x0f, 0x16, 0x07], 0).unwrap();
    let guard = instruction.memory.as_ref().unwrap();
    assert_eq!((guard.width, guard.alignment), (8, 1));
    let result = guarded(&instruction, &registers, BASE, &42_u64.to_le_bytes()).unwrap();
    assert_eq!(
        (result.registers[32], result.registers[33]),
        (registers[32], 42)
    );
}

#[test]
fn memory_loads_snapshot_both_lanes_before_architectural_destination_writes() {
    let instruction = x86::decode_vector_at(&[0xf3, 0x0f, 0x6f, 0x07], 0).unwrap();
    let mut registers = [u64::MAX; COUNT];
    registers[x86::RDI] = BASE;
    // Deliberately omit the outer guard: even a late scalar high-lane fault
    // cannot replace the destination's low lane with a partially loaded value.
    let report = program(&instruction)
        .run_with_memory(&registers, BASE, &[0x5a; 8], 1)
        .unwrap();
    assert!(matches!(report.status, RunStatus::Fault(_)));
    assert_eq!(&report.state.registers[32..64], &registers[32..64]);
}

#[test]
fn legacy_decoders_remain_opt_out_and_unsupported_forms_fail_closed() {
    for bytes in [
        &[0x66, 0x0f, 0xef, 0xc0][..],
        &[0x0f, 0x57, 0xc0],
        &[0x0f, 0x10, 0xc0],
        &[0x66, 0x48, 0x0f, 0x6e, 0xc0],
        &[0x66, 0x0f, 0x6c, 0xc0],
        &[0x0f, 0x16, 0x00],
    ] {
        assert!(x86::decode_at(bytes, 0).is_err());
        assert!(x86::decode_reference_at(bytes, 0).is_err());
        assert!(x86::decode_vector_at(bytes, 0).is_ok());
    }
    for bytes in [
        &[0x66, 0x0f, 0x6e, 0xc0][..],   // MOVD is not MOVQ.
        &[0x66, 0x48, 0x0f, 0x6e, 0x00], // Unsupported MOVQ m64.
        &[0x0f, 0x16, 0xc0],             // MOVLHPS is not MOVHPS.
        &[0x66, 0x0f, 0x10, 0xc0],       // MOVUPD.
        &[0x66, 0x0f, 0x28, 0xc0],       // MOVAPD.
        &[0xf3, 0x0f, 0x10, 0xc0],       // MOVSS.
        &[0xf2, 0x0f, 0x10, 0xc0],       // MOVSD.
        &[0x0f, 0x6f, 0xc0],             // MMX.
        &[0xf3, 0x0f, 0xef, 0xc0],
        &[0x66, 0x0f, 0x57, 0xc0],
        &[0xc5, 0xf8, 0x57, 0xc0],
        &[0x62, 0xf1, 0x7c, 0x48, 0x57, 0xc0],
        &[0x66, 0xf3, 0x0f, 0x6f, 0xc0],
        &[0xf3, 0x66, 0x0f, 0x6f, 0xc0],
        &[0x66, 0x66, 0x0f, 0xef, 0xc0],
        &[0x48, 0x66, 0x0f, 0xef, 0xc0],
        &[0x40, 0x48, 0x0f, 0x57, 0xc0],
    ] {
        assert!(x86::decode_vector_at(bytes, 0).is_err(), "{bytes:02x?}");
    }
    for prefix in [0xf0, 0xf2, 0x26, 0x2e, 0x36, 0x3e, 0x64, 0x65, 0x67] {
        let bytes = [prefix, 0x0f, 0x57, 0xc0];
        assert!(x86::decode_vector_at(&bytes, 0).is_err());
    }
}

#[test]
fn every_truncated_prefix_modrm_sib_displacement_and_address_overflow_is_rejected() {
    for bytes in [
        &[0x66, 0x4f, 0x0f, 0x6f, 0x84, 0xf5, 0x98, 0xba, 0xdc, 0xfe][..],
        &[0xf3, 0x45, 0x0f, 0x7f, 0x44, 0x24, 0xe0],
        &[0x0f, 0x10, 0x05, 0x12, 0x34, 0x56, 0x78],
        &[0x66, 0x48, 0x0f, 0x6e, 0xc0],
        &[0x0f, 0x16, 0x04, 0x25, 0x12, 0x34, 0x56, 0x78],
    ] {
        assert!(x86::decode_vector_at(bytes, 0).is_ok());
        for length in 0..bytes.len() {
            let error = x86::decode_vector_at(&bytes[..length], 0x1234).unwrap_err();
            assert_eq!(error.address, 0x1234);
        }
        assert!(x86::decode_vector_at(bytes, u64::MAX - bytes.len() as u64).is_ok());
        assert!(x86::decode_vector_at(bytes, u64::MAX - bytes.len() as u64 + 1).is_err());
    }
    assert!(x86::decode_vector_at(&[0x66; 16], 0).is_err());
    assert!(x86::decode_vector_at(&[0x40; 16], 0).is_err());
}

#[cfg(all(target_arch = "x86_64", target_os = "linux"))]
#[derive(Clone)]
struct OracleCase {
    mnemonic: &'static str,
    destination: u8,
    source: Option<u8>,
    store: bool,
    gpr: Option<u8>,
}

#[cfg(all(target_arch = "x86_64", target_os = "linux"))]
fn native_oracle(
    directory: &std::path::Path,
    cases: &[OracleCase],
) -> (std::path::PathBuf, Vec<Vec<u8>>) {
    use std::fmt::Write as _;
    use std::process::Command;
    let mut assembly = String::from(".intel_syntax noprefix\n.text\n");
    let mut source = String::from("#include <inttypes.h>\n#include <stdio.h>\n");
    let mut names = Vec::new();
    for (index, case) in cases.iter().enumerate() {
        let destination = case.destination;
        let name = format!("oracle_{index}");
        names.push(name.clone());
        writeln!(
            source,
            "extern void {name}(uint64_t *, uint64_t *, uint64_t);"
        )
        .unwrap();
        writeln!(assembly, ".global {name}\n.type {name}, @function\n{name}:\npush r15\nmovdqu xmm{destination}, [rdi]").unwrap();
        if let Some(register) = case.source
            && register != destination
        {
            writeln!(assembly, "movdqu xmm{register}, [rdi+16]").unwrap();
        }
        assembly.push_str("lea r8, [rdi+32]\nmov r9, 8\n");
        let operand = if let Some(register) = case.gpr {
            let gpr = ["rax", "r10", "r15"][register as usize];
            writeln!(assembly, "mov {gpr}, [rdi+16]").unwrap();
            gpr.to_owned()
        } else if let Some(register) = case.source {
            format!("xmm{register}")
        } else {
            let width = if case.mnemonic == "movhps" {
                "qword"
            } else {
                "xmmword"
            };
            format!("{width} ptr [r8+r9*2-16]")
        };
        writeln!(assembly, "push rdx\npopfq\n.global vector_op_{index}\n.type vector_op_{index}, @function\nvector_op_{index}:").unwrap();
        if case.store {
            writeln!(assembly, "{} {operand}, xmm{destination}", case.mnemonic).unwrap();
        } else {
            writeln!(assembly, "{} xmm{destination}, {operand}", case.mnemonic).unwrap();
        }
        writeln!(assembly, ".size vector_op_{index}, .-vector_op_{index}").unwrap();
        assembly.push_str("pushfq\npop rax\nmov [rsi+32], rax\n");
        writeln!(assembly, "movdqu [rsi], xmm{destination}").unwrap();
        assembly.push_str("mov rax, [rdi+32]\nmov [rsi+16], rax\nmov rax, [rdi+40]\nmov [rsi+24], rax\npop r15\nret\n");
        writeln!(assembly, ".size {name}, .-{name}").unwrap();
    }
    assembly.push_str(".section .note.GNU-stack,\"\",@progbits\n");
    writeln!(
        source,
        "static void (*const functions[])(uint64_t *,uint64_t *,uint64_t) = {{{}}};",
        names.join(",")
    )
    .unwrap();
    source.push_str(r#"
int main(void) {
    unsigned index;
    _Alignas(16) uint64_t input[6], output[5];
    uint64_t flags;
    while (scanf("%u %" SCNu64 " %" SCNu64 " %" SCNu64 " %" SCNu64 " %" SCNu64 " %" SCNu64 " %" SCNu64,
                 &index, &input[0], &input[1], &input[2], &input[3], &input[4], &input[5], &flags) == 8) {
        if (index >= sizeof(functions)/sizeof(functions[0])) return 2;
        functions[index](input, output, flags);
        printf("%" PRIu64 " %" PRIu64 " %" PRIu64 " %" PRIu64 " %" PRIu64 "\n",
               output[0], output[1], output[2], output[3], output[4]);
    }
    return 0;
}
"#);
    let assembly_path = directory.join("oracle.S");
    let source_path = directory.join("oracle.c");
    let object_path = directory.join("oracle.o");
    let executable = directory.join("oracle");
    std::fs::write(&assembly_path, assembly).unwrap();
    std::fs::write(&source_path, source).unwrap();
    let assembled = native::compile_output(
        Command::new("cc")
            .arg("-c")
            .arg(&assembly_path)
            .arg("-o")
            .arg(&object_path),
    );
    assert!(
        assembled.status.success(),
        "{}",
        String::from_utf8_lossy(&assembled.stderr)
    );
    let compiled = native::compile_output(
        Command::new("cc")
            .args(["-std=c11", "-O2", "-Wall", "-Wextra", "-Werror"])
            .arg(&source_path)
            .arg(&object_path)
            .arg("-o")
            .arg(&executable),
    );
    assert!(
        compiled.status.success(),
        "{}",
        String::from_utf8_lossy(&compiled.stderr)
    );
    let object = std::fs::read(object_path).unwrap();
    let instructions = (0..cases.len())
        .map(|index| {
            nirvana::elf::read_function(&object, &format!("vector_op_{index}"))
                .unwrap()
                .bytes
        })
        .collect();
    (executable, instructions)
}

#[cfg(all(target_arch = "x86_64", target_os = "linux"))]
#[test]
fn assembler_encoded_forms_match_native_sse_results_memory_and_preserved_flags() {
    use std::fmt::Write as _;
    let mut cases = Vec::new();
    for mnemonic in [
        "movaps",
        "movups",
        "movdqa",
        "movdqu",
        "pxor",
        "xorps",
        "punpcklqdq",
    ] {
        for destination in [0, 7, 8, 15] {
            for source in [0, 7, 8, 15] {
                cases.push(OracleCase {
                    mnemonic,
                    destination,
                    source: Some(source),
                    store: false,
                    gpr: None,
                });
            }
        }
        for destination in 0..16 {
            cases.push(OracleCase {
                mnemonic,
                destination,
                source: None,
                store: false,
                gpr: None,
            });
            if matches!(mnemonic, "movaps" | "movups" | "movdqa" | "movdqu") {
                cases.push(OracleCase {
                    mnemonic,
                    destination,
                    source: None,
                    store: true,
                    gpr: None,
                });
            }
        }
    }
    for destination in 0..16 {
        cases.push(OracleCase {
            mnemonic: "movhps",
            destination,
            source: None,
            store: false,
            gpr: None,
        });
        for gpr in 0..3 {
            cases.push(OracleCase {
                mnemonic: "movq",
                destination,
                source: None,
                store: false,
                gpr: Some(gpr),
            });
        }
    }
    let scratch = native::Scratch::new();
    let (executable, instructions) = native_oracle(&scratch.0, &cases);
    let mut input = String::new();
    let mut expected = Vec::new();
    for (index, (case, bytes)) in cases.iter().zip(instructions).enumerate() {
        let instruction = x86::decode_vector_at(&bytes, 0x2000).unwrap();
        assert_eq!(
            instruction.size as usize,
            bytes.len(),
            "{} {bytes:02x?}",
            case.mnemonic
        );
        for pattern in [
            0_u64,
            1,
            u64::MAX,
            0x8000_0000_0000_0000,
            0x1234_5678_9abc_def0,
            0x0123_4567_89ab_cdef,
        ] {
            let words = [
                pattern,
                pattern.rotate_left(7),
                !pattern,
                pattern.wrapping_add(91),
                pattern.rotate_left(23),
                pattern.wrapping_mul(1009),
            ];
            let mut registers = [0_u64; COUNT];
            registers[8] = BASE;
            registers[9] = 8;
            registers[32 + case.destination as usize * 2] = words[0];
            registers[33 + case.destination as usize * 2] = words[1];
            if let Some(source) = case.source
                && source != case.destination
            {
                registers[32 + source as usize * 2] = words[2];
                registers[33 + source as usize * 2] = words[3];
            }
            if let Some(gpr) = case.gpr {
                registers[[0, 10, 15][gpr as usize]] = words[2];
            }
            let mut seed = 0x202 | ((pattern & 1) << 4);
            for (ordinal, (register, bit)) in [
                (x86::CF, 0),
                (x86::PF, 2),
                (x86::ZF, 6),
                (x86::SF, 7),
                (x86::OF, 11),
            ]
            .into_iter()
            .enumerate()
            {
                registers[register] = (pattern >> ordinal) & 1;
                seed |= registers[register] << bit;
            }
            let memory: Vec<_> = words[4..]
                .iter()
                .flat_map(|word| word.to_le_bytes())
                .collect();
            let actual = guarded(&instruction, &registers, BASE, &memory).unwrap();
            assert_eq!(actual.registers[..32], registers[..32]);
            let output = [
                actual.registers[32 + case.destination as usize * 2],
                actual.registers[33 + case.destination as usize * 2],
                u64::from_le_bytes(actual.memory[..8].try_into().unwrap()),
                u64::from_le_bytes(actual.memory[8..16].try_into().unwrap()),
                seed & 0x8d5,
            ];
            expected.push(output);
            writeln!(
                input,
                "{index} {} {} {} {} {} {} {seed}",
                words[0], words[1], words[2], words[3], words[4], words[5]
            )
            .unwrap();
        }
    }
    let observed = native::run_fields(&executable, &input, 5);
    assert_eq!(observed.len(), expected.len());
    for (ordinal, (actual, expected)) in observed.into_iter().zip(expected).enumerate() {
        let mut actual = actual;
        actual[4] &= 0x8d5;
        assert_eq!(
            actual,
            expected,
            "oracle case {} ({}) pattern {}",
            ordinal / 6,
            cases[ordinal / 6].mnemonic,
            ordinal % 6
        );
    }
}

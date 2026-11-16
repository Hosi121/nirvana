use nirvana::ir::Width;
use nirvana::x86::{self, Alu, LiftError, Operand, Operation, Register};

#[test]
fn decodes_rex_sib_rip_and_extended_registers() {
    let instruction = x86::decode_at(&[0x4f, 0x8b, 0x64, 0xac, 0xe0], 0x1000).unwrap();
    let Operation::Mov {
        destination: Operand::Register(register),
        source: Operand::Memory { address, width },
    } = instruction.operation
    else {
        panic!()
    };
    assert_eq!(register.index, 12);
    assert_eq!(width, Width::U64);
    assert_eq!(
        (
            address.base,
            address.index,
            address.scale,
            address.displacement
        ),
        (Some(12), Some(13), 4, -32)
    );
    let instruction = x86::decode_at(&[0x48, 0x8b, 0x05, 0x10, 0, 0, 0], 0).unwrap();
    let Operation::Mov {
        source: Operand::Memory { address, .. },
        ..
    } = instruction.operation
    else {
        panic!()
    };
    assert!(address.rip_relative);
    assert_eq!(instruction.size, 7);
}

#[test]
fn byte_registers_distinguish_ah_from_spl_and_movzx_destinations() {
    let Operation::Mov {
        destination: Operand::Register(ah),
        ..
    } = x86::decode_at(&[0xb4, 0x12], 0).unwrap().operation
    else {
        panic!()
    };
    assert_eq!(
        ah,
        Register {
            index: 0,
            width: Width::U8,
            shift: 8
        }
    );
    let Operation::Mov {
        destination: Operand::Register(spl),
        ..
    } = x86::decode_at(&[0x40, 0xb4, 0x12], 0).unwrap().operation
    else {
        panic!()
    };
    assert_eq!(
        spl,
        Register {
            index: 4,
            width: Width::U8,
            shift: 0
        }
    );
    let Operation::Extend { destination, .. } =
        x86::decode_at(&[0x0f, 0xb6, 0xe0], 0).unwrap().operation
    else {
        panic!()
    };
    assert_eq!(
        destination,
        Register {
            index: 4,
            width: Width::U32,
            shift: 0
        }
    );
}

#[test]
fn rex_b_turns_the_nop_opcode_into_exchange_with_r8() {
    let program = x86::lift(&[0x49, 0x90, 0xc3], 0, 0).unwrap();
    let mut registers = vec![0; x86::REGISTER_COUNT];
    registers[x86::RAX] = 1;
    registers[8] = 2;
    let result = program.execute(&registers, 2).unwrap();
    assert_eq!((result.value, result.registers[8]), (2, 1));
}

#[test]
fn signed_multiply_flags_match_i128_without_using_the_umul_high_implementation() {
    for width in [Width::U16, Width::U32, Width::U64] {
        let mut code = Vec::new();
        if width == Width::U16 {
            code.push(0x66);
        }
        if width == Width::U64 {
            code.push(0x48);
        }
        code.extend([0x0f, 0xaf, 0xc1, 0xc3]);
        let program = x86::lift(&code, 0, 0).unwrap();
        let bits = width.bits();
        let sign = 1u64 << (bits - 1);
        let mask = width.mask();
        for left in [0, 1, 2, sign - 1, sign, mask - 1, mask] {
            for right in [0, 1, 2, sign - 1, sign, mask - 1, mask] {
                let mut registers = vec![0; x86::REGISTER_COUNT];
                registers[x86::RAX] = left;
                registers[x86::RCX] = right;
                let result = program.execute(&registers, 2).unwrap();
                let expected = signed(left, bits) * signed(right, bits);
                let overflow =
                    u64::from(expected < -(1i128 << (bits - 1)) || expected >= 1i128 << (bits - 1));
                assert_eq!(result.value, expected as u64 & mask);
                assert_eq!(
                    (result.registers[x86::CF], result.registers[x86::OF]),
                    (overflow, overflow),
                    "{width:?}: {left:#x} * {right:#x}"
                );
            }
        }
    }
}

#[test]
fn immediate_sign_extension_and_relative_targets_include_the_whole_instruction() {
    let instruction = x86::decode_at(&[0x48, 0x83, 0xc0, 0xff], 0).unwrap();
    assert!(matches!(
        instruction.operation,
        Operation::Alu {
            kind: Alu::Add,
            source: Operand::Immediate(u64::MAX),
            ..
        }
    ));
    assert_eq!(
        x86::decode_at(&[0xeb, 0xfe], 0x1000).unwrap().operation,
        Operation::Jump(0x1000)
    );
    assert_eq!(
        x86::decode_at(&[0x0f, 0x84, 4, 0, 0, 0], 0x1000)
            .unwrap()
            .operation,
        Operation::Branch {
            condition: 4,
            target: 0x100a
        }
    );
}

#[test]
fn reachable_decoding_ignores_dead_padding_and_rejects_interior_targets() {
    assert_eq!(
        x86::decode_reachable(&[0xc3, 0x0f, 0x0b], 0, 0)
            .unwrap()
            .len(),
        1
    );
    assert!(x86::decode_reachable(&[0xeb, 1, 0xb8, 0, 0, 0, 0, 0xc3], 0, 2).is_ok());
    assert!(x86::decode_reachable(&[0x74, 1, 0xb8, 0, 0, 0, 0, 0xc3], 0, 0).is_err());
    assert!(x86::decode_reachable(&[0xeb, 0x7f], 0, 0).is_err());
}

#[test]
fn rejects_truncation_prefixes_and_instruction_length_overflow() {
    for bytes in [
        &[0x48, 0x8b][..],
        &[0x67, 0x90],
        &[0x64, 0x90],
        &[0x0f, 0x28, 0xc0],
        &[0xe8, 0, 0, 0, 0],
    ] {
        assert!(x86::decode_at(bytes, 0).is_err(), "{bytes:02x?}");
    }
    assert!(x86::decode_at(&[0x66; 16], 0).is_err());
    assert!(x86::decode_at(&[0xc3], u64::MAX).is_err());
}

#[test]
fn decoding_small_arbitrary_inputs_never_panics() {
    let mut state = 0x1248_369a_bcde_f001u64;
    for _ in 0..2048 {
        let mut bytes = [0; 16];
        for byte in &mut bytes {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            *byte = state as u8;
        }
        for length in 0..=16 {
            let _ = x86::decode_at(&bytes[..length], 0x1000);
        }
        let _ = x86::lift(&bytes, 0x1000, 0x1000);
    }
}

#[test]
fn partial_writes_zero_extension_sign_extension_and_stack_round_trip() {
    for (code, input, expected) in [
        (
            &[0xb8, 0xff, 0xff, 0xff, 0xff, 0xc3][..],
            u64::MAX,
            0xffff_ffff,
        ),
        (
            &[0xb4, 0x12, 0xc3][..],
            0x1122_3344_5566_7788,
            0x1122_3344_5566_1288,
        ),
        (&[0x48, 0x0f, 0xbe, 0xc0, 0xc3][..], 0x80, u64::MAX - 127),
    ] {
        let program = x86::lift(code, 0, 0).unwrap();
        let mut registers = vec![0; x86::REGISTER_COUNT];
        registers[x86::RAX] = input;
        assert_eq!(program.execute(&registers, 10).unwrap().value, expected);
    }
    let program = x86::lift(&[0x50, 0x48, 0x31, 0xc0, 0x58, 0xc3], 0, 0).unwrap();
    let mut registers = vec![0; x86::REGISTER_COUNT];
    registers[x86::RAX] = 123;
    registers[x86::RSP] = 0x1080;
    let execution = program
        .execute_with_memory(&registers, 0x1000, &[0; 256], 10)
        .unwrap();
    assert_eq!(execution.value, 123);
    assert_eq!(execution.registers[x86::RSP], 0x1088);
}

#[test]
fn rip_relative_store_uses_the_address_after_its_immediate() {
    let program = x86::lift(
        &[
            0x48, 0xc7, 0x05, 0x20, 0, 0, 0, 0xff, 0xff, 0xff, 0xff, 0xc3,
        ],
        0x1000,
        0x1000,
    )
    .unwrap();
    let execution = program
        .execute_with_memory(&[0; x86::REGISTER_COUNT], 0x1000, &[0; 64], 10)
        .unwrap();
    assert_eq!(&execution.memory[0x2b..0x33], &[0xff; 8]);
}

#[test]
fn conditions_cannot_read_entry_or_imul_undefined_flags() {
    assert!(matches!(
        x86::lift(&[0x74, 0, 0xc3], 0, 0),
        Err(LiftError::UndefinedFlags { .. })
    ));
    assert!(matches!(
        x86::lift(&[0x48, 0x0f, 0xaf, 0xc1, 0x74, 0, 0xc3], 0, 0),
        Err(LiftError::UndefinedFlags { .. })
    ));
    assert!(x86::lift(&[0x48, 0x0f, 0xaf, 0xc1, 0x70, 0, 0xc3], 0, 0).is_ok());
}

#[test]
fn a_false_cmov_still_reads_its_memory_source() {
    // xor eax,eax sets ZF; CMOVNE rcx,[rdi] is false but still loads [rdi].
    let program = x86::lift(&[0x31, 0xc0, 0x48, 0x0f, 0x45, 0x0f, 0xc3], 0, 0).unwrap();
    assert!(matches!(
        program.execute_with_memory(&[0; x86::REGISTER_COUNT], 0x1000, &[0; 8], 10),
        Err(nirvana::ir::ExecutionError::MemoryAccess { address: 0, .. })
    ));
}

#[test]
fn inc_preserves_carry_instead_of_defining_it() {
    let program = x86::lift(&[0x39, 0xf2, 0xff, 0xc0, 0x0f, 0x92, 0xc1, 0xc3], 0, 0).unwrap();
    let mut registers = vec![0; x86::REGISTER_COUNT];
    registers[x86::RSI] = 1;
    registers[x86::RAX] = 0xffff_ffff;
    let result = program.execute(&registers, 10).unwrap();
    assert_eq!(
        (
            result.value,
            result.registers[x86::CF],
            result.registers[x86::RCX]
        ),
        (0, 1, 1)
    );
    assert!(matches!(
        x86::lift(&[0xff, 0xc0, 0x0f, 0x92, 0xc1, 0xc3], 0, 0),
        Err(LiftError::UndefinedFlags { .. })
    ));
}

fn signed(value: u64, bits: u32) -> i128 {
    let value = value as i128;
    if value & (1i128 << (bits - 1)) != 0 {
        value - (1i128 << bits)
    } else {
        value
    }
}

#[test]
fn arithmetic_flags_match_wide_integer_oracles_at_all_operand_widths() {
    for width in [Width::U8, Width::U16, Width::U32, Width::U64] {
        let bits = width.bits();
        let mask = width.mask();
        let sign = 1u64 << (bits - 1);
        let values = [0, 1, sign - 1, sign, mask - 1, mask];
        for (kind, opcode) in [
            (Alu::Add, 0x00),
            (Alu::Adc, 0x10),
            (Alu::Sub, 0x28),
            (Alu::Sbb, 0x18),
            (Alu::Cmp, 0x38),
        ] {
            for carry in [0u64, 1] {
                let mut code = if carry == 0 {
                    vec![0x39, 0xd2]
                } else {
                    vec![0x39, 0xf2]
                };
                match width {
                    Width::U16 => code.push(0x66),
                    Width::U64 => code.push(0x48),
                    _ => {}
                }
                code.extend([opcode + u8::from(width != Width::U8), 0xc8, 0xc3]);
                let program = x86::lift(&code, 0, 0).unwrap();
                for left in values {
                    for right in values {
                        let mut registers = vec![0; x86::REGISTER_COUNT];
                        registers[x86::RAX] = left;
                        registers[x86::RCX] = right;
                        registers[x86::RSI] = 1;
                        let actual = program.execute(&registers, 10).unwrap();
                        let borrow = if matches!(kind, Alu::Adc | Alu::Sbb) {
                            carry
                        } else {
                            0
                        };
                        let addition = matches!(kind, Alu::Add | Alu::Adc);
                        let wide = if addition {
                            i128::from(left) + i128::from(right) + i128::from(borrow)
                        } else {
                            i128::from(left) - i128::from(right) - i128::from(borrow)
                        };
                        let value = wide as u64 & mask;
                        let signed_wide = if addition {
                            signed(left, bits) + signed(right, bits) + i128::from(borrow)
                        } else {
                            signed(left, bits) - signed(right, bits) - i128::from(borrow)
                        };
                        assert_eq!(
                            actual.registers[x86::CF],
                            u64::from(wide < 0 || wide > i128::from(mask)),
                            "{width:?} {kind:?} {left:#x} {right:#x} carry={carry}"
                        );
                        assert_eq!(
                            actual.registers[x86::OF],
                            u64::from(
                                signed_wide < -(1i128 << (bits - 1))
                                    || signed_wide >= 1i128 << (bits - 1)
                            )
                        );
                        assert_eq!(actual.registers[x86::ZF], u64::from(value == 0));
                        assert_eq!(actual.registers[x86::SF], (value >> (bits - 1)) & 1);
                        assert_eq!(
                            actual.registers[x86::PF],
                            u64::from((value as u8).count_ones().is_multiple_of(2))
                        );
                        assert_eq!(actual.value, if kind == Alu::Cmp { left } else { value });
                    }
                }
            }
        }
    }
}

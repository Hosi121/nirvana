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

#[cfg(target_arch = "x86_64")]
#[test]
fn high_byte_reads_keep_static_slices_and_match_native_movzx_for_all_byte_values() {
    use nirvana::ir::UnaryOp;
    let op = UnaryOp::Extract {
        start: 8,
        width: Width::U8,
    };
    let mut compared = 0;
    for index in 0..4 {
        // MOVZX EAX, AH/CH/DH/BH; RET. No REX prefix is present.
        let program = x86::lift(&[0x0f, 0xb6, 0xc4 + index as u8, 0xc3], 0, 0).unwrap();
        assert!(program.uses_unary_operator(op));
        for byte in 0..=255u64 {
            for surround in [0, 0xabc1_2345_6789_00ef, u64::MAX] {
                let value = (surround & !0xff00) | (byte << 8);
                let actual: u64;
                unsafe {
                    std::arch::asm!("movzx ecx,ah", in("rax") value, lateout("rcx") actual, options(pure,nomem,nostack,preserves_flags));
                }
                let mut registers = vec![0x9371_cafe_7890_fedc; x86::REGISTER_COUNT];
                registers[index] = value;
                let result = program.execute(&registers, 2).unwrap();
                assert_eq!(result.value, actual);
                for (other, &original) in registers.iter().enumerate().take(16).skip(1) {
                    let expected = if other == x86::RSP {
                        original.wrapping_add(8)
                    } else {
                        original
                    };
                    assert_eq!(result.registers[other], expected);
                }
                compared += 1;
            }
        }
    }
    println!("{compared} native high-byte/IR observations across all four register aliases");
}

#[cfg(target_arch = "x86_64")]
#[test]
fn every_low_register_alias_keeps_its_width_and_matches_native_zero_extension() {
    use nirvana::ir::UnaryOp;
    let mut compared = 0;
    for width in [Width::U8, Width::U16, Width::U32] {
        for index in 0..16 {
            let mut code = Vec::new();
            if index >= 8 || width == Width::U8 && index >= 4 {
                code.push(0x40 | u8::from(index >= 8));
            }
            if width == Width::U32 {
                code.push(0x8b);
            } else {
                code.extend([0x0f, if width == Width::U8 { 0xb6 } else { 0xb7 }]);
            }
            code.extend([0xc0 | (index as u8 & 7), 0xc3]);
            let program = x86::lift(&code, 0, 0).unwrap();
            assert!(program.uses_unary_operator(UnaryOp::Extract { start: 0, width }));
            for low in 0..256u64 {
                for surround in [0, 0xa1b2_c3d4_8000_7f00, 0x1234_5678_ff00_0000, !255u64] {
                    let value = surround | low;
                    let actual: u64;
                    unsafe {
                        match width {
                            Width::U8 => {
                                std::arch::asm!("movzx ecx,al", in("rax") value, lateout("rcx") actual, options(pure,nomem,nostack,preserves_flags))
                            }
                            Width::U16 => {
                                std::arch::asm!("movzx ecx,ax", in("rax") value, lateout("rcx") actual, options(pure,nomem,nostack,preserves_flags))
                            }
                            Width::U32 => {
                                std::arch::asm!("mov ecx,eax", in("rax") value, lateout("rcx") actual, options(pure,nomem,nostack,preserves_flags))
                            }
                            Width::U64 => unreachable!(),
                        }
                    }
                    let mut registers = vec![0x9371_cafe_7890_fedc; x86::REGISTER_COUNT];
                    registers[index] = value;
                    let result = program.execute(&registers, 2).unwrap();
                    assert_eq!(result.value, actual, "{width:?}, register {index}");
                    for (other, &original) in registers.iter().enumerate().take(21) {
                        let expected = if other == x86::RAX {
                            actual
                        } else if other == x86::RSP {
                            original.wrapping_add(8)
                        } else {
                            original
                        };
                        assert_eq!(
                            result.registers[other], expected,
                            "preserved register {other}"
                        );
                    }
                    compared += 1;
                }
            }
        }
    }
    println!(
        "{compared} native/IR low-register projections with preserved machine registers and flags"
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
#[test]
fn implicit_accumulator_sign_extension_preserves_width_rules_and_flags() {
    use nirvana::ir::Width;
    for (bytes, from, to) in [
        (&[0x98][..], Width::U16, Width::U32),
        (&[0x66, 0x98], Width::U8, Width::U16),
        (&[0x48, 0x98], Width::U32, Width::U64),
        (&[0x49, 0x98], Width::U32, Width::U64),
    ] {
        let mut code = bytes.to_vec();
        code.push(0xc3);
        let program = nirvana::x86::lift(&code, 0, 0).unwrap();
        for value in [
            0,
            0x7f,
            0x80,
            0x7fff,
            0x8000,
            0x7fff_ffff,
            0x8000_0000,
            0x1234_5678_ffff_ffff,
            u64::MAX,
        ] {
            let mut input = vec![0; nirvana::x86::REGISTER_COUNT];
            input[0] = value;
            for (i, r) in input.iter_mut().enumerate().skip(16) {
                *r = i as u64;
            }
            let extended = match from {
                Width::U8 => (value as u8 as i8 as i64) as u64,
                Width::U16 => (value as u16 as i16 as i64) as u64,
                _ => (value as u32 as i32 as i64) as u64,
            };
            let expected = if to == Width::U16 {
                (value & !0xffff) | (extended & 0xffff)
            } else if to == Width::U32 {
                extended & 0xffff_ffff
            } else {
                extended
            };
            let report = program.execute(&input, 2).unwrap();
            assert_eq!(report.value, expected, "{bytes:02x?} {value:#x}");
            assert_eq!(&report.registers[16..], &input[16..]);
            assert_eq!(report.registers[8], input[8]);
        }
    }
}

#[cfg(target_arch = "x86_64")]
#[test]
fn partial_register_inserts_match_native_mov_and_preserve_other_machine_values() {
    let values = [
        0,
        1,
        127,
        128,
        255,
        256,
        65535,
        65536,
        u32::MAX as u64,
        1 << 63,
        u64::MAX,
        0x1234_5678_9abc_def0,
    ];
    let mut cases = Vec::new();
    for width in [Width::U8, Width::U16] {
        for destination in 0..16 {
            let mut code = Vec::new();
            if width == Width::U16 {
                code.push(0x66);
            }
            if destination >= 8 || width == Width::U8 && destination >= 4 {
                code.push(0x40 | u8::from(destination >= 8));
            }
            code.extend([
                if width == Width::U8 { 0x88 } else { 0x89 },
                0xc8 | (destination as u8 & 7),
                0xc3,
            ]);
            cases.push((width, 0, destination, code));
        }
    }
    for destination in 0..4 {
        cases.push((
            Width::U8,
            8,
            destination,
            vec![0x88, 0xcc + destination as u8, 0xc3],
        ));
    }
    let mut checked = 0;
    for (width, start, destination, code) in cases {
        let p = x86::lift(&code, 0, 0).unwrap();
        assert!(p.uses_operator(nirvana::ir::BinaryOp::Insert { start, width }));
        for base in values {
            for value in values {
                let mut regs = vec![0xcafe_9371_1122_7890; x86::REGISTER_COUNT];
                regs[x86::RCX] = value;
                regs[destination] = base;
                let mut actual = base;
                let rhs = regs[x86::RCX];
                unsafe {
                    match (start, width) {
                        (0, Width::U8) => {
                            std::arch::asm!("mov al,cl",inout("rax")actual,in("rcx")rhs,options(pure,nomem,nostack,preserves_flags))
                        }
                        (0, Width::U16) => {
                            std::arch::asm!("mov ax,cx",inout("rax")actual,in("rcx")rhs,options(pure,nomem,nostack,preserves_flags))
                        }
                        (8, Width::U8) => {
                            std::arch::asm!("mov ah,cl",inout("rax")actual,in("rcx")rhs,options(pure,nomem,nostack,preserves_flags))
                        }
                        _ => unreachable!(),
                    }
                }
                let report = p.execute(&regs, 2).unwrap();
                for (index, &old) in regs.iter().enumerate().take(21) {
                    let expected = if index == destination { actual } else { old };
                    let expected = if index == x86::RSP {
                        expected.wrapping_add(8)
                    } else {
                        expected
                    };
                    assert_eq!(
                        report.registers[index], expected,
                        "{width:?}/{start}/destination {destination}/register {index}"
                    );
                }
                checked += 1;
            }
        }
    }
    println!(
        "{checked} native partial-register writes with full architectural register/flag comparisons"
    );
}

#[cfg(target_arch = "x86_64")]
#[test]
fn zero_extended_memory_reads_expose_saved_slices_and_keep_all_fault_prefixes() {
    use nirvana::ir::{Expr, Place, Reg};
    // mov eax,[rdi]; mov [rdi+8],eax; xor eax,eax; movzx eax,[rdi+9]; ret
    let program = x86::lift(
        &[
            0x8b, 0x07, 0x89, 0x47, 0x08, 0x31, 0xc0, 0x0f, 0xb6, 0x47, 0x09, 0xc3,
        ],
        0,
        0,
    )
    .unwrap();
    let reload = program
        .instructions()
        .iter()
        .find(|i| i.address == 7)
        .unwrap();
    assert!(
        reload
            .assignments
            .iter()
            .any(|a| a.destination == Place::Register(Reg(x86::RAX))
                && matches!(
                    a.value,
                    Expr::Load {
                        width: Width::U8,
                        ..
                    }
                ))
    );
    let plan = nirvana::memory_values::MemoryValuePlan::analyze(&program)
        .expect("lifting preserves a root narrow Load");
    assert_eq!(plan.evidence().snapshot_values, 1);
    assert_eq!(plan.evidence().proved_loads, 1);
    let candidate = plan.lower(&program).unwrap();
    let mut checked = 0;
    for value in [
        0u64,
        1,
        255,
        256,
        65535,
        1 << 31,
        u64::MAX,
        0x1234_5678_9abc_def0,
    ] {
        let mut ram = [0xa5; 64];
        ram[..8].copy_from_slice(&value.to_le_bytes());
        let mut native_ram = ram;
        let result: u64;
        unsafe {
            std::arch::asm!("mov eax,dword ptr [{ptr}]","mov dword ptr [{ptr}+8],eax","xor eax,eax","movzx eax,byte ptr [{ptr}+9]",ptr=in(reg)native_ram.as_mut_ptr(),out("rax")result,options(nostack));
        }
        let mut regs = vec![0x9371_cafe_7890_fedc; program.register_count()];
        regs[x86::RDI] = 4096;
        let expected = program.execute_with_memory(&regs, 4096, &ram, 5).unwrap();
        assert_eq!(expected.value, result);
        assert_eq!(expected.memory, native_ram);
        for pointer in [4096, 4097, 4148, 4155, 4159, u64::MAX] {
            regs[x86::RDI] = pointer;
            let mut extended = regs.clone();
            extended.resize(candidate.register_count(), u64::MAX);
            for limit in 0..=6 {
                let before = program.run_with_memory(&regs, 4096, &ram, limit).unwrap();
                let mut after = candidate
                    .run_with_memory(&extended, 4096, &ram, limit)
                    .unwrap();
                after.state.registers.truncate(program.register_count());
                assert_eq!(before, after, "{value}/{pointer}/{limit}");
                checked += 1;
            }
        }
    }
    println!(
        "8 native memory/zero-extension comparisons; {checked} lifted saved-byte full-state/fault/budget observations"
    );
}

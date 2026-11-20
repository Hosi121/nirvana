use nirvana::ir::Width;
use nirvana::jump_tables::{self, MAX_ENTRIES};
use nirvana::x86::{self, DecodedInstruction, Operand, Operation, Register};

fn window(bytes: &[u8]) -> Vec<DecodedInstruction> {
    let mut out = Vec::new();
    let mut offset = 0;
    while offset < bytes.len() {
        let i = x86::decode_reference_at(&bytes[offset..], 0x1000 + offset as u64).unwrap();
        offset += i.size as usize;
        out.push(i);
    }
    out
}
fn rip_lea(bytes: &mut Vec<u8>, register: u8) {
    let next = 0x1000 + bytes.len() as u64 + 7;
    bytes.extend([0x48, 0x8d, 0x05 | (register << 3)]);
    bytes.extend(((0x2000i64 - next as i64) as i32).to_le_bytes());
}
fn absolute() -> Vec<u8> {
    vec![0x3e, 0xff, 0x24, 0xfd, 0x00, 0x20, 0, 0]
}

#[test]
fn signed_relative_entries_and_split_scaled_index_keep_negative_offsets() {
    for split in [false, true] {
        let mut code = Vec::new();
        if split {
            code.extend([0x48, 0x8d, 0x0c, 0xbd, 0, 0, 0, 0]);
        }
        rip_lea(&mut code, 2);
        if split {
            code.extend([0x8b, 0x04, 0x0a, 0x48, 0x98]);
        } else {
            code.extend([0x48, 0x63, 0x04, 0xba]);
        }
        code.extend([0x48, 0x01, 0xd0, 0x3e, 0xff, 0xe0]);
        let mut memory = Vec::new();
        for target in [0x1050i32, 0x1060] {
            memory.extend((target - 0x2000).to_le_bytes());
        }
        memory.extend([0; 8]);
        let c = jump_tables::discover(&window(&code), 0x2000, &memory, 0x1000..0x1100).unwrap();
        assert_eq!(
            (c.table, c.width, c.signed, c.bias),
            (0x2000, Width::U32, true, 0x2000)
        );
        assert_eq!(
            c.targets().into_iter().collect::<Vec<_>>(),
            [0x1050, 0x1060]
        );
    }
}

#[test]
fn mask_and_unsigned_fallthrough_guard_bound_the_initial_table_extent() {
    for prefix in [vec![0x83, 0xe7, 1], vec![0x48, 0x83, 0xff, 1, 0x77, 0x30]] {
        let mut bytes = prefix;
        bytes.extend(absolute());
        let mut memory = Vec::new();
        for target in [0x1050u64, 0x1060, 0x1070, 0x1080] {
            memory.extend(target.to_le_bytes());
        }
        let c = jump_tables::discover(&window(&bytes), 0x2000, &memory, 0x1000..0x1100).unwrap();
        assert_eq!((c.width, c.signed, c.bias), (Width::U64, false, 0));
        assert_eq!(c.entry_limit_hint, Some(2));
        assert_eq!(c.entries.len(), 2);
        let json = jump_tables::to_json(&[c], &[]).unwrap();
        assert!(json.contains("\"complete\":false"));
        assert!(json.contains("\"unknown_target\":true"));
    }
}

#[test]
fn guards_follow_compared_values_and_respect_narrow_register_views() {
    let mut memory = Vec::new();
    for target in [0x1050u64, 0x1060, 0x1070, 0x1080] {
        memory.extend(target.to_le_bytes());
    }
    for (prefix, hint, entries) in [
        // A low-32 comparison cannot bound the untouched high half of RDI.
        (vec![0x83, 0xff, 1, 0x77, 0x30], None, 4),
        // Writing EDI zero extends the compared low-32 value.
        (vec![0x83, 0xff, 1, 0x77, 0x30, 0x89, 0xff], Some(2), 2),
        // CMP facts survive flag-preserving copies and follow the old value,
        // even when the compared physical register has since been overwritten.
        (
            vec![
                0x83, 0xff, 1, 0x89, 0xf9, 0xbf, 99, 0, 0, 0, 0x77, 0x30, 0x89, 0xcf,
            ],
            Some(2),
            2,
        ),
        (vec![0x48, 0x83, 0xff, 1, 0x90, 0x77, 0x30], Some(2), 2),
    ] {
        let mut code = prefix;
        code.extend(absolute());
        let c = jump_tables::discover(&window(&code), 0x2000, &memory, 0x1000..0x1100).unwrap();
        assert_eq!(c.entry_limit_hint, hint);
        assert_eq!(c.entries.len(), entries);
    }
}

#[test]
fn a_32_bit_left_shift_masks_the_count_before_scaling_an_index() {
    let mut code = vec![0x83, 0xe7, 1, 0xc1, 0xe7, 32];
    code.extend(absolute());
    let memory: Vec<_> = [0x1050u64, 0x1060]
        .into_iter()
        .flat_map(u64::to_le_bytes)
        .collect();
    let c = jump_tables::discover(&window(&code), 0x2000, &memory, 0x1000..0x1100).unwrap();
    assert_eq!(c.entry_limit_hint, Some(2));
    assert_eq!(c.entries.len(), 2);
}

fn spill_guard(noise: &[u8], reload: &[u8]) -> Vec<u8> {
    let mut code = vec![0x48, 0x89, 0xe5, 0x48, 0x89, 0x7d, 0xf0];
    code.extend(noise);
    // SUB/JA checks the pre-subtraction index saved at [RBP-16].
    code.extend([0x48, 0x83, 0xef, 1, 0x77, 0x30]);
    code.extend(reload);
    code.extend(absolute());
    code
}

#[test]
fn saved_indices_carry_subtraction_guards_and_stores_invalidate_aliases() {
    let memory: Vec<_> = [0x1050u64, 0x1060, 0x1070, 0x1080]
        .into_iter()
        .flat_map(u64::to_le_bytes)
        .collect();
    for (noise, hint, entries) in [
        (vec![], Some(2), 2),
        // Same affine base, disjoint byte intervals.
        (vec![0x48, 0xc7, 0x45, 0xf8, 9, 0, 0, 0], Some(2), 2),
        // Partial overlap destroys the earlier eight-byte value.
        (vec![0xc7, 0x45, 0xf4, 9, 0, 0, 0], None, 4),
        // RSP aliases the copied RBP; different register names are insufficient.
        (vec![0xc7, 0x44, 0x24, 0xf4, 9, 0, 0, 0], None, 4),
        // A different unknown base may alias any saved value.
        (vec![0x48, 0x89, 0x06], None, 4),
        // Calls have unknown memory effects as well as register effects.
        (vec![0xe8, 0, 0, 0, 0], None, 4),
    ] {
        let code = spill_guard(&noise, &[0x48, 0x8b, 0x7d, 0xf0]);
        let c = jump_tables::discover(&window(&code), 0x2000, &memory, 0x1000..0x1100).unwrap();
        assert_eq!(c.entry_limit_hint, hint, "{noise:x?}");
        assert_eq!(c.entries.len(), entries, "{noise:x?}");
    }
    // A narrower reload gets its own truncated value, not the old 64-bit bound.
    let code = spill_guard(&[], &[0x8b, 0x7d, 0xf0]);
    let c = jump_tables::discover(&window(&code), 0x2000, &memory, 0x1000..0x1100).unwrap();
    assert_ne!(c.entry_limit_hint, Some(2));
    assert_eq!(c.entries.len(), 4);
}

#[test]
fn exact_spill_cache_has_a_bounded_lifetime() {
    let mut noise = Vec::new();
    for n in 0..33i32 {
        noise.extend([0x48, 0xc7, 0x85]);
        noise.extend((32 + n * 8).to_le_bytes());
        noise.extend(9u32.to_le_bytes());
    }
    let code = window(&spill_guard(&noise, &[0x48, 0x8b, 0x7d, 0xf0]));
    let memory = 0x1080u64.to_le_bytes().repeat(4);
    let result = jump_tables::discover_cfg(
        &code,
        code.last().unwrap().address,
        0x2000,
        &memory,
        0x1000..0x1200,
    );
    assert_eq!(result.candidates.len(), 1);
    assert_eq!(result.candidates[0].entry_limit_hint, None);
}

#[test]
fn sign_extension_preserves_address_identity_only_with_a_clear_sign_bit() {
    let memory = 0x1050u64.to_le_bytes().repeat(2);
    for bounded in [false, true] {
        let mut code = vec![0x89, 0xfe]; // ESI is a zero-extended copy of EDI.
        if bounded {
            code.extend([0x83, 0xe6, 1]);
        }
        code.extend([0x48, 0x63, 0xfe]); // RDI = sign_extend(ESI).
        rip_lea(&mut code, 0);
        code.extend([0x48, 0x89, 0x06]); // Store a pointer at [RSI].
        code.extend([0x48, 0x8b, 0x17]); // [RDI] need not be that same address.
        code.extend([0xff, 0x24, 0xca]); // JMP [RDX + RCX*8].
        let found = jump_tables::discover(&window(&code), 0x2000, &memory, 0x1000..0x1100);
        assert_eq!(found.is_some(), bounded);
    }
}

#[test]
fn opaque_scalar_operations_invalidate_only_their_ir_write_effects() {
    let memory: Vec<_> = [0x1050u64, 0x1060, 0x1070, 0x1080]
        .into_iter()
        .flat_map(u64::to_le_bytes)
        .collect();
    for (effect, hint) in [
        (vec![0x48, 0x0f, 0xc8], Some(2)), // BSWAP RAX preserves RBX and flags.
        (vec![0x48, 0xff, 0xc0], None),    // INC RAX changes flags, preserves RBX.
        (vec![0x48, 0x0f, 0xba, 0xe1, 0], None), // BT RCX,0 changes CF.
        (vec![0x58], Some(2)),             // POP RAX reads RAM and writes RSP, not RBX.
        (vec![0x48, 0xf7, 0xe1], None),    // MUL RCX writes RAX/RDX and flags.
        (vec![0x48, 0x0f, 0x44, 0xc3], Some(2)), // CMOVZ RAX,RBX preserves flags.
        (vec![0x48, 0x87, 0xc8], Some(2)), // XCHG RAX,RCX preserves RBX.
        (vec![0x0f, 0x94, 0x06], Some(2)), // SETZ [RSI] writes RAM, not flags.
    ] {
        let mut code = Vec::new();
        rip_lea(&mut code, 3);
        code.extend([0x48, 0x83, 0xff, 1]);
        code.extend(&effect);
        code.extend([0x77, 0x30, 0xff, 0x24, 0xfb]);
        let c = jump_tables::discover(&window(&code), 0x2000, &memory, 0x1000..0x1100).unwrap();
        assert_eq!(c.entry_limit_hint, hint, "{effect:x?}");
        assert_eq!(c.entries.len(), if hint.is_some() { 2 } else { 4 });
    }
    for effect in [
        vec![0x48, 0x0f, 0xcb],
        vec![0x48, 0x87, 0xd8],
        vec![0xe8, 0, 0, 0, 0],
    ] {
        let mut code = Vec::new();
        rip_lea(&mut code, 3);
        code.extend(&effect);
        code.extend([0xff, 0x24, 0xfb]);
        assert!(
            jump_tables::discover(&window(&code), 0x2000, &memory, 0x1000..0x1100).is_none(),
            "{effect:x?}"
        );
    }
    // A pure write to an unrelated GPR keeps saved values, while an opaque
    // memory write invalidates them even when no GPR is changed.
    for (effect, hint) in [
        (vec![0x48, 0x0f, 0xc8], Some(2)),
        (vec![0x0f, 0x94, 0x06], None),
    ] {
        let code = spill_guard(&effect, &[0x48, 0x8b, 0x7d, 0xf0]);
        let c = jump_tables::discover(&window(&code), 0x2000, &memory, 0x1000..0x1100).unwrap();
        assert_eq!(c.entry_limit_hint, hint);
    }
}

#[test]
fn malformed_opaque_effect_operands_decline_before_lifting() {
    let memory = 0x1050u64.to_le_bytes().repeat(2);
    let bad = Register {
        index: 255,
        width: Width::U64,
        shift: 0,
    };
    let high = Register {
        index: 0,
        width: Width::U64,
        shift: 255,
    };
    for operation in [
        Operation::ByteSwap { destination: bad },
        Operation::Pop(bad),
        Operation::Unary {
            kind: nirvana::x86::Unary::Inc,
            destination: Operand::Register(high),
        },
        Operation::Set {
            condition: 255,
            destination: Operand::Register(Register {
                index: 0,
                width: Width::U8,
                shift: 0,
            }),
        },
        Operation::Imul {
            destination: bad,
            left: Operand::Immediate(1),
            right: Operand::Immediate(2),
        },
    ] {
        let mut code = vec![DecodedInstruction {
            address: 0x1000,
            size: 1,
            operation,
        }];
        let mut branch = window(&absolute())[0];
        branch.address = 0x1001;
        code.push(branch);
        assert!(jump_tables::discover(&code, 0x2000, &memory, 0x1000..0x1100).is_none());
    }
}

#[test]
fn read_provenance_tracks_the_table_load_through_target_spills() {
    let mut bytes = Vec::new();
    rip_lea(&mut bytes, 2);
    let producer = 0x1000 + bytes.len() as u64;
    bytes.extend([0x48, 0x63, 0x04, 0xba]);
    bytes.extend([0x48, 0x89, 0x44, 0x24, 0xf8, 0x48, 0x8b, 0x44, 0x24, 0xf8]);
    bytes.extend([0x48, 0x01, 0xd0, 0x3e, 0xff, 0xe0]);
    let memory: Vec<_> = [0x1050i32, 0x1060]
        .into_iter()
        .flat_map(|t| (t - 0x2000).to_le_bytes())
        .collect();
    let table = jump_tables::discover(&window(&bytes), 0x2000, &memory, 0x1000..0x1100).unwrap();
    assert_eq!(table.read_sites.len(), 1);
    assert_eq!(table.read_sites[0].instruction, producer);
    assert_eq!(table.read_sites[0].next, producer + 4);
    assert!(table.read_sites[0].address_expr().is_some());
    assert!(
        jump_tables::to_json(std::slice::from_ref(&table), &[])
            .unwrap()
            .contains("\"read_sites\":[")
    );
    let mut invalid = table.clone();
    invalid.read_sites = vec![invalid.read_sites[0]; jump_tables::MAX_READ_SITES + 1];
    assert!(jump_tables::to_json(&[invalid], &[]).is_err());
}

#[test]
fn repeated_targets_are_retained_as_distinct_entries_and_coverage_stays_open_at_the_cap() {
    let memory = 0x1050u64.to_le_bytes().repeat(MAX_ENTRIES + 1);
    let c = jump_tables::discover(&window(&absolute()), 0x2000, &memory, 0x1000..0x1100).unwrap();
    assert_eq!(c.entries.len(), MAX_ENTRIES);
    assert_eq!(c.targets().len(), 1);
    assert!(c.reached_entry_limit);
    let mut oversized = c.clone();
    oversized.entries.push(c.entries[0].clone());
    assert!(jump_tables::to_json(&[oversized], &[]).is_err());
}

#[test]
fn clobbers_invalid_entries_truncation_and_malformed_windows_decline() {
    let mut code = Vec::new();
    rip_lea(&mut code, 2);
    code.extend([0x48, 0x63, 0x04, 0xba, 0x48, 0x01, 0xd0]);
    // An unmodeled register write cannot leave the earlier pointer expression.
    code.extend([0x48, 0xff, 0xc0, 0xff, 0xe0]);
    let mut relative = Vec::new();
    for n in [0x1050i32, 0x1060] {
        relative.extend((n - 0x2000).to_le_bytes());
    }
    assert!(jump_tables::discover(&window(&code), 0x2000, &relative, 0x1000..0x1100).is_none());
    let memory = 0x1050u64.to_le_bytes().repeat(2);
    let good = window(&absolute());
    assert!(jump_tables::discover(&good, 0x2000, &memory[..7], 0x1000..0x1100).is_none());
    assert!(jump_tables::discover(&good, 0x2000, &[0; 16], 0x1000..0x1100).is_none());
    let mut bad = good.clone();
    bad[0].operation = Operation::IndirectJump(Operand::Register(Register {
        index: 255,
        width: Width::U64,
        shift: 0,
    }));
    assert!(jump_tables::discover(&bad, 0x2000, &memory, 0x1000..0x1100).is_none());
    bad = good.clone();
    bad[0].size = 0;
    assert!(jump_tables::discover(&bad, 0x2000, &memory, 0x1000..0x1100).is_none());
    assert!(jump_tables::discover(&good, u64::MAX - 4, &memory, 0x1000..0x1100).is_none());
}

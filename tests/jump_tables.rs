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

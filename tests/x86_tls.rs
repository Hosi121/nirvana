use nirvana::{
    ir::Width,
    x86::{self, Operand, Operation},
};

#[test]
fn fs_guard_read_profiles_keep_original_length_width_destination_and_alu() {
    for (opcode, kind) in [
        (0x8b, None),
        (0x2b, Some(x86::Alu::Sub)),
        (0x33, Some(x86::Alu::Xor)),
        (0x3b, Some(x86::Alu::Cmp)),
    ] {
        let bytes = [0x64, 0x48, opcode, 0x04, 0x25, 0x28, 0, 0, 0];
        assert!(x86::decode_at(&bytes, 0x1000).is_err());
        assert!(x86::decode_reference_at(&bytes, 0x1000).is_err());
        for slot in [0, 0x12345028, u64::MAX - 7] {
            let decoded = x86::decode_fs_guard_at(&bytes, 0x1000, slot).unwrap();
            assert_eq!(decoded.address, 0x1000);
            assert_eq!(decoded.size, 9);
            let (destination, source) = match decoded.operation {
                Operation::Mov {
                    destination,
                    source,
                } if kind.is_none() => (destination, source),
                Operation::Alu {
                    kind: actual,
                    destination,
                    source,
                } if Some(actual) == kind => (destination, source),
                other => panic!("unexpected {other:?}"),
            };
            assert!(
                matches!(destination,Operand::Register(r) if r.index==0 && r.width==Width::U64)
            );
            let Operand::Memory { address, width } = source else {
                panic!()
            };
            assert_eq!(width, Width::U64);
            assert_eq!(address.displacement as u64, slot);
            assert!(address.base.is_none() && address.index.is_none() && !address.rip_relative);
        }
    }
}

#[test]
fn tls_profile_rejects_other_segments_offsets_widths_stores_and_truncations() {
    let valid = [0x64, 0x48, 0x8b, 0x04, 0x25, 0x28, 0, 0, 0];
    for len in 0..valid.len() {
        assert!(x86::decode_fs_guard_at(&valid[..len], 0x1000, 0x2028).is_err());
    }
    for (index, value) in [(0, 0x65), (1, 0x40), (2, 0x89), (4, 0x20), (5, 0x30)] {
        let mut bytes = valid;
        bytes[index] = value;
        assert!(
            x86::decode_fs_guard_at(&bytes, 0x1000, 0x2028).is_err(),
            "index={index}"
        );
    }
    assert!(x86::decode_fs_guard_at(&valid, u64::MAX, 0x2028).is_err());
    let repeated = [&[0x64][..], &valid].concat();
    assert!(x86::decode_fs_guard_at(&repeated, 0x1000, 0x2028).is_err());
}

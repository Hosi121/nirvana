use nirvana::cfg::{Cfg, EdgeKind, Flow, Target};
use nirvana::ir::Width;
use nirvana::x86::{self, Addressing, LiftError, Operand, Operation, Register};

fn reg(index: u8) -> Operand {
    Operand::Register(Register {
        index,
        width: Width::U64,
        shift: 0,
    })
}

#[test]
fn reference_calls_use_signed_rel32_from_the_complete_instruction() {
    for (bytes, target) in [
        (&[0xe8, 0x10, 0, 0, 0][..], 0x1015),
        (&[0xe8, 0xfb, 0xff, 0xff, 0xff], 0x1000),
        (&[0xe8, 0, 0, 0, 0x80], 0xffff_ffff_8000_1005),
        (&[0xe8, 0xff, 0xff, 0xff, 0x7f], 0x8000_1004),
        (&[0x48, 0xe8, 0xfa, 0xff, 0xff, 0xff], 0x1000),
    ] {
        let mut with_suffix = bytes.to_vec();
        with_suffix.push(0xc3);
        let decoded = x86::decode_reference_at(&with_suffix, 0x1000).unwrap();
        assert_eq!(decoded.address, 0x1000);
        assert_eq!(usize::from(decoded.size), bytes.len());
        assert_eq!(decoded.operation, Operation::Call(target));
        assert_eq!(decoded.layout().flow, Flow::Next);
    }
}

#[test]
fn executable_decoding_and_lifting_keep_rejecting_reference_control_transfers() {
    for bytes in [
        &[0xe8, 0, 0, 0, 0][..],
        &[0x48, 0xe8, 0, 0, 0, 0],
        &[0xff, 0xd0],
        &[0x41, 0xff, 0xe0],
        &[0xff, 0x15, 0, 0, 0, 0],
        &[0xff, 0x25, 0, 0, 0, 0],
    ] {
        assert!(x86::decode_reference_at(bytes, 0x1000).is_ok());
        assert!(x86::decode_at(bytes, 0x1000).is_err());
        let mut function = bytes.to_vec();
        function.push(0xc3);
        assert!(x86::decode_reachable(&function, 0x1000, 0x1000).is_err());
        assert!(matches!(
            x86::lift(&function, 0x1000, 0x1000),
            Err(LiftError::Decode(_))
        ));
    }
}

#[test]
fn indirect_registers_are_near64_with_or_without_rex_w() {
    for prefix in [None, Some(0x40), Some(0x44), Some(0x48), Some(0x4c)] {
        for extension in 0..=1 {
            if prefix.is_none() && extension != 0 {
                continue;
            }
            for index in 0..8 {
                for (group, call) in [(2, true), (4, false)] {
                    let mut bytes = Vec::new();
                    if let Some(rex) = prefix {
                        bytes.push(rex | extension);
                    }
                    bytes.extend([0xff, 0xc0 | (group << 3) | index]);
                    let instruction = x86::decode_reference_at(&bytes, 0).unwrap();
                    let operand = reg(index | (extension << 3));
                    assert_eq!(
                        instruction.operation,
                        if call {
                            Operation::IndirectCall(operand)
                        } else {
                            Operation::IndirectJump(operand)
                        },
                        "{bytes:02x?}"
                    );
                    assert_eq!(usize::from(instruction.size), bytes.len());
                }
            }
        }
    }
}

#[test]
fn indirect_memory_reuses_rip_sib_and_signed_displacements() {
    for (bytes, call, expected) in [
        (
            &[0xff, 0x10][..],
            true,
            Addressing {
                base: Some(0),
                index: None,
                scale: 1,
                displacement: 0,
                rip_relative: false,
            },
        ),
        (
            &[0xff, 0x15, 0xfc, 0xff, 0xff, 0xff],
            true,
            Addressing {
                base: None,
                index: None,
                scale: 1,
                displacement: -4,
                rip_relative: true,
            },
        ),
        (
            &[0x49, 0xff, 0x25, 0, 0, 0, 0x80],
            false,
            Addressing {
                base: None,
                index: None,
                scale: 1,
                displacement: i64::from(i32::MIN),
                rip_relative: true,
            },
        ),
        (
            &[0x4f, 0xff, 0x54, 0xac, 0xe0],
            true,
            Addressing {
                base: Some(12),
                index: Some(13),
                scale: 4,
                displacement: -32,
                rip_relative: false,
            },
        ),
        (
            &[0x4f, 0xff, 0xa4, 0xac, 0, 1, 0, 0],
            false,
            Addressing {
                base: Some(12),
                index: Some(13),
                scale: 4,
                displacement: 256,
                rip_relative: false,
            },
        ),
        (
            &[0x43, 0xff, 0x14, 0xe5, 0x78, 0x56, 0x34, 0x12],
            true,
            Addressing {
                base: None,
                index: Some(12),
                scale: 8,
                displacement: 0x1234_5678,
                rip_relative: false,
            },
        ),
        (
            &[0xff, 0x24, 0x25, 0xfc, 0xff, 0xff, 0xff],
            false,
            Addressing {
                base: None,
                index: None,
                scale: 1,
                displacement: -4,
                rip_relative: false,
            },
        ),
    ] {
        let instruction = x86::decode_reference_at(bytes, 0x1000).unwrap();
        let operand = Operand::Memory {
            address: expected,
            width: Width::U64,
        };
        assert_eq!(
            instruction.operation,
            if call {
                Operation::IndirectCall(operand)
            } else {
                Operation::IndirectJump(operand)
            },
            "{bytes:02x?}"
        );
        assert_eq!(usize::from(instruction.size), bytes.len());
    }
}

#[test]
fn indirect_jumps_have_a_terminal_unknown_cfg_edge_and_calls_fall_through() {
    let jump = x86::decode_reference_at(&[0xff, 0xe0], 0x1000).unwrap();
    assert_eq!(jump.layout().flow, Flow::IndirectJump);
    let cfg = Cfg::build(0x1000, vec![jump.layout()]).unwrap();
    let edges = &cfg.block(cfg.entry()).successors;
    assert_eq!(edges.len(), 1);
    assert_eq!(edges[0].kind, EdgeKind::Indirect);
    assert_eq!(edges[0].target, Target::Unknown);
    for bytes in [&[0xe8, 0, 0, 0, 0][..], &[0xff, 0xd0]] {
        assert_eq!(
            x86::decode_reference_at(bytes, 0).unwrap().layout().flow,
            Flow::Next
        );
    }
}

#[test]
fn reference_control_transfers_reject_legacy_and_ambiguous_prefixes() {
    for prefix in [
        &[0x66][..],
        &[0x26],
        &[0x2e],
        &[0x36],
        &[0x64],
        &[0x65],
        &[0x67],
        &[0xf0],
        &[0xf2],
        &[0xf3],
        &[0x66, 0x48],
        &[0x48, 0x66],
        &[0x40, 0x40],
        &[0x48, 0x41],
        &[0x41, 0x48],
        &[0x3e, 0x3e],
        &[0x3e, 0x2e],
        &[0x2e, 0x3e],
    ] {
        for body in [
            &[0xe8, 0, 0, 0, 0][..],
            &[0xff, 0xd0],
            &[0xff, 0xe0],
            &[0xff, 0x15, 0, 0, 0, 0],
            &[0xff, 0x25, 0, 0, 0, 0],
        ] {
            let bytes = [prefix, body].concat();
            assert!(x86::decode_reference_at(&bytes, 0).is_err(), "{bytes:02x?}");
        }
    }
}

#[test]
fn notrack_near_indirect_transfers_preserve_operands_and_scalar_policy() {
    for bytes in [
        &[0xff, 0xe0][..],
        &[0x41, 0xff, 0xe3],
        &[0xff, 0xd0],
        &[0xff, 0x25, 0xfc, 0xff, 0xff, 0xff],
        &[0x49, 0xff, 0x24, 0xc0],
    ] {
        let expected = x86::decode_reference_at(bytes, 0x1000).unwrap();
        let prefixed = [&[0x3e][..], bytes].concat();
        let actual = x86::decode_reference_at(&prefixed, 0x1000).unwrap();
        assert_eq!(actual.operation, expected.operation);
        assert_eq!(actual.size, expected.size + 1);
        assert!(x86::decode_at(&prefixed, 0x1000).is_err());
    }
    assert!(x86::decode_reference_at(&[0x3e, 0xe8, 0, 0, 0, 0], 0).is_err());
    assert!(x86::decode_reference_at(&[0x48, 0x3e, 0xff, 0xe0], 0).is_err());
}

#[test]
fn reference_policy_rejects_far_and_invalid_control_encodings() {
    for bytes in [
        &[0xff, 0x18][..], // Far call through memory.
        &[0xff, 0xd8],     // Invalid register far call.
        &[0xff, 0x28],     // Far jump through memory.
        &[0xff, 0xe8],     // Invalid register far jump.
        &[0xff, 0xf8],     // Reserved FF /7.
        &[0xfe, 0xd0],     // FE has no call group.
        &[0xfe, 0xe0],     // FE has no jump group.
        &[0x9a, 0, 0, 0, 0, 0, 0],
        &[0xea, 0, 0, 0, 0, 0, 0],
    ] {
        assert!(x86::decode_reference_at(bytes, 0).is_err(), "{bytes:02x?}");
    }
}

#[test]
fn reference_forms_reject_every_truncated_operand() {
    for bytes in [
        &[0xe8, 0, 0, 0, 0][..],
        &[0x48, 0xe8, 0, 0, 0, 0],
        &[0xff, 0xd0],
        &[0x41, 0xff, 0xe0],
        &[0xff, 0x15, 0, 0, 0, 0],
        &[0x49, 0xff, 0x25, 0, 0, 0, 0],
        &[0x4f, 0xff, 0x54, 0xac, 0xe0],
        &[0x4f, 0xff, 0xa4, 0xac, 0, 1, 0, 0],
    ] {
        for length in 0..bytes.len() {
            let error = x86::decode_reference_at(&bytes[..length], 0x1000).unwrap_err();
            assert_eq!(error.address, 0x1000, "{bytes:02x?}, length {length}");
        }
        assert!(x86::decode_reference_at(bytes, 0x1000).is_ok());
    }
}

#[test]
fn reference_decoding_preserves_instruction_length_and_address_bounds() {
    let mut longest_nop = vec![0x66; 14];
    longest_nop.push(0x90);
    assert_eq!(x86::decode_reference_at(&longest_nop, 0).unwrap().size, 15);
    let mut oversized = vec![0x66; 15];
    oversized.push(0x90);
    assert!(x86::decode_reference_at(&oversized, 0).is_err());
    assert!(x86::decode_reference_at(&[0x40; 16], 0).is_err());

    for bytes in [
        &[0xe8, 0, 0, 0, 0][..],
        &[0x48, 0xe8, 0, 0, 0, 0],
        &[0xff, 0xd0],
        &[0xff, 0xe0],
        &[0xff, 0x15, 0, 0, 0, 0],
    ] {
        let last_start = u64::MAX - bytes.len() as u64;
        assert!(x86::decode_reference_at(bytes, last_start).is_ok());
        let error = x86::decode_reference_at(bytes, last_start + 1).unwrap_err();
        assert_eq!(error.address, last_start + 1);
        assert!(error.reason.contains("overflow"));
    }
    // Relative targets retain the existing decoder's architectural wrapping.
    assert_eq!(
        x86::decode_reference_at(&[0xe8, 0xf6, 0xff, 0xff, 0xff], 0)
            .unwrap()
            .operation,
        Operation::Call(u64::MAX - 4)
    );
}

#[test]
fn opt_in_keeps_existing_instruction_decoding_identical() {
    for bytes in [
        &[0x48, 0x8b, 0x05, 0x10, 0, 0, 0][..],
        &[0x66, 0x0f, 0xaf, 0xc0],
        &[0x48, 0x41, 0x8b, 0xc0],
        &[0x2e, 0x90],
        &[0xf3, 0x0f, 0x1e, 0xfa],
        &[0xff, 0xc0],
        &[0xff, 0xc8],
        &[0xff, 0xf0],
        &[0xe9, 0xfb, 0xff, 0xff, 0xff],
        &[0xeb, 0xfe],
        &[0x74, 0],
        &[0xc3],
    ] {
        assert_eq!(
            x86::decode_reference_at(bytes, 0x1000),
            x86::decode_at(bytes, 0x1000),
            "{bytes:02x?}"
        );
    }
}

#[test]
fn reference_decoding_arbitrary_bytes_and_short_slices_never_panics() {
    let mut state = 0x1248_369a_bcde_f001u64;
    for _ in 0..512 {
        let mut bytes = [0; 16];
        for byte in &mut bytes {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            *byte = state as u8;
        }
        for length in 0..=16 {
            for address in [0, 0x1000, u64::MAX - 8] {
                let _ = x86::decode_reference_at(&bytes[..length], address);
            }
        }
    }
}

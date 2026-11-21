use nirvana::eh_frame;

fn record(out: &mut Vec<u8>, body: &[u8]) -> usize {
    let start = out.len();
    out.extend_from_slice(&(body.len() as u32).to_le_bytes());
    out.extend_from_slice(body);
    start
}
fn common(out: &mut Vec<u8>, version: u8, augmentation: &[u8], payload: &[u8]) -> usize {
    let mut body = vec![0, 0, 0, 0, version];
    body.extend_from_slice(augmentation);
    body.extend_from_slice(&[0, 1, 0x78, 16]); // NUL, code_align=1, data_align=-8, RIP
    if augmentation.first() == Some(&b'z') {
        body.push(payload.len() as u8);
        body.extend_from_slice(payload);
    }
    body.extend_from_slice(&[0x0c, 7, 8]); // opaque CFI
    record(out, &body)
}
fn fde(out: &mut Vec<u8>, cie: usize, pc: &[u8], size: &[u8], augmented: bool) -> usize {
    let start = out.len();
    let mut body = ((start + 4 - cie) as u32).to_le_bytes().to_vec();
    body.extend_from_slice(pc);
    body.extend_from_slice(size);
    if augmented {
        body.push(0);
    }
    body.extend_from_slice(&[0x0e, 16]);
    record(out, &body)
}
fn relative() -> (Vec<u8>, usize, usize) {
    let mut data = Vec::new();
    let cie = common(&mut data, 1, b"zR", &[0x1b]);
    let field = data.len() as i32 + 8;
    let a = fde(
        &mut data,
        cie,
        &(0x800i32 - field).to_le_bytes(),
        &0x40i32.to_le_bytes(),
        true,
    );
    let field = data.len() as i32 + 8;
    let b = fde(
        &mut data,
        cie,
        &(-0x100i32 - field).to_le_bytes(),
        &0x20i32.to_le_bytes(),
        true,
    );
    data.extend_from_slice(&[0; 8]);
    (data, a, b)
}

#[test]
fn pc_relative_start_uses_field_address_and_range_is_absolute() {
    let (data, a, b) = relative();
    for base in [0x1000, 0x1234_5678_0000] {
        assert_eq!(
            eh_frame::read(&data, base).unwrap(),
            vec![
                eh_frame::Region {
                    address: base + 0x800,
                    size: 0x40,
                    record: a
                },
                eh_frame::Region {
                    address: base - 0x100,
                    size: 0x20,
                    record: b
                },
            ]
        );
    }
}

#[test]
fn fixed_width_and_leb_encodings_accept_their_exact_boundaries() {
    for (encoding, pc, size, expected_pc, expected_size) in [
        (2, vec![0xff, 0x7f], vec![0x20, 0], 32767, 32),
        (
            3,
            0x1234_5678u32.to_le_bytes().to_vec(),
            64u32.to_le_bytes().to_vec(),
            0x1234_5678,
            64,
        ),
        (
            4,
            (u64::MAX - 8).to_le_bytes().to_vec(),
            8u64.to_le_bytes().to_vec(),
            u64::MAX - 8,
            8,
        ),
        (
            10,
            1234i16.to_le_bytes().to_vec(),
            24i16.to_le_bytes().to_vec(),
            1234,
            24,
        ),
        (
            11,
            2345i32.to_le_bytes().to_vec(),
            32i32.to_le_bytes().to_vec(),
            2345,
            32,
        ),
        (
            12,
            3456i64.to_le_bytes().to_vec(),
            48i64.to_le_bytes().to_vec(),
            3456,
            48,
        ),
        (1, [vec![0xff; 9], vec![1]].concat(), vec![0], u64::MAX, 0),
        (9, vec![0xff, 0x00], vec![0x3f], 127, 63),
    ] {
        let mut data = Vec::new();
        let cie = common(&mut data, 1, b"zR", &[encoding]);
        fde(&mut data, cie, &pc, &size, true);
        let regions = eh_frame::read(&data, 0).unwrap();
        if expected_size == 0 {
            assert!(regions.is_empty());
        } else {
            assert_eq!(
                (regions[0].address, regions[0].size),
                (expected_pc, expected_size)
            );
        }
    }
    // Both extreme signed LEB values are valid; only the negative PC/range
    // is invalid. Check data alignment independently of address interpretation.
    for alignment in [
        [vec![0x80; 9], vec![0x7f]].concat(),
        [vec![0xff; 9], vec![0]].concat(),
    ] {
        let mut body = vec![0, 0, 0, 0, 3, 0, 1];
        body.extend_from_slice(&alignment);
        body.extend_from_slice(&[0x80, 1]); // v3 return register is ULEB128
        let mut data = Vec::new();
        record(&mut data, &body);
        assert!(eh_frame::read(&data, 0).unwrap().is_empty());
    }
}

#[test]
fn absolute_default_and_augmented_signed_leb_and_personality_are_consumed() {
    let mut data = Vec::new();
    let first = common(&mut data, 1, b"", &[]);
    fde(
        &mut data,
        first,
        &0x401000u64.to_le_bytes(),
        &0x120u64.to_le_bytes(),
        false,
    );
    // An opaque indirect PC-relative personality can be skipped without RAM.
    let second = common(
        &mut data,
        3,
        b"zPLRS",
        &[0x9b, 0xff, 0xff, 0xff, 0x7f, 0xff, 0x19],
    );
    let field = data.len() as u64 + 8;
    fde(&mut data, second, &[0x78], &[0x3f], true); // start=-8, range=63
    let regions = eh_frame::read(&data, 0x2000).unwrap();
    assert_eq!((regions[0].address, regions[0].size), (0x401000, 0x120));
    assert_eq!(
        (regions[1].address, regions[1].size),
        (0x2000 + field - 8, 63)
    );
    let mut empty = Vec::new();
    let cie = common(&mut empty, 1, b"zR", &[0]);
    fde(
        &mut empty,
        cie,
        &7u64.to_le_bytes(),
        &0u64.to_le_bytes(),
        true,
    );
    assert!(eh_frame::read(&empty, 0).unwrap().is_empty());
}

#[test]
fn malformed_lengths_references_encodings_and_ranges_are_rejected() {
    let (original, a, _) = relative();
    for length in [1, 3, 6, a + 1, a + 7, original.len() - 7] {
        assert!(
            eh_frame::read(&original[..length], 0x1000).is_err(),
            "length{length}"
        );
    }
    for (offset, value) in [
        (0, u32::MAX),
        (0, 3),
        (0, 1_000_000),
        (a + 4, u32::MAX),
        (a + 4, 1),
        (a + 4, (a + 3) as u32),
        (a + 12, u32::MAX),
    ] {
        let mut data = original.clone();
        data[offset..offset + 4].copy_from_slice(&value.to_le_bytes());
        assert!(
            eh_frame::read(&data, 0x1000).is_err(),
            "offset{offset} value{value}"
        );
    }
    let mut data = original.clone();
    *data.last_mut().unwrap() = 1;
    assert!(eh_frame::read(&data, 0x1000).is_err());
    assert!(eh_frame::read(&original, u64::MAX - 4).is_err());
    assert!(eh_frame::read(&original, 0).is_err()); // negative second PC
    for encoding in [0xff, 0x9b, 0x2b, 0x3b, 0x4b, 0x5b, 5, 8, 13] {
        let mut data = Vec::new();
        common(&mut data, 1, b"zR", &[encoding]);
        assert!(eh_frame::read(&data, 0).is_err(), "encoding{encoding:x}");
    }
    for (version, aug, payload) in [
        (4, &b"zR"[..], &b"\x1b"[..]),
        (1, &b"eh"[..], &b""[..]),
        (1, &b"zX"[..], &b""[..]),
        (1, &b"zRR"[..], &b"\x1b\x1b"[..]),
        (1, &b"zP"[..], &b"\xff"[..]),
        (1, &b"zR"[..], &b""[..]),
    ] {
        let mut data = Vec::new();
        common(&mut data, version, aug, payload);
        assert!(eh_frame::read(&data, 0).is_err());
    }
    let mut data = Vec::new();
    let cie = common(&mut data, 1, b"", &[]);
    fde(
        &mut data,
        cie,
        &(u64::MAX - 8).to_le_bytes(),
        &16u64.to_le_bytes(),
        false,
    );
    assert!(eh_frame::read(&data, 0).is_err());
}

#[test]
fn leb_and_augmentation_bounds_and_work_caps_are_enforced() {
    for leb in [
        &[0x80; 10][..],
        &[0xff; 9].iter().copied().chain([2]).collect::<Vec<_>>()[..],
    ] {
        let mut body = vec![0, 0, 0, 0, 1, 0];
        body.extend_from_slice(leb);
        body.extend_from_slice(&[0x78, 16]);
        let mut data = Vec::new();
        record(&mut data, &body);
        assert!(eh_frame::read(&data, 0).is_err());
    }
    let mut body = vec![0, 0, 0, 0, 1, b'z', b'R', 0, 1, 0x78, 16];
    body.extend_from_slice(&[0xff; 10]);
    let mut data = Vec::new();
    record(&mut data, &body);
    assert!(eh_frame::read(&data, 0).is_err());
    let mut data = Vec::new();
    for _ in 0..4097 {
        common(&mut data, 1, b"", &[]);
    }
    assert!(
        eh_frame::read(&data, 0)
            .unwrap_err()
            .reason
            .contains("CIE count")
    );
    let mut data = Vec::new();
    let cie = common(&mut data, 1, b"", &[]);
    for _ in 0..65_536 {
        fde(
            &mut data,
            cie,
            &1u64.to_le_bytes(),
            &1u64.to_le_bytes(),
            false,
        );
    }
    assert!(
        eh_frame::read(&data, 0)
            .unwrap_err()
            .reason
            .contains("record count")
    );
    assert!(eh_frame::read(&vec![0; 4 * 1024 * 1024 + 1], 0).is_err());
}

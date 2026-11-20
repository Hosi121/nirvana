use nirvana::linked_elf::{self, BinaryError, FunctionOrigin, LinkedOptions};

fn put16(data: &mut [u8], at: usize, value: u16) {
    data[at..at + 2].copy_from_slice(&value.to_le_bytes());
}
fn put32(data: &mut [u8], at: usize, value: u32) {
    data[at..at + 4].copy_from_slice(&value.to_le_bytes());
}
fn put64(data: &mut [u8], at: usize, value: u64) {
    data[at..at + 8].copy_from_slice(&value.to_le_bytes());
}
fn section(
    data: &mut [u8],
    index: usize,
    name: u32,
    kind: u32,
    flags: u64,
    location: (u64, u64),
    size: u64,
) {
    let (address, offset) = location;
    let at = 0x800 + index * 64;
    put32(data, at, name);
    put32(data, at + 4, kind);
    put64(data, at + 8, flags);
    put64(data, at + 16, address);
    put64(data, at + 24, offset);
    put64(data, at + 32, size);
}
fn frames(regions: &[(u64, u32)]) -> Vec<u8> {
    let body = [0, 0, 0, 0, 1, b'z', b'R', 0, 1, 0x78, 16, 1, 0x1b];
    let mut data = (body.len() as u32).to_le_bytes().to_vec();
    data.extend_from_slice(&body);
    for &(address, size) in regions {
        let record = data.len();
        data.extend_from_slice(&13u32.to_le_bytes());
        data.extend_from_slice(&((record + 4) as u32).to_le_bytes());
        data.extend_from_slice(
            &((address as i64 - (0x500 + record + 8) as i64) as i32).to_le_bytes(),
        );
        data.extend_from_slice(&size.to_le_bytes());
        data.push(0);
    }
    data.extend_from_slice(&[0; 4]);
    data
}
fn fixture(regions: &[(u64, u32)]) -> Vec<u8> {
    let mut data = vec![0; 0x1000];
    data[..7].copy_from_slice(b"\x7fELF\x02\x01\x01");
    put16(&mut data, 16, 3);
    put16(&mut data, 18, 62);
    put32(&mut data, 20, 1);
    put64(&mut data, 32, 64);
    put64(&mut data, 40, 0x800);
    put16(&mut data, 52, 64);
    put16(&mut data, 54, 56);
    put16(&mut data, 56, 1);
    put16(&mut data, 58, 64);
    put16(&mut data, 60, 4);
    put16(&mut data, 62, 2);
    put32(&mut data, 64, 1);
    put32(&mut data, 68, 7);
    put64(&mut data, 96, 0x1000);
    put64(&mut data, 104, 0x1100);
    put64(&mut data, 112, 0x1000);
    data[0x400..0x440].fill(0x90);
    data[0x40f] = 0xc3;
    data[0x42f] = 0xc3;
    let names = b"\0.text\0.shstrtab\0.eh_frame\0.strtab\0.symtab\0";
    data[0x700..0x700 + names.len()].copy_from_slice(names);
    section(&mut data, 1, 1, 1, 6, (0x400, 0x400), 0x40);
    section(&mut data, 2, 7, 3, 0, (0, 0x700), names.len() as u64);
    let frames = frames(regions);
    data[0x500..0x500 + frames.len()].copy_from_slice(&frames);
    section(&mut data, 3, 17, 1, 2, (0x500, 0x500), frames.len() as u64);
    data
}
fn options(bias: u64) -> LinkedOptions {
    LinkedOptions {
        load_bias: bias,
        stack_size: 256,
    }
}

#[test]
fn numeric_entries_use_exact_unwind_regions_and_apply_bias_once() {
    let data = fixture(&[(0x400, 16), (0x420, 16)]);
    for bias in [0, 0x10000, 0x234567] {
        let image = linked_elf::load_at(&data, 0x400, options(bias)).unwrap();
        assert_eq!(image.image.function.address, bias + 0x400);
        assert_eq!(image.image.function.name, "sub_400");
        assert_eq!(image.image.function.bytes.len(), 16);
        assert_eq!(image.functions.len(), 2);
        assert_eq!(
            image.functions[0].origin,
            FunctionOrigin::Unwind {
                record_offset: 0x511
            }
        );
        assert!(linked_elf::load_at(&data, 0x420, options(bias)).is_ok());
        assert!(matches!(
            linked_elf::load_at(&data, 0x401, options(bias)),
            Err(BinaryError::MissingFunctionAddress(0x401))
        ));
        if bias != 0 {
            assert!(linked_elf::load_at(&data, bias + 0x400, options(bias)).is_err());
        }
        let module = nirvana::module_ir::lift_elf_at(&data, 0x400, options(bias)).unwrap();
        assert_eq!(module.program.entry(), bias + 0x400);
    }
    assert!(matches!(
        linked_elf::load(&data, "fixture", options(0)),
        Err(BinaryError::MissingFunction(_))
    ));
}

#[test]
fn metadata_ranges_require_executable_file_bytes_and_unique_ownership() {
    for regions in [
        vec![(0x400, 32), (0x410, 32)],
        vec![(0x400, 16), (0x400, 32)],
        vec![(0x10f0, 16)],
        vec![(0x500, 0x100001)],
    ] {
        assert!(
            linked_elf::load_at(&fixture(&regions), 0x400, options(0)).is_err(),
            "{regions:?}"
        );
    }
    let duplicate =
        linked_elf::load_at(&fixture(&[(0x400, 16), (0x400, 16)]), 0x400, options(0)).unwrap();
    assert_eq!(duplicate.functions.len(), 1);
    let original = fixture(&[(0x400, 16)]);
    for (offset, width, value) in [
        (68, 4, 6),                      // PT_LOAD is not executable
        (0x800 + 3 * 64 + 24, 8, 0x501), // section mapping differs
        (0x800 + 3 * 64 + 8, 8, 0),      // not allocated
        (0x800 + 3 * 64 + 8, 8, 0x802),  // compressed
        (0x800 + 3 * 64 + 4, 4, 8),      // NOBITS
        (0x800 + 3 * 64 + 32, 8, 1),     // truncated frame
        (0x800 + 3 * 64 + 32, 8, 4 * 1024 * 1024 + 1),
        (0x700, 4, 1),               // section-name boundary NUL
        (0x800 + 3 * 64, 4, 0xffff), // section name outside string table
        (0x800 + 2 * 64 + 4, 4, 1),  // names require SHT_STRTAB
        (0x500, 4, u32::MAX as u64), // unsupported extended length
    ] {
        let mut data = original.clone();
        if width == 4 {
            put32(&mut data, offset, value as u32);
        } else {
            put64(&mut data, offset, value);
        }
        assert!(
            linked_elf::load_at(&data, 0x400, options(0)).is_err(),
            "offset{offset:x}"
        );
    }
    let mut data = original.clone();
    put16(&mut data, 60, 5);
    let copy = data[0x800 + 3 * 64..0x800 + 4 * 64].to_vec();
    data[0x800 + 4 * 64..0x800 + 5 * 64].copy_from_slice(&copy);
    assert!(
        linked_elf::load_at(&data, 0x400, options(0))
            .unwrap_err()
            .to_string()
            .contains("multiple .eh_frame")
    );
}

fn with_symbol(mut data: Vec<u8>, size: u64) -> Vec<u8> {
    put16(&mut data, 60, 6);
    data[0x740..0x749].copy_from_slice(b"\0fixture\0");
    section(&mut data, 4, 27, 3, 0, (0, 0x740), 9);
    section(&mut data, 5, 35, 2, 0, (0, 0x600), 48);
    put32(&mut data, 0x800 + 5 * 64 + 40, 4);
    put64(&mut data, 0x800 + 5 * 64 + 56, 24);
    put32(&mut data, 0x618, 1);
    data[0x61c] = 0x12;
    put16(&mut data, 0x61e, 1);
    put64(&mut data, 0x620, 0x400);
    put64(&mut data, 0x628, size);
    data
}

#[test]
fn sized_symbols_cover_fragments_and_name_selection_is_independent() {
    let data = with_symbol(fixture(&[(0x400, 16), (0x420, 16)]), 48);
    let image = linked_elf::load_at(&data, 0x400, options(0)).unwrap();
    assert_eq!(image.functions.len(), 1);
    assert_eq!(image.functions[0].origin, FunctionOrigin::Symbol);
    assert_eq!(image.image.function.bytes.len(), 48);
    assert!(matches!(
        linked_elf::load_at(&data, 0x420, options(0)),
        Err(BinaryError::MissingFunctionAddress(_))
    ));
    let crossing = with_symbol(fixture(&[(0x400, 48)]), 16);
    assert!(matches!(
        linked_elf::load_at(&crossing, 0x400, options(0)),
        Err(BinaryError::AmbiguousFunctionAddress(_))
    ));
    let mut malformed = data;
    put32(&mut malformed, 0x500, u32::MAX);
    assert!(linked_elf::load(&malformed, "fixture", options(0)).is_ok());
    assert!(linked_elf::load_at(&malformed, 0x400, options(0)).is_err());
}

#[test]
fn dynamic_relocations_in_unwind_data_have_an_explicit_boundary() {
    let mut data = fixture(&[(0x400, 16)]);
    put16(&mut data, 56, 2);
    put32(&mut data, 120, 2);
    put32(&mut data, 124, 6);
    put64(&mut data, 128, 0x200);
    put64(&mut data, 136, 0x200);
    put64(&mut data, 152, 64);
    put64(&mut data, 160, 64);
    for (i, (tag, value)) in [(7, 0x300), (8, 24), (9, 24), (0, 0)]
        .into_iter()
        .enumerate()
    {
        put64(&mut data, 0x200 + i * 16, tag);
        put64(&mut data, 0x208 + i * 16, value);
    }
    put64(&mut data, 0x300, 0x508);
    put64(&mut data, 0x308, 8);
    put64(&mut data, 0x310, 0x400);
    assert!(matches!(
        linked_elf::load_at(&data, 0x400, options(0)),
        Err(BinaryError::Unsupported(
            "dynamic relocations within .eh_frame"
        ))
    ));
    put64(&mut data, 0x300, 0x450);
    let image = linked_elf::load_at(&data, 0x400, options(0x10000)).unwrap();
    assert_eq!(
        u64::from_le_bytes(image.image.memory[0x450..0x458].try_into().unwrap()),
        0x10400
    );
}

#[test]
fn cli_entry_is_a_link_time_address_and_conflicting_selectors_are_diagnosed() {
    let directory = std::env::temp_dir().join(format!("nirvana-unwind-cli-{}", std::process::id()));
    std::fs::create_dir_all(&directory).unwrap();
    let file = directory.join("stripped");
    std::fs::write(&file, fixture(&[(0x400, 16)])).unwrap();
    let command = |args: &[&str]| {
        std::process::Command::new(env!("CARGO_BIN_EXE_nirvana"))
            .arg(&file)
            .args(args)
            .output()
            .unwrap()
    };
    let output = command(&["--entry", "0x400", "--emit", "module-ir"]);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        String::from_utf8(output.stdout)
            .unwrap()
            .contains("sub_400")
    );
    for mode in [
        "module-c",
        "module-readable-c",
        "module-locals-c",
        "module-values",
        "module-jumps",
    ] {
        assert!(
            command(&["--entry", "0x400", "--emit", mode])
                .status
                .success(),
            "{mode}"
        );
    }
    let output = command(&[
        "--entry",
        "0x400",
        "--symbol",
        "fixture",
        "--emit",
        "module-ir",
    ]);
    assert!(!output.status.success());
    assert!(
        String::from_utf8(output.stderr)
            .unwrap()
            .contains("either --symbol")
    );
    assert!(
        !command(&["--entry", "0x10400", "--emit", "module-ir"])
            .status
            .success()
    );
    std::fs::remove_dir_all(directory).unwrap();
}

use nirvana::elf::{ElfError, Relocation, read_function};
use std::path::PathBuf;
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

fn put16(bytes: &mut [u8], offset: usize, value: u16) {
    bytes[offset..offset + 2].copy_from_slice(&value.to_le_bytes());
}
fn put32(bytes: &mut [u8], offset: usize, value: u32) {
    bytes[offset..offset + 4].copy_from_slice(&value.to_le_bytes());
}
fn put64(bytes: &mut [u8], offset: usize, value: u64) {
    bytes[offset..offset + 8].copy_from_slice(&value.to_le_bytes());
}
fn get64(bytes: &[u8], offset: usize) -> u64 {
    u64::from_le_bytes(bytes[offset..offset + 8].try_into().unwrap())
}
fn header(bytes: &[u8], index: usize) -> usize {
    get64(bytes, 40) as usize + index * 64
}
fn contents(bytes: &[u8], index: usize) -> usize {
    get64(bytes, header(bytes, index) + 24) as usize
}

/// A function starts at text offset 4 and has exactly 8 bytes. A named external
/// relocation is at function offset 2, with a four-byte field wholly inside it.
fn object_fixture() -> Vec<u8> {
    let text: Vec<u8> = (0..16).collect();
    let strings = b"\0foo\0external\0".to_vec();
    let mut symbols = vec![0; 72];
    put32(&mut symbols, 24, 1);
    symbols[28] = 0x12; // STB_GLOBAL | STT_FUNC
    put16(&mut symbols, 30, 1);
    put64(&mut symbols, 32, 4);
    put64(&mut symbols, 40, 8);
    put32(&mut symbols, 48, 5); // external, SHN_UNDEF
    symbols[52] = 0x10;
    let mut relocations = vec![0; 24];
    put64(&mut relocations, 0, 6);
    put64(&mut relocations, 8, (2u64 << 32) | 4);
    put64(&mut relocations, 16, u64::MAX - 3); // explicit addend -4
    let names = b"\0.text\0.strtab\0.symtab\0.rela.text\0.shstrtab\0".to_vec();
    let sections = [text, strings, symbols, relocations, names];
    let mut bytes = vec![0; 64];
    bytes[..7].copy_from_slice(b"\x7fELF\x02\x01\x01");
    put16(&mut bytes, 16, 1);
    put16(&mut bytes, 18, 62);
    put32(&mut bytes, 20, 1);
    put16(&mut bytes, 52, 64);
    put16(&mut bytes, 58, 64);
    put16(&mut bytes, 60, 6);
    put16(&mut bytes, 62, 5);
    let mut offsets = Vec::new();
    for section in &sections {
        offsets.push(bytes.len());
        bytes.extend(section);
    }
    let section_table = bytes.len();
    put64(&mut bytes, 40, section_table as u64);
    bytes.resize(section_table + 6 * 64, 0);
    for (index, section) in sections.iter().enumerate() {
        let position = section_table + (index + 1) * 64;
        put32(&mut bytes, position, [1, 7, 15, 23, 34][index]);
        put32(&mut bytes, position + 4, [1, 3, 2, 4, 3][index]);
        put64(&mut bytes, position + 8, if index == 0 { 6 } else { 0 });
        put64(&mut bytes, position + 24, offsets[index] as u64);
        put64(&mut bytes, position + 32, section.len() as u64);
        put64(&mut bytes, position + 48, 1);
        if index == 2 {
            put32(&mut bytes, position + 40, 2);
            put32(&mut bytes, position + 44, 1);
            put64(&mut bytes, position + 56, 24);
        } else if index == 3 {
            put32(&mut bytes, position + 40, 3);
            put32(&mut bytes, position + 44, 1);
            put64(&mut bytes, position + 56, 24);
        }
    }
    bytes
}

#[test]
fn extracts_symbol_size_and_section_relative_relocations() {
    let object = object_fixture();
    let image = read_function(&object, "foo").unwrap();
    assert_eq!(image.name, "foo");
    assert_eq!(image.address, 4);
    assert_eq!(image.bytes, (4..12).collect::<Vec<_>>());
    assert_eq!(
        image.relocations,
        vec![Relocation {
            offset: 2,
            kind: 4,
            symbol: Some("external".to_owned()),
        }]
    );
    let mut addressed = object;
    let text_header = header(&addressed, 1);
    put64(&mut addressed, text_header + 16, 0x1000);
    assert_eq!(read_function(&addressed, "foo").unwrap().address, 0x1004);
}

#[test]
fn reports_rel_and_unnamed_or_unknown_relocations_without_resolving_them() {
    let mut object = object_fixture();
    let relocation_header = header(&object, 4);
    let relocation = contents(&object, 4);
    put32(&mut object, relocation_header + 4, 9); // SHT_REL
    put64(&mut object, relocation_header + 32, 16);
    put64(&mut object, relocation_header + 56, 16);
    put64(&mut object, relocation + 8, 0xfeed); // symbol zero; unknown relocation type
    assert_eq!(
        read_function(&object, "foo").unwrap().relocations,
        vec![Relocation {
            offset: 2,
            kind: 0xfeed,
            symbol: None,
        }]
    );
}

#[test]
fn only_collects_relocations_for_the_selected_function_and_section() {
    for offset in [0, 12] {
        let mut object = object_fixture();
        let relocation = contents(&object, 4);
        put64(&mut object, relocation, offset);
        assert!(
            read_function(&object, "foo")
                .unwrap()
                .relocations
                .is_empty()
        );
    }
    let mut object = object_fixture();
    let relocation_header = header(&object, 4);
    put32(&mut object, relocation_header + 44, 2); // targets .strtab instead of .text
    assert!(
        read_function(&object, "foo")
            .unwrap()
            .relocations
            .is_empty()
    );
}

#[test]
fn rejects_unknown_sizes_ambiguous_symbols_and_nonfunctions() {
    let original = object_fixture();
    let symbol = contents(&original, 3) + 24;
    let mut object = original.clone();
    put64(&mut object, symbol + 16, 0);
    assert_eq!(
        read_function(&object, "foo"),
        Err(ElfError::ZeroSizedFunction("foo".into()))
    );
    let mut object = original.clone();
    let copy = object[symbol..symbol + 24].to_vec();
    object[symbol + 24..symbol + 48].copy_from_slice(&copy);
    assert_eq!(
        read_function(&object, "foo"),
        Err(ElfError::AmbiguousFunction("foo".into()))
    );
    let mut object = original.clone();
    object[symbol + 4] = 0x11; // STT_OBJECT
    assert_eq!(
        read_function(&object, "foo"),
        Err(ElfError::MissingFunction("foo".into()))
    );
    let mut object = original.clone();
    put16(&mut object, symbol + 6, 0); // SHN_UNDEF
    assert_eq!(
        read_function(&object, "foo"),
        Err(ElfError::MissingFunction("foo".into()))
    );
    assert_eq!(
        read_function(&original, "missing"),
        Err(ElfError::MissingFunction("missing".into()))
    );
}

#[test]
fn unsupported_identification_and_extended_numbering_have_explicit_errors() {
    let original = object_fixture();
    for (offset, value) in [(4, 1), (5, 2), (6, 0)] {
        let mut object = original.clone();
        object[offset] = value;
        assert!(matches!(
            read_function(&object, "foo"),
            Err(ElfError::Unsupported(_))
        ));
    }
    for (offset, value) in [
        (16, 2),
        (16, 3),
        (18, 3),
        (60, 0),
        (60, 0xff00),
        (62, 0xffff),
        (56, 0xffff),
    ] {
        let mut object = original.clone();
        put16(&mut object, offset, value);
        assert!(
            matches!(read_function(&object, "foo"), Err(ElfError::Unsupported(_))),
            "offset={offset}, value={value}"
        );
    }
    let mut object = original.clone();
    let symbol = contents(&object, 3) + 24;
    put16(&mut object, symbol + 6, 0xffff);
    assert!(matches!(
        read_function(&object, "foo"),
        Err(ElfError::Unsupported(_))
    ));
    let mut object = original;
    let section = header(&object, 2);
    put32(&mut object, section + 4, 18);
    assert!(matches!(
        read_function(&object, "foo"),
        Err(ElfError::Unsupported(_))
    ));
}

#[test]
fn invalid_ranges_tables_indices_and_strings_are_errors() {
    let original = object_fixture();
    let mut bad = Vec::new();
    for (offset, value) in [
        (40, u64::MAX),
        (40, u64::MAX - 31),
        (40, 0),
        (header(&original, 1) + 24, u64::MAX),
        (header(&original, 1) + 32, u64::MAX),
        (contents(&original, 3) + 32, u64::MAX),
        (contents(&original, 3) + 40, u64::MAX),
        (header(&original, 3) + 56, 0),
        (header(&original, 3) + 56, 23),
        (header(&original, 3) + 32, 71),
        (header(&original, 4) + 56, 0),
        (header(&original, 4) + 32, 23),
        (contents(&original, 4), 16),
        (contents(&original, 4), 15),
        (contents(&original, 4) + 8, u64::MAX),
    ] {
        let mut object = original.clone();
        put64(&mut object, offset, value);
        bad.push(object);
    }
    for (offset, value) in [
        (header(&original, 3) + 40, 99),
        (header(&original, 3) + 40, 1),
        (header(&original, 3) + 44, 99),
        (header(&original, 4) + 40, 99),
        (header(&original, 4) + 44, 99),
        (contents(&original, 3) + 24, u32::MAX),
        (header(&original, 1), u32::MAX),
    ] {
        let mut object = original.clone();
        put32(&mut object, offset, value);
        bad.push(object);
    }
    for (offset, value) in [
        (52, 63),
        (58, 63),
        (62, 99),
        (contents(&original, 3) + 30, 99),
    ] {
        let mut object = original.clone();
        put16(&mut object, offset, value);
        bad.push(object);
    }
    for offset in [
        0,
        contents(&original, 2),
        contents(&original, 2) + 13,
        contents(&original, 2) + 1,
    ] {
        let mut object = original.clone();
        object[offset] = 0xff;
        bad.push(object);
    }
    for (index, object) in bad.iter().enumerate() {
        assert!(read_function(object, "foo").is_err(), "mutation {index}");
    }
}

#[test]
fn relocation_fields_crossing_function_boundaries_are_not_silently_ignored() {
    for offset in [3, 10] {
        let mut object = object_fixture();
        let relocation = contents(&object, 4);
        put64(&mut object, relocation, offset);
        assert!(read_function(&object, "foo").is_err());
    }
}

#[test]
fn all_truncations_and_every_single_byte_mutation_are_panic_free() {
    let original = object_fixture();
    for length in 0..original.len() {
        assert!(
            read_function(&original[..length], "foo").is_err(),
            "length {length}"
        );
    }
    for index in 0..original.len() {
        for value in [0, 1, 0x7f, 0xff] {
            let mut object = original.clone();
            object[index] = value;
            let _ = read_function(&object, "foo");
        }
    }
}

struct Scratch(PathBuf);
impl Scratch {
    fn new() -> Self {
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let path = std::env::temp_dir().join(format!("nirvana-elf-{}-{nonce}", std::process::id()));
        std::fs::create_dir(&path).unwrap();
        Self(path)
    }
}
impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

#[test]
fn reads_real_diamond_and_preserves_call_chain_external_relocations() {
    let scratch = Scratch::new();
    for optimization in ["-O0", "-O2"] {
        for name in ["diamond", "call-chain"] {
            let output = scratch.0.join(format!("{name}-{optimization}.o"));
            let source = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                .join("tests/fixtures/cases")
                .join(format!("{name}.c"));
            let compilation = Command::new("cc")
                .args([
                    "-std=c11",
                    optimization,
                    "-c",
                    "-fno-pie",
                    "-fno-stack-protector",
                    "-fno-asynchronous-unwind-tables",
                ])
                .arg(source)
                .arg("-o")
                .arg(&output)
                .output()
                .expect("ELF integration tests require a system compiler named cc");
            assert!(
                compilation.status.success(),
                "{}",
                String::from_utf8_lossy(&compilation.stderr)
            );
            let object = std::fs::read(output).unwrap();
            let image = read_function(&object, "fixture").unwrap();
            assert_eq!(image.name, "fixture");
            assert!(!image.bytes.is_empty());
            if name == "diamond" {
                assert!(image.relocations.is_empty());
            } else {
                assert_eq!(image.relocations.len(), 2);
                for relocation in image.relocations {
                    assert_eq!(relocation.symbol.as_deref(), Some("fixture_mix"));
                    assert!(matches!(relocation.kind, 2 | 4));
                    assert!(relocation.offset + 4 <= image.bytes.len() as u64);
                }
            }
        }
    }
}

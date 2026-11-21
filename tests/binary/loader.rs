use crate::support::native;
use nirvana::elf::{self, RelocationTarget};
use nirvana::loader::{self, LinkedImage, LoadOptions};
use std::process::Command;

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

// Two relocation tables ensure sites outside the selected function, including
// data initializers, cannot disappear from loader validation.
fn object(text_relocs: &[(u64, u32, u32, i64)], data_relocs: &[(u64, u32, u32, i64)]) -> Vec<u8> {
    let strings = b"\0fixture\0puts\0data\0readonly\0".to_vec();
    let mut symbols = vec![0; 5 * 24];
    for (index, (name, kind, section, size)) in
        [(1, 2, 1, 32), (9, 0, 0, 0), (14, 1, 3, 16), (19, 1, 2, 16)]
            .into_iter()
            .enumerate()
    {
        let start = (index + 1) * 24;
        put32(&mut symbols, start, name);
        symbols[start + 4] = 0x10 | kind;
        put16(&mut symbols, start + 6, section);
        put64(&mut symbols, start + 16, size);
    }
    let encode = |records: &[(u64, u32, u32, i64)]| {
        let mut bytes = Vec::new();
        for &(offset, kind, symbol, addend) in records {
            bytes.extend(offset.to_le_bytes());
            bytes.extend((u64::from(symbol) << 32 | u64::from(kind)).to_le_bytes());
            bytes.extend(addend.to_le_bytes());
        }
        bytes
    };
    let sections = [
        vec![0x90; 32],
        b"hello readonly\0\0".to_vec(),
        vec![0; 16],
        Vec::new(),
        strings,
        symbols,
        encode(text_relocs),
        encode(data_relocs),
    ];
    let mut bytes = vec![0; 64];
    bytes[..7].copy_from_slice(b"\x7fELF\x02\x01\x01");
    put16(&mut bytes, 16, 1);
    put16(&mut bytes, 18, 62);
    put32(&mut bytes, 20, 1);
    put16(&mut bytes, 52, 64);
    put16(&mut bytes, 58, 64);
    put16(&mut bytes, 60, 9);
    let mut offsets = Vec::new();
    for section in &sections {
        offsets.push(bytes.len());
        bytes.extend(section);
    }
    let table = bytes.len();
    put64(&mut bytes, 40, table as u64);
    bytes.resize(table + 9 * 64, 0);
    for (index, section) in sections.iter().enumerate() {
        let position = table + (index + 1) * 64;
        put32(&mut bytes, position + 4, [1, 1, 1, 8, 3, 2, 4, 4][index]);
        put64(&mut bytes, position + 8, [6, 2, 3, 3, 0, 0, 0, 0][index]);
        put64(&mut bytes, position + 24, offsets[index] as u64);
        put64(
            &mut bytes,
            position + 32,
            if index == 3 { 64 } else { section.len() as u64 },
        );
        put64(
            &mut bytes,
            position + 48,
            [16, 64, 32, 128, 1, 8, 8, 8][index],
        );
        if index == 5 {
            put32(&mut bytes, position + 40, 5);
            put32(&mut bytes, position + 44, 1);
            put64(&mut bytes, position + 56, 24);
        }
        if index >= 6 {
            put32(&mut bytes, position + 40, 6);
            put32(&mut bytes, position + 44, if index == 6 { 1 } else { 3 });
            put64(&mut bytes, position + 56, 24);
        }
    }
    bytes
}

fn placed(image: &LinkedImage, index: usize) -> u64 {
    image
        .sections
        .iter()
        .find(|section| section.index == index)
        .unwrap()
        .address
}

#[test]
fn puts_import_requires_an_untyped_or_function_symbol() {
    for kind in [0, 1, 2, 3, 6, 10] {
        let mut bytes = object(&[(0, 4, 2, -4)], &[]);
        let entry = contents(&bytes, 6) + 2 * 24;
        bytes[entry + 4] = 0x10 | kind;
        assert_eq!(
            loader::link(&bytes, "fixture", LoadOptions::default()).is_ok(),
            matches!(kind, 0 | 2)
        );
    }
}
fn read(image: &LinkedImage, address: u64, width: usize) -> u64 {
    let start = (address - image.memory_base) as usize;
    let mut bytes = [0; 8];
    bytes[..width].copy_from_slice(&image.memory[start..start + width]);
    u64::from_le_bytes(bytes)
}

fn verify_relocations(object: &[u8], image: &LinkedImage) -> Vec<u64> {
    let mut slots = Vec::new();
    for record in elf::read_allocated_relocations(object).unwrap() {
        let r = record.relocation;
        let place = placed(image, record.section) + r.offset;
        let symbol = match r.target {
            RelocationTarget::Undefined => {
                assert_eq!(r.symbol.as_deref(), Some("puts"));
                image.puts_address
            }
            RelocationTarget::Section { index, offset } => placed(image, index) + offset,
            RelocationTarget::Absolute(value) => value,
            RelocationTarget::Reserved(_) => panic!("unexpected reserved symbol"),
        };
        let addend = i128::from(r.addend.unwrap());
        if matches!(r.kind, 9 | 41 | 42) {
            let displacement = read(image, place, 4) as u32 as i32;
            let slot = (i128::from(place) + i128::from(displacement) - addend) as u64;
            assert_eq!(slot % 8, 0);
            assert_eq!(read(image, slot, 8), symbol);
            assert!(slot + 8 <= image.stack_pointer);
            slots.push(slot);
        } else {
            let expected = i128::from(symbol) + addend
                - if matches!(r.kind, 2 | 4) {
                    i128::from(place)
                } else {
                    0
                };
            let width = r.width.unwrap() as usize;
            let mask = if width == 8 {
                u64::MAX
            } else {
                u64::from(u32::MAX)
            };
            assert_eq!(
                read(image, place, width),
                (expected as u64) & mask,
                "relocation {r:?}"
            );
        }
    }
    slots
}

#[test]
fn patches_every_supported_relocation_and_got_slots_without_mutating_input() {
    let object = object(
        &[
            (0, 1, 4, 1),
            (8, 2, 3, -4),
            (12, 4, 2, -4),
            (16, 10, 3, 3),
            (20, 11, 4, -1),
            (24, 9, 2, -4),
            (28, 41, 2, 3),
        ],
        &[(0, 42, 4, -7), (8, 1, 4, 2)],
    );
    let original = object.clone();
    let old_function = elf::read_function(&object, "fixture").unwrap();
    let old_context = elf::read_function_context(&object, "fixture").unwrap();
    let records = elf::read_allocated_relocations(&object).unwrap();
    assert_eq!(records.len(), 9);
    assert_eq!(records[7].section, 3);
    assert_eq!(records[7].relocation.offset, 0);
    for base in [0x10003, 0x34560] {
        let options = LoadOptions {
            base,
            stack_size: 17,
        };
        let image = loader::link(&object, "fixture", options).unwrap();
        assert_eq!(image.memory_base, base);
        assert_eq!(image.puts_address, base + image.memory.len() as u64);
        assert_eq!(image.stack_pointer % 16, 8);
        assert_eq!(image.stack_pointer + 8, image.puts_address);
        for section in &image.sections {
            let source = &old_context.sections[section.index];
            assert_eq!(section.address % source.alignment.max(1), 0);
            assert_eq!(section.size, source.size);
        }
        assert_eq!(image.sections.len(), 4);
        let bss = (placed(&image, 4) - base) as usize;
        assert_eq!(&image.memory[bss..bss + 64], &[0; 64]);
        let slots = verify_relocations(&object, &image);
        assert_eq!(
            slots[0], slots[1],
            "one slot per symbol, even with different addends"
        );
        assert_ne!(slots[0], slots[2]);
        let function_start = (image.function.address - base) as usize;
        assert_eq!(
            image.function.bytes,
            image.memory[function_start..function_start + 32]
        );
        assert!(image.function.relocations.is_empty());
        assert_eq!(image, loader::link(&object, "fixture", options).unwrap());
    }
    assert_eq!(object, original);
    assert_eq!(
        elf::read_function(&object, "fixture").unwrap(),
        old_function
    );
    assert_eq!(
        elf::read_function_context(&object, "fixture").unwrap(),
        old_context
    );
}

#[test]
fn rejects_unknown_implicit_overlapping_and_unresolved_allocated_relocations() {
    for (text, data) in [
        (vec![(0, 12345, 2, 0)], vec![]),
        (vec![], vec![(0, 12345, 2, 0)]),
        (vec![(0, 1, 2, 0), (0, 1, 2, 0)], vec![]),
        (vec![(0, 1, 2, 0), (4, 10, 2, 0)], vec![]),
        (vec![], vec![(0, 1, 2, 0), (7, 1, 2, 0)]),
    ] {
        assert!(loader::link(&object(&text, &data), "fixture", LoadOptions::default()).is_err());
    }
    let original = object(&[(0, 4, 2, -4)], &[(0, 1, 3, 0)]);
    let mut bad = original.clone();
    let strings = contents(&bad, 5);
    bad[strings + 9..strings + 13].copy_from_slice(b"gets");
    assert!(
        loader::link(&bad, "fixture", LoadOptions::default())
            .unwrap_err()
            .to_string()
            .contains("unresolved import")
    );
    for section in [7, 8] {
        let mut bad = original.clone();
        let h = header(&bad, section);
        put32(&mut bad, h + 4, 9);
        put64(&mut bad, h + 32, 16);
        put64(&mut bad, h + 56, 16);
        assert!(loader::link(&bad, "fixture", LoadOptions::default()).is_err());
    }
    // Relocation tables targeting the same section must be checked together.
    let mut bad = original.clone();
    let h = header(&bad, 8);
    put32(&mut bad, h + 44, 1);
    assert!(
        loader::link(&bad, "fixture", LoadOptions::default())
            .unwrap_err()
            .to_string()
            .contains("overlapping")
    );
    // A valid function does not excuse unresolved data initializer imports.
    let mut bad = object(&[], &[(0, 1, 2, 0)]);
    let start = contents(&bad, 5);
    bad[start + 9..start + 13].copy_from_slice(b"gets");
    assert!(loader::link(&bad, "fixture", LoadOptions::default()).is_err());
}

#[test]
fn rejects_field_overflows_and_checks_signed_and_unsigned_bounds() {
    for (kind, addend, base, accepted) in [
        (10, 63, 0xffff_ff80, true),
        (10, 0, 0x1_0000_0000, false),
        (11, 63, 0x7fff_ff80, true),
        (11, 0, 0x8000_0000, false),
        (10, -0x20000, 0x10000, false),
        (11, -0x20000, 0x10000, true),
        (1, i64::MAX, 0x8000_0000_0000_0000, false),
        (1, i64::MIN, 0x10000, false),
        (2, i64::MAX, 0x10000, false),
        (4, i64::MIN, 0x10000, false),
        (9, i64::MAX, 0x10000, false),
        (42, i64::MIN, 0x10000, false),
    ] {
        let bytes = object(&[(0, kind, 4, addend)], &[]);
        let result = loader::link(
            &bytes,
            "fixture",
            LoadOptions {
                base,
                ..LoadOptions::default()
            },
        );
        assert_eq!(
            result.is_ok(),
            accepted,
            "kind {kind}, addend {addend}, base {base:#x}: {result:?}"
        );
    }
    // PC32 uses the relocation FIELD address P, not the following instruction.
    let bytes = object(&[(12, 2, 4, -4)], &[]);
    let image = loader::link(&bytes, "fixture", LoadOptions::default()).unwrap();
    let place = placed(&image, 1) + 12;
    assert_eq!(
        read(&image, place, 4),
        (placed(&image, 2) - place - 4) as u32 as u64
    );
}

#[test]
fn bounds_alignment_guest_ranges_and_dangerous_metadata_before_loading() {
    let bytes = object(&[], &[]);
    for (section, field, value) in [
        (1, 48, 3),
        (2, 48, 1 << 21),
        (4, 32, 16 * 1024 * 1024),
        (4, 32, u64::MAX),
        (1, 8, 6 | 0x800),
        (2, 8, 2 | 0x400),
        (3, 8, 3 | 0x200),
    ] {
        let mut bad = bytes.clone();
        let h = header(&bad, section);
        put64(&mut bad, h + field, value);
        assert!(
            loader::link(&bad, "fixture", LoadOptions::default()).is_err(),
            "section {section}, field {field}, value {value:#x}"
        );
    }
    for kind in [6, 11, 14, 15, 16, 17, 0x6000_0000] {
        let mut bad = bytes.clone();
        let h = header(&bad, 3);
        put32(&mut bad, h + 4, kind);
        assert!(loader::link(&bad, "fixture", LoadOptions::default()).is_err());
    }
    for stack_size in [0, 8, 15, 16 * 1024 * 1024 + 1, usize::MAX] {
        assert!(
            loader::link(
                &bytes,
                "fixture",
                LoadOptions {
                    stack_size,
                    ..LoadOptions::default()
                }
            )
            .is_err()
        );
    }
    assert!(
        loader::link(
            &bytes,
            "fixture",
            LoadOptions {
                base: u64::MAX - 7,
                ..LoadOptions::default()
            }
        )
        .is_err()
    );
    let mut bad = bytes.clone();
    let h = header(&bad, 3);
    let text = contents(&bad, 1);
    put64(&mut bad, h + 24, text as u64);
    assert!(
        loader::link(&bad, "fixture", LoadOptions::default())
            .unwrap_err()
            .to_string()
            .contains("overlapping")
    );
    let mut bad = bytes.clone();
    let h = header(&bad, 2);
    put64(&mut bad, h + 24, 0);
    assert!(loader::link(&bad, "fixture", LoadOptions::default()).is_err());
    let mut bad = bytes.clone();
    let start = contents(&bad, 6) + 4 * 24;
    put64(&mut bad, start + 8, 17);
    assert!(loader::link(&bad, "fixture", LoadOptions::default()).is_err());
    for kind in [6, 10] {
        let mut bad = bytes.clone();
        let start = contents(&bad, 6) + 4 * 24;
        bad[start + 4] = kind;
        assert!(loader::link(&bad, "fixture", LoadOptions::default()).is_err());
    }
    let mut bad = bytes;
    put16(&mut bad, 60, 4097);
    assert!(
        loader::link(&bad, "fixture", LoadOptions::default())
            .unwrap_err()
            .to_string()
            .contains("section count limit")
    );
}

#[test]
fn malformed_objects_and_all_truncations_never_panic_or_change_the_input() {
    let bytes = object(&[(0, 4, 2, -4)], &[(0, 1, 4, 0)]);
    for len in 0..bytes.len() {
        assert!(
            loader::link(&bytes[..len], "fixture", LoadOptions::default()).is_err(),
            "len {len}"
        );
    }
    for index in 0..bytes.len() {
        for value in [0, 1, 0x7f, 0xff] {
            let mut changed = bytes.clone();
            changed[index] = value;
            let before = changed.clone();
            let _ = loader::link(&changed, "fixture", LoadOptions::default());
            assert_eq!(changed, before);
        }
    }
}

#[test]
fn allocated_inspection_preserves_rel_unknown_and_section_coordinates_with_limits() {
    let mut bytes = object(&[(20, 0xfeed, 2, -123)], &[(8, 1, 4, 5)]);
    // The selected function ends before this relocation. Allocated inspection
    // still exposes it with its original section-relative offset.
    let symbol = contents(&bytes, 6) + 24;
    put64(&mut bytes, symbol + 16, 16);
    assert!(
        elf::read_function_context(&bytes, "fixture")
            .unwrap()
            .references
            .is_empty()
    );
    let h = header(&bytes, 7);
    put32(&mut bytes, h + 4, 9);
    put64(&mut bytes, h + 32, 16);
    put64(&mut bytes, h + 56, 16);
    let records = elf::read_allocated_relocations(&bytes).unwrap();
    assert_eq!(records.len(), 2);
    assert_eq!((records[0].section, records[0].relocation.offset), (1, 20));
    assert_eq!(records[0].relocation.width, None);
    assert_eq!(records[0].relocation.addend, None);
    assert_eq!((records[1].section, records[1].relocation.offset), (3, 8));
    for (count, accepted) in [(16_384, true), (16_385, false)] {
        let bytes = object(&[], &vec![(0, 1, 4, 0); count]);
        assert_eq!(elf::read_allocated_relocations(&bytes).is_ok(), accepted);
    }
}

#[test]
fn exact_ram_limit_is_inclusive_and_pc32_works_above_the_32_bit_address_space() {
    let bytes = object(&[], &[]);
    let max = 16 * 1024 * 1024;
    let options = LoadOptions {
        stack_size: max - 192,
        ..LoadOptions::default()
    };
    let image = loader::link(&bytes, "fixture", options).unwrap();
    assert_eq!(image.memory.len(), max);
    assert!(
        loader::link(
            &bytes,
            "fixture",
            LoadOptions {
                stack_size: options.stack_size + 1,
                ..options
            }
        )
        .is_err()
    );
    let bytes = object(
        &[(0, 2, 4, -4), (4, 4, 2, -4), (8, 42, 2, -4)],
        &[(0, 1, 4, 0)],
    );
    for base in [0x1_0000_0000, 0xffff_ffff_fffe_0000] {
        let image = loader::link(
            &bytes,
            "fixture",
            LoadOptions {
                base,
                ..LoadOptions::default()
            },
        )
        .unwrap();
        verify_relocations(&bytes, &image);
    }
}

use crate::support::native::Scratch;

#[test]
fn real_gcc_o0_o2_pie_absolute_got_function_sections_and_data_initializers() {
    let scratch = Scratch::new();
    let source = scratch.0.join("fixture.c");
    std::fs::write(&source, r#"
extern int puts(const char *);
const char readonly[] __attribute__((aligned(64))) = "readonly";
char writable[] __attribute__((aligned(128))) = "writable";
char zeroed[64];
char *pointer = writable + 3;
int (*external)(const char *) = puts;
__attribute__((noinline)) int before(void) { return 42; }
int fixture(void) { zeroed[3] = 'x'; return puts(readonly + 1) + puts(pointer) + external(writable); }
"#).unwrap();
    let mut seen_plt = false;
    let mut seen_got = false;
    for optimization in ["-O0", "-O2"] {
        for flags in [
            vec![],
            vec!["-fno-pie"],
            vec!["-fno-plt"],
            vec!["-fno-pie", "-fno-plt"],
            vec!["-ffunction-sections", "-fdata-sections", "-fno-pie"],
            vec!["-ffunction-sections", "-fdata-sections", "-fno-plt"],
        ] {
            let output = scratch.0.join("fixture.o");
            let result = native::compile_output(
                Command::new("gcc")
                    .args(["-std=c11", "-c", optimization, "-fno-stack-protector"])
                    .args(&flags)
                    .arg(&source)
                    .arg("-o")
                    .arg(&output),
            );
            assert!(
                result.status.success(),
                "{}",
                String::from_utf8_lossy(&result.stderr)
            );
            let bytes = std::fs::read(&output).unwrap();
            let original = bytes.clone();
            let context = elf::read_function_context(&bytes, "fixture").unwrap();
            let records = elf::read_allocated_relocations(&bytes).unwrap();
            assert!(
                records
                    .iter()
                    .any(|record| record.section != context.section && record.relocation.kind == 1)
            );
            seen_plt |= records.iter().any(|record| record.relocation.kind == 4);
            seen_got |= records
                .iter()
                .any(|record| matches!(record.relocation.kind, 9 | 41 | 42));
            for base in [0x10000, 0x70003] {
                let image = loader::link(
                    &bytes,
                    "fixture",
                    LoadOptions {
                        base,
                        ..LoadOptions::default()
                    },
                )
                .unwrap_or_else(|error| panic!("{optimization} {flags:?}: {error}"));
                assert_eq!(
                    image.sections.len(),
                    context
                        .sections
                        .iter()
                        .filter(|section| section.flags & 2 != 0)
                        .count()
                );
                for section in context
                    .sections
                    .iter()
                    .filter(|section| section.flags & 2 != 0)
                {
                    assert_eq!(placed(&image, section.index) % section.alignment.max(1), 0);
                    if section.kind == 8 {
                        let start = (placed(&image, section.index) - base) as usize;
                        assert!(
                            image.memory[start..start + section.size as usize]
                                .iter()
                                .all(|&byte| byte == 0)
                        );
                    }
                }
                verify_relocations(&bytes, &image);
            }
            assert_eq!(bytes, original);
            assert_eq!(
                elf::read_function(&bytes, "fixture").unwrap(),
                context.image
            );
        }
    }
    assert!(seen_plt);
    assert!(seen_got);
}

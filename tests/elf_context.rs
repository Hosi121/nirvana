use nirvana::elf::{ElfError, RelocationTarget, read_function, read_function_context};
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

const TEXT: usize = 1;
const RODATA: usize = 2;
const DATA: usize = 3;
const BSS: usize = 4;
const STRTAB: usize = 5;
const SYMTAB: usize = 6;
const RELOCATIONS: usize = 7;

/// Nonzero function and symbol offsets deliberately differ from file offsets
/// and section addresses. The object contains unnamed, defined, undefined,
/// absolute, COMMON and NOBITS symbol identities.
fn fixture_with(function_size: usize, relocations: &[(u64, u32, usize, i64)]) -> Vec<u8> {
    let strings = b"\0foo\0named\0puts\0absolute\0common\0writable\0zeroed\0".to_vec();
    let mut symbols = vec![0; 9 * 24];
    for (index, (name, kind, section, value, size)) in [
        (1, 2, TEXT as u16, 8, function_size as u64),
        (0, 3, RODATA as u16, 3, 0),
        (5, 1, RODATA as u16, 6, 6),
        (11, 0, 0, 0, 0),
        (16, 0, 0xfff1, 0x345, 0),
        (25, 1, 0xfff2, 16, 4),
        (32, 1, DATA as u16, 1, 8),
        (41, 1, BSS as u16, 3, 2),
    ]
    .into_iter()
    .enumerate()
    {
        let position = (index + 1) * 24;
        put32(&mut symbols, position, name);
        symbols[position + 4] = 0x10 | kind;
        put16(&mut symbols, position + 6, section);
        put64(&mut symbols, position + 8, value);
        put64(&mut symbols, position + 16, size);
    }
    let mut relocation_bytes = Vec::new();
    for &(offset, kind, symbol, addend) in relocations {
        relocation_bytes.extend(offset.to_le_bytes());
        relocation_bytes.extend(((symbol as u64) << 32 | u64::from(kind)).to_le_bytes());
        relocation_bytes.extend(addend.to_le_bytes());
    }
    let names =
        b"\0.text\0.rodata\0.data\0.bss\0.strtab\0.symtab\0.rela.text\0.shstrtab\0".to_vec();
    let sections = [
        vec![0x90; function_size + 16],
        b"pad\0hello\0tail\0".to_vec(),
        b"\0mutable\0".to_vec(),
        Vec::new(),
        strings,
        symbols,
        relocation_bytes,
        names,
    ];
    let mut object = vec![0; 64];
    object[..7].copy_from_slice(b"\x7fELF\x02\x01\x01");
    put16(&mut object, 16, 1);
    put16(&mut object, 18, 62);
    put32(&mut object, 20, 1);
    put16(&mut object, 52, 64);
    put16(&mut object, 58, 64);
    put16(&mut object, 60, 9);
    put16(&mut object, 62, 8);
    let mut offsets = Vec::new();
    for section in &sections {
        offsets.push(object.len());
        object.extend(section);
    }
    let table = object.len();
    put64(&mut object, 40, table as u64);
    object.resize(table + 9 * 64, 0);
    for (index, section) in sections.iter().enumerate() {
        let position = table + (index + 1) * 64;
        put32(&mut object, position, [1, 7, 15, 21, 26, 34, 42, 53][index]);
        put32(&mut object, position + 4, [1, 1, 1, 8, 3, 2, 4, 3][index]);
        put64(&mut object, position + 8, [6, 2, 3, 3, 0, 0, 0, 0][index]);
        put64(
            &mut object,
            position + 16,
            [0x1000, 0x2000, 0, 0, 0, 0, 0, 0][index],
        );
        put64(&mut object, position + 24, offsets[index] as u64);
        put64(
            &mut object,
            position + 32,
            if index == 3 {
                4096
            } else {
                section.len() as u64
            },
        );
        put64(&mut object, position + 48, 1);
        if index + 1 == SYMTAB {
            put32(&mut object, position + 40, STRTAB as u32);
            put32(&mut object, position + 44, 1);
            put64(&mut object, position + 56, 24);
        } else if index + 1 == RELOCATIONS {
            put32(&mut object, position + 40, SYMTAB as u32);
            put32(&mut object, position + 44, TEXT as u32);
            put64(&mut object, position + 56, 24);
        }
    }
    object
}

fn fixture() -> Vec<u8> {
    fixture_with(
        64,
        &[
            (8, 1, 2, 4),
            (16, 10, 3, -2),
            (24, 4, 4, -4),
            (32, 1, 5, i64::MIN),
            (40, 1, 6, i64::MAX),
            (48, 1, 7, 0),
            (56, 1, 8, 7),
            (64, 0, 0, 0),
        ],
    )
}

#[test]
fn exposes_original_borrowed_sections_and_complete_symbol_identity() {
    let object = fixture();
    let original = object.clone();
    let context = read_function_context(&object, "foo").unwrap();
    assert_eq!(context.image, read_function(&object, "foo").unwrap());
    assert_eq!((context.section, context.offset), (TEXT, 8));
    assert_eq!(context.image.address, 0x1008);
    assert_eq!(context.image.bytes, vec![0x90; 64]);
    assert_eq!(context.sections.len(), 9);
    for (index, section) in context.sections.iter().enumerate() {
        assert_eq!(section.index, index);
        if index == BSS {
            assert_eq!(section.name, Some(".bss"));
            assert_eq!(section.size, 4096);
            assert_eq!(section.bytes, None);
        } else {
            let offset = contents(&object, index);
            let bytes = section.bytes.unwrap();
            assert_eq!(bytes.as_ptr(), object[offset..].as_ptr());
            assert_eq!(bytes.len() as u64, section.size);
        }
    }
    assert_eq!(context.sections[RODATA].name, Some(".rodata"));
    assert_eq!(context.sections[RODATA].flags & 1, 0);
    assert_eq!(context.sections[RODATA].address, 0x2000);
    assert_eq!(context.sections[DATA].flags & 1, 1);
    let references = &context.references;
    assert_eq!(references.len(), 8);
    assert_eq!(references[0].symbol, None);
    assert_eq!(references[0].symbol_kind, 3);
    assert_eq!(
        references[0].target,
        RelocationTarget::Section {
            index: RODATA,
            offset: 3
        }
    );
    assert_eq!(
        (
            references[0].offset,
            references[0].addend,
            references[0].width
        ),
        (0, Some(4), Some(8))
    );
    assert_eq!(references[1].symbol.as_deref(), Some("named"));
    assert_eq!(
        references[1].target,
        RelocationTarget::Section {
            index: RODATA,
            offset: 6
        }
    );
    assert_eq!(references[1].addend, Some(-2));
    assert_eq!(references[2].symbol.as_deref(), Some("puts"));
    assert_eq!(references[2].target, RelocationTarget::Undefined);
    assert_eq!(
        (
            references[2].kind,
            references[2].width,
            references[2].addend
        ),
        (4, Some(4), Some(-4))
    );
    assert_eq!(references[3].target, RelocationTarget::Absolute(0x345));
    assert_eq!(references[3].addend, Some(i64::MIN));
    assert_eq!(references[4].target, RelocationTarget::Reserved(0xfff2));
    assert_eq!(references[4].addend, Some(i64::MAX));
    assert_eq!(
        references[5].target,
        RelocationTarget::Section {
            index: DATA,
            offset: 1
        }
    );
    assert_eq!(
        references[6].target,
        RelocationTarget::Section {
            index: BSS,
            offset: 3
        }
    );
    assert_eq!(references[7].target, RelocationTarget::Undefined);
    assert_eq!(references[7].width, Some(0));
    for (index, reference) in references.iter().enumerate() {
        assert_eq!(reference.symbol_table, SYMTAB);
        assert_eq!(
            reference.symbol_index,
            if index == 7 { 0 } else { index + 2 }
        );
        assert_eq!(reference.offset, index as u64 * 8);
    }
    assert_eq!(object, original);
}

#[test]
fn rel_addends_and_unknown_widths_remain_unknown_and_names_may_be_absent() {
    let mut object = fixture_with(64, &[(16, 0xfeed, 3, -123)]);
    let relocations = header(&object, RELOCATIONS);
    put32(&mut object, relocations + 4, 9);
    put64(&mut object, relocations + 32, 16);
    put64(&mut object, relocations + 56, 16);
    put16(&mut object, 62, 0);
    let context = read_function_context(&object, "foo").unwrap();
    assert!(
        context
            .sections
            .iter()
            .all(|section| section.name.is_none())
    );
    let reference = &context.references[0];
    assert_eq!(reference.offset, 8);
    assert_eq!(reference.addend, None);
    assert_eq!(reference.width, None);
    assert_eq!(reference.symbol.as_deref(), Some("named"));
    assert_eq!(reference.symbol_kind, 1);
    assert_eq!(
        reference.target,
        RelocationTarget::Section {
            index: RODATA,
            offset: 6
        }
    );
}

#[test]
fn relocations_are_scoped_and_field_boundaries_are_checked() {
    for (offset, accepted, count) in [
        (0, true, 0),
        (4, true, 0),
        (5, false, 0),
        (7, false, 0),
        (8, true, 1),
        (68, true, 1),
        (69, false, 0),
        (72, true, 0),
        (76, true, 0),
        (77, false, 0),
        (80, false, 0),
    ] {
        let object = fixture_with(64, &[(offset, 10, 4, -4)]);
        let result = read_function_context(&object, "foo");
        assert_eq!(result.is_ok(), accepted, "offset {offset}: {result:?}");
        if let Ok(context) = result {
            assert_eq!(context.references.len(), count);
        }
    }
    let object = fixture_with(64, &[(7, 0xfeed, 4, 0)]);
    assert!(matches!(
        read_function_context(&object, "foo"),
        Err(ElfError::Unsupported(_))
    ));
    let mut object = fixture_with(64, &[(0, 10, 3, 0)]);
    let section = header(&object, RELOCATIONS);
    put32(&mut object, section + 44, RODATA as u32);
    assert!(
        read_function_context(&object, "foo")
            .unwrap()
            .references
            .is_empty()
    );
}

#[test]
fn malformed_metadata_truncations_and_mutations_are_checked() {
    let original = fixture();
    for length in 0..original.len() {
        assert!(
            read_function_context(&original[..length], "foo").is_err(),
            "length {length}"
        );
    }
    for index in 0..original.len() {
        for value in [0, 1, 0x7f, 0xff] {
            let mut object = original.clone();
            object[index] = value;
            let _ = read_function_context(&object, "foo");
        }
    }
    for (offset, value) in [
        (40, u64::MAX - 31),
        (header(&original, TEXT) + 24, u64::MAX),
        (header(&original, SYMTAB) + 32, u64::MAX),
        (header(&original, SYMTAB) + 56, 0),
        (header(&original, RELOCATIONS) + 32, 23),
        (header(&original, RELOCATIONS) + 56, 0),
        (contents(&original, RELOCATIONS) + 8, u64::MAX),
    ] {
        let mut object = original.clone();
        put64(&mut object, offset, value);
        assert!(
            read_function_context(&object, "foo").is_err(),
            "offset {offset}"
        );
    }
    for (offset, value) in [
        (header(&original, SYMTAB) + 40, TEXT as u32),
        (header(&original, SYMTAB) + 44, 100),
        (header(&original, RELOCATIONS) + 40, STRTAB as u32),
        (header(&original, RELOCATIONS) + 44, 100),
        (contents(&original, SYMTAB) + 24, u32::MAX),
        (header(&original, RODATA), u32::MAX),
    ] {
        let mut object = original.clone();
        put32(&mut object, offset, value);
        assert!(
            read_function_context(&object, "foo").is_err(),
            "offset {offset}"
        );
    }
    // No file range should be fabricated for a valid NOBITS section.
    let mut object = original;
    let bss = header(&object, BSS);
    put64(&mut object, bss + 24, u64::MAX);
    put64(&mut object, bss + 32, u64::MAX);
    assert_eq!(
        read_function_context(&object, "foo").unwrap().sections[BSS].bytes,
        None
    );
}

#[test]
fn context_limits_are_inclusive_and_do_not_restrict_legacy_extraction() {
    for (size, accepted) in [(1_048_576, true), (1_048_577, false)] {
        let object = fixture_with(size, &[]);
        assert_eq!(read_function_context(&object, "foo").is_ok(), accepted);
        assert_eq!(read_function(&object, "foo").unwrap().bytes.len(), size);
    }
    for (count, accepted) in [(16_384, true), (16_385, false)] {
        let object = fixture_with(64, &vec![(8, 0, 0, 0); count]);
        let result = read_function_context(&object, "foo");
        assert_eq!(result.is_ok(), accepted, "count {count}");
        if let Ok(context) = result {
            assert_eq!(context.references.len(), count);
        }
        assert_eq!(
            read_function(&object, "foo").unwrap().relocations.len(),
            count
        );
    }
}

#[test]
fn repeated_long_names_exhaust_work_without_per_symbol_copies() {
    let original = fixture();
    let old_table = get64(&original, 40) as usize;
    let mut object = original[..old_table].to_vec();
    let names_offset = object.len();
    object.push(0);
    object.extend(b"foo\0");
    let long_name = object.len() - names_offset;
    object.resize(object.len() + 1_100_000, b'x');
    object.push(0);
    let names_size = object.len() - names_offset;
    let new_table = object.len();
    object.extend(&original[old_table..]);
    put64(&mut object, 40, new_table as u64);
    let names_header = header(&object, STRTAB);
    put64(&mut object, names_header + 24, names_offset as u64);
    put64(&mut object, names_header + 32, names_size as u64);
    let symbols = contents(&object, SYMTAB);
    for index in 2..9 {
        put32(&mut object, symbols + index * 24, long_name as u32);
    }
    assert!(matches!(
        read_function_context(&object, "foo"),
        Err(ElfError::Unsupported(
            "ELF context inspection work limit exceeded"
        ))
    ));
}

struct Scratch(PathBuf);
impl Scratch {
    fn new() -> Self {
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let path = std::env::temp_dir().join(format!(
            "nirvana-elf-context-{}-{nonce}",
            std::process::id()
        ));
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
fn compiler_strings_puts_and_function_sections_keep_their_original_coordinates() {
    let scratch = Scratch::new();
    let source = scratch.0.join("context.c");
    std::fs::write(
        &source,
        r#"
extern int puts(const char *);
const char prefix[] = "prefix padding";
const char named_readonly[] = "named readonly";
char writable[] = "writable";
char zeroed[32];
__attribute__((noinline)) int before(void) { return 42; }
int fixture(void) {
    return puts("inline literal") + puts(named_readonly) + puts(writable);
}
"#,
    )
    .unwrap();
    for function_sections in [false, true] {
        let output = scratch.0.join(format!("context-{function_sections}.o"));
        let mut compiler = Command::new("cc");
        compiler.args([
            "-std=c11",
            "-O0",
            "-c",
            "-fno-pie",
            "-fno-stack-protector",
            "-fno-asynchronous-unwind-tables",
        ]);
        if function_sections {
            compiler.arg("-ffunction-sections");
        }
        let compilation = compiler
            .arg(&source)
            .arg("-o")
            .arg(&output)
            .output()
            .expect("ELF context tests require cc");
        assert!(
            compilation.status.success(),
            "{}",
            String::from_utf8_lossy(&compilation.stderr)
        );
        let object = std::fs::read(output).unwrap();
        let original = object.clone();
        let context = read_function_context(&object, "fixture").unwrap();
        assert_eq!(context.image, read_function(&object, "fixture").unwrap());
        let selected = &context.sections[context.section];
        assert_eq!(
            selected.name,
            Some(if function_sections {
                ".text.fixture"
            } else {
                ".text"
            })
        );
        if function_sections {
            assert_eq!(context.offset, 0);
        } else {
            assert!(context.offset > 0);
        }
        let start = context.offset as usize;
        assert_eq!(
            context.image.bytes,
            selected.bytes.unwrap()[start..start + context.image.bytes.len()]
        );
        let calls: Vec<_> = context
            .references
            .iter()
            .filter(|reference| reference.symbol.as_deref() == Some("puts"))
            .collect();
        assert_eq!(calls.len(), 3);
        for reference in calls {
            assert_eq!(reference.target, RelocationTarget::Undefined);
            assert!(matches!(reference.kind, 2 | 4));
            assert_eq!(reference.width, Some(4));
            assert_eq!(reference.addend, Some(-4));
        }
        let literal = context
            .references
            .iter()
            .find(|reference| {
                reference.symbol_kind == 3
                    && matches!(reference.target, RelocationTarget::Section { .. })
            })
            .unwrap();
        let RelocationTarget::Section { index, offset } = literal.target else {
            panic!("expected section symbol");
        };
        let target = &context.sections[index];
        assert_eq!(target.name, Some(".rodata"));
        assert_eq!(target.flags & 1, 0);
        // -fno-pie emits an absolute relocation for the literal. Its positive
        // explicit addend distinguishes section symbol value from string offset.
        assert!(matches!(literal.kind, 1 | 10 | 11));
        let string_offset = offset.checked_add_signed(literal.addend.unwrap()).unwrap() as usize;
        assert!(string_offset > 0);
        assert!(target.bytes.unwrap()[string_offset..].starts_with(b"inline literal\0"));
        for (name, text, writable) in [
            ("named_readonly", b"named readonly\0".as_slice(), false),
            ("writable", b"writable\0".as_slice(), true),
        ] {
            let reference = context
                .references
                .iter()
                .find(|reference| reference.symbol.as_deref() == Some(name))
                .unwrap();
            let RelocationTarget::Section { index, offset } = reference.target else {
                panic!("expected defined symbol");
            };
            let target = &context.sections[index];
            assert_eq!(target.flags & 1 != 0, writable);
            assert!(target.bytes.unwrap()[offset as usize..].starts_with(text));
        }
        assert!(
            context
                .sections
                .iter()
                .any(|section| section.name == Some(".bss")
                    && section.bytes.is_none()
                    && section.size >= 32)
        );
        assert_eq!(object, original);
    }
}

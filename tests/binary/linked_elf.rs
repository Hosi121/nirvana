use crate::support::native;
use nirvana::linked_elf::{self, BinaryError, LinkedOptions};
use std::process::Command;

fn put16(b: &mut [u8], o: usize, x: u16) {
    b[o..o + 2].copy_from_slice(&x.to_le_bytes());
}
fn put32(b: &mut [u8], o: usize, x: u32) {
    b[o..o + 4].copy_from_slice(&x.to_le_bytes());
}
fn put64(b: &mut [u8], o: usize, x: u64) {
    b[o..o + 8].copy_from_slice(&x.to_le_bytes());
}
fn get64(b: &[u8], o: usize) -> u64 {
    u64::from_le_bytes(b[o..o + 8].try_into().unwrap())
}
fn rela(b: &mut [u8], o: usize, site: u64, kind: u32, symbol: u32, addend: i64) {
    put64(b, o, site);
    put64(b, o + 8, (u64::from(symbol) << 32) | u64::from(kind));
    put64(b, o + 16, addend as u64);
}
fn fixture() -> Vec<u8> {
    let mut b = vec![0; 0x800];
    b[..7].copy_from_slice(b"\x7fELF\x02\x01\x01");
    put16(&mut b, 16, 3);
    put16(&mut b, 18, 62);
    put32(&mut b, 20, 1);
    put64(&mut b, 32, 64);
    put64(&mut b, 40, 0x500);
    put16(&mut b, 52, 64);
    put16(&mut b, 54, 56);
    put16(&mut b, 56, 2);
    put16(&mut b, 58, 64);
    put16(&mut b, 60, 5);
    put32(&mut b, 64, 1);
    put32(&mut b, 68, 7);
    put64(&mut b, 96, 0x800);
    put64(&mut b, 104, 0x900);
    put64(&mut b, 112, 0x1000);
    put32(&mut b, 120, 2);
    put32(&mut b, 124, 6);
    put64(&mut b, 128, 0x180);
    put64(&mut b, 136, 0x180);
    let tags = [
        (5, 0x300),
        (10, 29),
        (6, 0x280),
        (11, 24),
        (4, 0x3d0),
        (7, 0x340),
        (8, 72),
        (9, 24),
        (23, 0x3a0),
        (2, 24),
        (20, 7),
        (0, 0),
    ];
    put64(&mut b, 152, tags.len() as u64 * 16);
    put64(&mut b, 160, tags.len() as u64 * 16);
    for (i, (tag, value)) in tags.into_iter().enumerate() {
        put64(&mut b, 0x180 + i * 16, tag);
        put64(&mut b, 0x188 + i * 16, value);
    }
    for (i, (name, info, section, value, size)) in [
        (1, 0x12, 1, 0x400, 32),
        (9, 0x12, 0, 0, 0),
        (14, 0x20, 0, 0, 0),
    ]
    .into_iter()
    .enumerate()
    {
        let o = 0x280 + (i + 1) * 24;
        put32(&mut b, o, name);
        b[o + 4] = info;
        put16(&mut b, o + 6, section);
        put64(&mut b, o + 8, value);
        put64(&mut b, o + 16, size);
    }
    b[0x300..0x31d].copy_from_slice(b"\0fixture\0puts\0__gmon_start__\0");
    rela(&mut b, 0x340, 0x470, 8, 0, 0x420);
    rela(&mut b, 0x358, 0x478, 1, 2, 0);
    rela(&mut b, 0x370, 0x488, 6, 3, 0);
    rela(&mut b, 0x3a0, 0x480, 7, 2, 0);
    put32(&mut b, 0x3d0, 1);
    put32(&mut b, 0x3d4, 4);
    put32(&mut b, 0x3d8, 1);
    b[0x400..0x406].copy_from_slice(&[0xff, 0x25, 0x7a, 0, 0, 0]);
    b[0x410] = 0xc3;
    b[0x420..0x426].copy_from_slice(b"hello\0");
    for (index, kind, flags, address, offset, size, link, stride) in [
        (1, 1, 6, 0x400, 0x400, 32, 0, 0),
        (2, 3, 0, 0, 0x300, 29, 0, 0),
        (3, 11, 0, 0x280, 0x280, 96, 2, 24),
        (4, 4, 0, 0, 0x700, 24, 3, 24),
    ] {
        let o = 0x500 + index * 64;
        put32(&mut b, o + 4, kind);
        put64(&mut b, o + 8, flags);
        put64(&mut b, o + 16, address);
        put64(&mut b, o + 24, offset);
        put64(&mut b, o + 32, size);
        put32(&mut b, o + 40, link);
        put64(&mut b, o + 56, stride);
    }
    // An unsupported section relocation is not a dynamic relocation.
    rela(&mut b, 0x700, 0x490, 12345, 2, 0);
    b
}
fn load(b: &[u8]) -> Result<linked_elf::BinaryImage, BinaryError> {
    linked_elf::load(b, "fixture", LinkedOptions::default())
}
fn read(image: &linked_elf::BinaryImage, address: u64) -> u64 {
    get64(
        &image.image.memory,
        (address - image.image.memory_base) as usize,
    )
}

#[test]
fn maps_bss_relative_absolute_and_imports_without_trusting_section_relocations() {
    let b = fixture();
    let original = b.clone();
    for bias in [0, 0x10000, 0x234567] {
        let image = linked_elf::load(
            &b,
            "fixture",
            LinkedOptions {
                load_bias: bias,
                stack_size: 17,
            },
        )
        .unwrap();
        assert_eq!(image.elf_type, 3);
        assert_eq!(image.bias, bias);
        assert_eq!(image.image.memory_base, bias);
        assert_eq!(image.image.function.address, bias + 0x400);
        assert_eq!(image.image.function.bytes.len(), 32);
        assert_eq!(read(&image, bias + 0x470), bias + 0x420);
        assert_eq!(read(&image, bias + 0x478), image.image.puts_address);
        assert_eq!(read(&image, bias + 0x480), image.image.puts_address);
        assert_eq!(read(&image, bias + 0x488), image.image.puts_address + 8);
        assert_eq!(image.imports.len(), 3);
        assert_eq!(image.imports.iter().filter(|s| s.modeled).count(), 2);
        assert_eq!(image.plt_slot(bias + 0x400).unwrap().address, bias + 0x480);
        assert_eq!(&image.image.memory[0x800..0x900], &[0; 256]);
        assert_eq!(image.image.stack_pointer % 16, 8);
        assert_eq!(image.image.stack_pointer + 8, image.image.puts_address);
        assert_eq!(
            image.image.puts_address,
            bias + image.image.memory.len() as u64
        );
    }
    assert_eq!(b, original);
}

fn stream_fixture(copy: bool) -> Vec<u8> {
    let mut b = fixture();
    b[0x31d..0x324].copy_from_slice(b"stdout\0");
    put64(&mut b, 0x198, 36); // DT_STRSZ
    put64(&mut b, 0x5a0, 36); // linked string section
    for index in [2, 3] {
        let o = 0x280 + index * 24;
        put32(&mut b, o, 29);
        b[o + 4] = 0x11;
        put16(&mut b, o + 6, if copy && index == 2 { 1 } else { 0 });
        put64(&mut b, o + 8, if copy && index == 2 { 0x478 } else { 0 });
        put64(&mut b, o + 16, if copy && index == 2 { 8 } else { 0 });
    }
    rela(&mut b, 0x358, 0x478, if copy { 5 } else { 1 }, 2, 0);
    rela(&mut b, 0x3a0, 0x480, 6, 2, 0);
    b
}

#[test]
fn copy_and_got_data_references_share_one_mutable_guest_variable() {
    for copy in [false, true] {
        for bias in [0, 0x10000, 0x234567] {
            let bytes = stream_fixture(copy);
            let mut image = linked_elf::load(
                &bytes,
                "fixture",
                LinkedOptions {
                    load_bias: bias,
                    stack_size: 64,
                },
            )
            .unwrap();
            assert_eq!(image.image.external_data.len(), 1);
            assert!(
                image.imports.is_empty(),
                "data objects must not become callable imports"
            );
            assert!(image.plt_slot(bias + 0x400).is_none());
            let binding = image.image.external_data[0].clone();
            assert_eq!(binding.stream.name(), "stdout");
            assert_eq!(read(&image, bias + 0x480), binding.address);
            assert_eq!(read(&image, bias + 0x488), binding.address);
            assert_eq!(read(&image, binding.address), binding.handle);
            assert!(binding.handle > image.image.memory_base + image.image.memory.len() as u64);
            if copy {
                assert_eq!(binding.address, bias + 0x478);
            } else {
                assert_eq!(read(&image, bias + 0x478), binding.address);
            }
            let offset = (binding.address - image.image.memory_base) as usize;
            image.image.memory[offset..offset + 8].copy_from_slice(&0x1234_u64.to_le_bytes());
            assert_eq!(read(&image, read(&image, bias + 0x480)), 0x1234);
            assert_eq!(read(&image, read(&image, bias + 0x488)), 0x1234);
        }
    }
}

#[test]
fn copy_bindings_require_matching_object_size_location_name_and_addend() {
    let original = stream_fixture(true);
    for (offset, width, value) in [
        (0x2b4, 1, 0x12), // FUNC
        (0x2b6, 2, 0),    // undefined COPY
        (0x2b8, 8, 0x480),
        (0x2c0, 8, 16),
        (0x368, 8, 1), // nonzero COPY addend
        (0x2b0, 4, 9), // unsupported external object name
    ] {
        let mut bytes = original.clone();
        match width {
            1 => bytes[offset] = value as u8,
            2 => put16(&mut bytes, offset, value as u16),
            4 => put32(&mut bytes, offset, value as u32),
            _ => put64(&mut bytes, offset, value),
        }
        assert!(load(&bytes).is_err(), "offset={offset:#x}");
    }
    let mut bytes = original;
    rela(&mut bytes, 0x3a0, 0x480, 7, 3, 0);
    assert!(
        load(&bytes).is_err(),
        "an OBJECT JUMP_SLOT is not a callable binding"
    );
}
#[test]
fn validates_plt_instruction_execution_range_and_exact_import_field() {
    let mut image = load(&fixture()).unwrap();
    let base = image.image.memory_base;
    assert!(image.plt_slot(base + 0x420).is_none());
    assert!(image.plt_slot(u64::MAX).is_none());
    image.image.memory[0x400..0x40a]
        .copy_from_slice(&[0xf3, 0x0f, 0x1e, 0xfa, 0xff, 0x25, 0x76, 0, 0, 0]);
    assert_eq!(image.plt_slot(base + 0x400).unwrap().name, "puts");
    image.image.memory[0x406] += 1;
    assert!(image.plt_slot(base + 0x400).is_none());
    image.image.memory[0x420..0x426].copy_from_slice(&[0xff, 0x25, 0x5a, 0, 0, 0]);
    // This PT_LOAD is executable, so an actual stub outside the selected
    // function is supported too. Merely containing its destination is not.
    assert!(image.plt_slot(base + 0x420).is_some());
    let mut bytes = fixture();
    put32(&mut bytes, 68, 6);
    assert!(load(&bytes).is_err());
    let mut bytes = fixture();
    put32(&mut bytes, 64 + 56, 1);
    put32(&mut bytes, 68 + 56, 6);
    put64(&mut bytes, 128, 0x600);
    put64(&mut bytes, 136, 0x900);
    put64(&mut bytes, 152, 0x100);
    put64(&mut bytes, 160, 0x100);
    // Without PT_DYNAMIC the section relocations cannot prove an import.
    assert!(load(&bytes).unwrap().plt_slot(base + 0x400).is_none());
    let mut bytes = fixture();
    put16(&mut bytes, 56, 3);
    put64(&mut bytes, 104, 0x800);
    put32(&mut bytes, 176, 1);
    put32(&mut bytes, 180, 6);
    put64(&mut bytes, 184, 0x800);
    put64(&mut bytes, 192, 0x800);
    put64(&mut bytes, 208, 0);
    put64(&mut bytes, 216, 0x100);
    put64(&mut bytes, 224, 1);
    let mut image = load(&bytes).unwrap();
    image.image.memory[0x800..0x806].copy_from_slice(&[0xff, 0x25, 0x7a, 0xfc, 0xff, 0xff]);
    assert!(image.plt_slot(base + 0x800).is_none());
}

#[test]
fn endbr_bnd_plt_uses_the_actual_instruction_end_and_function_got_field() {
    let mut image = load(&fixture()).unwrap();
    let base = image.image.memory_base;
    image.image.memory[0x400..0x40b]
        .copy_from_slice(&[0xf3, 0x0f, 0x1e, 0xfa, 0xf2, 0xff, 0x25, 0x75, 0, 0, 0]);
    assert_eq!(image.plt_slot(base + 0x400).unwrap().address, base + 0x480);
    image.image.memory[0x407] += 1;
    assert!(
        image.plt_slot(base + 0x400).is_none(),
        "one byte into a GOT field is not its identity"
    );
    image.image.memory[0x400..0x407].copy_from_slice(&[0xf2, 0xff, 0x25, 0x79, 0, 0, 0]);
    assert_eq!(image.plt_slot(base + 0x400).unwrap().address, base + 0x480);
    image.image.memory[0x400..0x408].copy_from_slice(&[0xf2, 0xf2, 0xff, 0x25, 0x78, 0, 0, 0]);
    assert!(
        image.plt_slot(base + 0x400).is_none(),
        "ambiguous repeated prefixes stay unsupported"
    );
}
#[test]
fn malformed_headers_segments_and_function_symbols_are_rejected() {
    let original = fixture();
    for (offset, width, value) in [
        (16, 2, 1),
        (18, 2, 3),
        (52, 2, 63),
        (54, 2, 55),
        (56, 2, 0),
        (40, 8, u64::MAX),
        (32, 8, u64::MAX),
        (96, 8, 0xa00),
        (104, 8, u64::MAX),
        (112, 8, 3),
        (136, 8, 0x190),
        (152, 8, 1),
        (0x500 + 64 + 8, 8, 2),
        (0x280 + 24 + 16, 8, 0),
        (0x280 + 24 + 8, 8, 0x8ff),
    ] {
        let mut b = original.clone();
        match width {
            2 => put16(&mut b, offset, value as u16),
            8 => put64(&mut b, offset, value),
            _ => unreachable!(),
        };
        assert!(load(&b).is_err(), "offset {offset:#x}");
    }
    for length in [0, 6, 63, 120, 0x7ff] {
        assert!(load(&original[..length]).is_err());
    }
    for stack_size in [0, 15, usize::MAX] {
        assert!(
            linked_elf::load(
                &original,
                "fixture",
                LinkedOptions {
                    load_bias: 0,
                    stack_size
                }
            )
            .is_err()
        );
    }
    assert!(
        linked_elf::load(
            &original,
            "fixture",
            LinkedOptions {
                load_bias: u64::MAX,
                stack_size: 16
            }
        )
        .is_err()
    );
    assert!(matches!(
        linked_elf::load(&original, "missing", LinkedOptions::default()),
        Err(BinaryError::MissingFunction(_))
    ));
}
#[test]
fn rejects_unknown_copy_tls_ifunc_rel_overlaps_and_bad_dynamic_tables() {
    for kind in [2, 4, 5, 9, 16, 36, 37, 38, 12345] {
        let mut b = fixture();
        put64(&mut b, 0x348, kind);
        assert!(load(&b).is_err(), "kind {kind}");
    }
    for (offset, value) in [
        (0x340, 0x8f9),
        (0x358, 0x474),
        (0x348, (1_u64 << 32) | 8),
        (0x360, (100_u64 << 32) | 1),
        (0x3a8, (2_u64 << 32) | 7),
        (0x3b0, 1),
        (0x180 + 5 * 16, 17),
        (0x180 + 7 * 16 + 8, 23),
        (0x180 + 10 * 16 + 8, 17),
        (0x180 + 11 * 16, 11),
        (0x3d4, 262145),
        (0x300, 0x41),
    ] {
        let mut b = fixture();
        put64(&mut b, offset, value);
        // The unmodified JUMP_SLOT is valid; make that row a bad symbol index.
        if offset == 0x3a8 {
            put64(&mut b, offset, (100_u64 << 32) | 7);
        }
        assert!(load(&b).is_err(), "offset {offset:#x}");
    }
    for kind in [1, 6, 10] {
        let mut b = fixture();
        b[0x280 + 2 * 24 + 4] = 0x10 | kind;
        assert!(load(&b).is_err());
    }
    for kind in [1, 6, 10] {
        let mut b = fixture();
        b[0x280 + 3 * 24 + 4] = 0x20 | kind;
        assert!(load(&b).is_err());
    }
    let mut b = fixture();
    b[0x280 + 3 * 24 + 4] = 0x10;
    assert!(load(&b).is_err());
    let mut b = fixture();
    put32(&mut b, 120, 7);
    assert!(load(&b).is_err());
    let mut b = fixture();
    put32(&mut b, 0x280 + 3 * 24, 1);
    put16(&mut b, 0x280 + 3 * 24 + 6, 1);
    b[0x280 + 3 * 24 + 4] = 0x12;
    put64(&mut b, 0x280 + 3 * 24 + 8, 0x410);
    put64(&mut b, 0x280 + 3 * 24 + 16, 1);
    assert!(matches!(load(&b), Err(BinaryError::AmbiguousFunction(_))));
}
#[test]
fn supports_sectionless_dynamic_symbols_and_fixed_exec_bias() {
    let mut b = fixture();
    put64(&mut b, 40, 0);
    put16(&mut b, 60, 0);
    put16(&mut b, 62, 0);
    assert_eq!(load(&b).unwrap().image.function.address, 0x10400);
    put16(&mut b, 16, 2);
    assert!(load(&b).is_err());
    let image = linked_elf::load(
        &b,
        "fixture",
        LinkedOptions {
            load_bias: 0,
            stack_size: 256,
        },
    )
    .unwrap();
    assert_eq!(image.image.function.address, 0x400);
    assert_eq!(read(&image, 0x470), 0x420);
}

use crate::support::native::Scratch;
fn checked(command: &mut Command) {
    let result = native::compile_output(command);
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
}
#[test]
fn real_cc_exec_pie_got_o0_o2_at_multiple_biases() {
    let scratch = Scratch::new();
    let source = scratch.0.join("hello.c");
    std::fs::write(&source,"#include <stdio.h>\nchar *message=\"linked hello\"; char bss[32]; __attribute__((noinline)) int fixture(void){bss[0]=7; return puts(message);}\nint main(void){return fixture()<0;}\n").unwrap();
    for opt in ["-O0", "-O2"] {
        for pie in [false, true] {
            for got in [false, true] {
                let binary = scratch.0.join(format!("hello-{opt}-{pie}-{got}"));
                let mut cc = Command::new("cc");
                cc.args(["-std=c11", "-fno-lto", opt]);
                cc.args(if pie {
                    ["-fPIE", "-pie"]
                } else {
                    ["-fno-pie", "-no-pie"]
                });
                if got {
                    cc.arg("-fno-plt");
                }
                checked(cc.arg(&source).arg("-o").arg(&binary));
                let bytes = std::fs::read(&binary).unwrap();
                for bias in if pie {
                    vec![0, 0x10000, 0x200000]
                } else {
                    vec![0]
                } {
                    let image = linked_elf::load(
                        &bytes,
                        "fixture",
                        LinkedOptions {
                            load_bias: bias,
                            stack_size: 256,
                        },
                    )
                    .unwrap_or_else(|e| panic!("{opt} pie={pie} got={got} bias={bias:#x}: {e}"));
                    let puts: Vec<_> = image.imports.iter().filter(|i| i.name == "puts").collect();
                    assert_eq!(puts.len(), 1);
                    assert!(puts[0].modeled);
                    assert_eq!(read(&image, puts[0].address), image.image.puts_address);
                    assert!(image.imports.iter().any(|i| !i.modeled));
                    assert!(image.image.function.relocations.is_empty());
                    let mut stubs = 0;
                    for offset in 0..image.image.memory.len().saturating_sub(10) {
                        if image
                            .plt_slot(image.image.memory_base + offset as u64)
                            .is_some_and(|s| s.name == "puts")
                        {
                            stubs += 1;
                        }
                    }
                    if !got {
                        assert!(stubs >= 1, "expected checked puts PLT entry");
                    }
                    assert_eq!(
                        image.image.memory
                            [(image.image.stack_pointer - image.image.memory_base) as usize..],
                        vec![0; 8]
                    );
                }
            }
        }
    }
}

#[test]
fn input_limit_and_file_backed_stub_boundaries_are_enforced() {
    let bytes = vec![0; 64 * 1024 * 1024 + 1];
    assert!(matches!(load(&bytes), Err(BinaryError::Limit(_))));
    let mut image = load(&fixture()).unwrap();
    let base = image.image.memory_base;
    // The executable PT_LOAD's BSS is valid guest RAM, but does not prove a PLT.
    image.image.memory[0x800..0x806].copy_from_slice(&[0xff, 0x25, 0x7a, 0xfc, 0xff, 0xff]);
    assert!(image.plt_slot(base + 0x800).is_none());
    image.image.memory[0x7fd..0x803].copy_from_slice(&[0xff, 0x25, 0x7d, 0xfc, 0xff, 0xff]);
    assert!(image.plt_slot(base + 0x7fd).is_none());
}

#[test]
fn symbolic_relocations_require_a_proven_dynamic_symbol_extent() {
    let mut bytes = fixture();
    // Remove DT_HASH, retaining only a DT_INIT tag. A matching SHT_DYNSYM
    // extent proves the exact DT_SYMTAB bytes without consulting its name.
    put64(&mut bytes, 0x180 + 4 * 16, 12);
    put64(&mut bytes, 0x188 + 4 * 16, 0);
    assert!(load(&bytes).is_ok());
    // A static symbol table can still select fixture, but cannot prove the
    // extent of the dynamic table used by the relocation records.
    put32(&mut bytes, 0x500 + 3 * 64 + 4, 2);
    assert!(
        load(&bytes)
            .unwrap_err()
            .to_string()
            .contains("no proven bound")
    );
}

#[test]
fn gnu_hash_bounds_sectionless_exports_and_empty_hash_needs_another_bound() {
    let mut bytes = fixture();
    put64(&mut bytes, 0x180 + 4 * 16, 0x6fff_fef5);
    bytes[0x3d0..0x400].fill(0);
    put32(&mut bytes, 0x3d0, 1); // nbuckets
    put32(&mut bytes, 0x3d4, 1); // symoffset
    put32(&mut bytes, 0x3d8, 1); // bloom size
    put32(&mut bytes, 0x3e8, 1); // bucket: fixture, puts, weak CRT
    put32(&mut bytes, 0x3f4, 1); // final chain bit
    assert!(load(&bytes).is_ok());
    put64(&mut bytes, 40, 0);
    put16(&mut bytes, 60, 0);
    assert!(load(&bytes).is_ok());
    put32(&mut bytes, 0x3e8, 0);
    assert!(load(&bytes).is_err());
    let mut bytes = fixture();
    put64(&mut bytes, 0x180 + 4 * 16, 0x6fff_fef5);
    bytes[0x3d0..0x400].fill(0);
    put32(&mut bytes, 0x3d0, 1);
    put32(&mut bytes, 0x3d4, 1);
    put32(&mut bytes, 0x3d8, 1);
    assert!(load(&bytes).is_ok());
    put32(&mut bytes, 0x3d8, 3);
    assert!(load(&bytes).is_err());
}

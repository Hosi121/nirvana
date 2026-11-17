//! Scalar MOVBE uses exactly one existing-width memory access and no flags.
use nirvana::ir::{AccessKind, RunStatus, Width};
use nirvana::x86::{self, LiftError, Operand, Operation};

#[allow(dead_code)]
#[path = "support/native.rs"]
mod native;

fn code(width: Width, store: bool, register: u8, base: u8) -> Vec<u8> {
    let mut bytes = Vec::new();
    if width == Width::U16 {
        bytes.push(0x66);
    }
    let rex = 0x40 | if width == Width::U64 { 8 } else { 0 } | ((register >> 3) << 2) | (base >> 3);
    if rex != 0x40 {
        bytes.push(rex);
    }
    bytes.extend([
        0x0f,
        0x38,
        if store { 0xf1 } else { 0xf0 },
        0x40 | ((register & 7) << 3) | (base & 7),
    ]);
    if base & 7 == 4 {
        bytes.push(0x24);
    } // SIB without an index for RSP/R12.
    bytes.extend([0, 0xc3]);
    bytes
}

#[cfg(target_arch = "x86_64")]
fn evidence_directory(label: &str) -> std::path::PathBuf {
    let nonce = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("target/movbe-tests")
        .join(format!("{label}-{}-{nonce}", std::process::id()));
    std::fs::create_dir_all(&path).unwrap();
    path
}

#[test]
fn decodes_only_same_width_register_memory_forms_with_rex_extensions() {
    for width in [Width::U16, Width::U32, Width::U64] {
        for store in [false, true] {
            for register in 0..16 {
                for base in 0..16 {
                    let bytes = code(width, store, register, base);
                    let decoded = x86::decode_at(&bytes, 0).unwrap();
                    let Operation::Movbe {
                        destination,
                        source,
                    } = decoded.operation
                    else {
                        panic!()
                    };
                    assert_eq!(decoded.size as usize, bytes.len() - 1);
                    let (actual_register, memory) = if store {
                        (source, destination)
                    } else {
                        (destination, source)
                    };
                    let Operand::Register(actual) = actual_register else {
                        panic!()
                    };
                    assert_eq!(
                        (actual.index, actual.width, actual.shift),
                        (register, width, 0)
                    );
                    let Operand::Memory {
                        address,
                        width: actual,
                    } = memory
                    else {
                        panic!()
                    };
                    assert_eq!(
                        (actual, address.base, address.displacement),
                        (width, Some(base), 0)
                    );
                }
            }
        }
    }
    let Operation::Movbe {
        source: Operand::Memory { address, width },
        destination: Operand::Register(reg),
    } = x86::decode_at(&[0x4f, 0x0f, 0x38, 0xf0, 0x44, 0xf5, 0xe0], 0)
        .unwrap()
        .operation
    else {
        panic!()
    };
    assert_eq!(
        (
            reg.index,
            width,
            address.base,
            address.index,
            address.scale,
            address.displacement
        ),
        (8, Width::U64, Some(13), Some(14), 8, -32)
    );
    // 66+REX.W is a quadword, never a byte form.
    let Operation::Movbe { destination, .. } =
        x86::decode_at(&[0x66, 0x48, 0x0f, 0x38, 0xf0, 0x00], 0)
            .unwrap()
            .operation
    else {
        panic!()
    };
    assert_eq!(destination.width(), Some(Width::U64));
}

#[test]
fn rejects_register_pairs_lock_repeat_crc32_and_truncation() {
    for bytes in [
        &[0x0f, 0x38, 0xf0, 0xc0][..],
        &[0x0f, 0x38, 0xf1, 0xc0],
        &[0x66, 0x0f, 0x38, 0xf0, 0xc0],
        &[0x48, 0x0f, 0x38, 0xf1, 0xc0],
        &[0xf0, 0x0f, 0x38, 0xf0, 0x00],
        &[0xf0, 0x0f, 0x38, 0xf1, 0x00],
        &[0xf3, 0x0f, 0x38, 0xf0, 0x00],
        &[0xf3, 0x0f, 0x38, 0xf1, 0x00],
        &[0xf2, 0x0f, 0x38, 0xf0, 0x00],
        &[0xf2, 0x0f, 0x38, 0xf1, 0x00],
        &[0xf2, 0x0f, 0x38, 0xf0, 0xc0], // CRC32 byte source, not MOVBE.
        &[0x0f, 0x38],
        &[0x0f, 0x38, 0xf0],
        &[0x0f, 0x38, 0xf2, 0x00],
    ] {
        assert!(x86::decode_at(bytes, 0).is_err(), "{bytes:02x?}");
    }
}

fn seed_flags(registers: &mut [u64], pattern: u64) -> u64 {
    let mut seed = 0x202 | (((pattern >> 5) & 1) << 4); // AF is also poisoned.
    for (i, (reg, bit)) in [
        (x86::CF, 0),
        (x86::PF, 2),
        (x86::ZF, 6),
        (x86::SF, 7),
        (x86::OF, 11),
    ]
    .into_iter()
    .enumerate()
    {
        registers[reg] = (pattern >> i) & 1;
        seed |= registers[reg] << bit;
    }
    seed
}

#[cfg(target_arch = "x86_64")]
fn has_movbe() -> bool {
    // Intel SDM MOVBE: CPUID.01H:ECX[22]. Native tests require this feature;
    // all decoder/IR/fault tests remain active on hosts without it.
    std::arch::x86_64::__cpuid(1).ecx & (1 << 22) != 0
}

#[cfg(target_arch = "x86_64")]
fn native_movbe(
    width: Width,
    store: bool,
    high: bool,
    alias: bool,
    initial: u64,
    address: u64,
    seed: u64,
) -> (u64, u64) {
    use std::arch::asm;
    let mut value = initial;
    let flags: u64;
    macro_rules! instruction {
        ($op:literal, $reg:tt, $address:tt) => {
            unsafe { asm!("push {seed}", "popfq", $op, "pushfq", "pop rdx", seed=in(reg) seed, inout($reg) value, in($address) address, lateout("rdx") flags); }
        };
    }
    match (width, store, high, alias) {
        (Width::U16, false, false, false) => instruction!("movbe ax, word ptr [rdi]", "rax", "rdi"),
        (Width::U32, false, false, false) => {
            instruction!("movbe eax, dword ptr [rdi]", "rax", "rdi")
        }
        (Width::U64, false, false, false) => {
            instruction!("movbe rax, qword ptr [rdi]", "rax", "rdi")
        }
        (Width::U16, true, false, false) => instruction!("movbe word ptr [rdi], ax", "rax", "rdi"),
        (Width::U32, true, false, false) => {
            instruction!("movbe dword ptr [rdi], eax", "rax", "rdi")
        }
        (Width::U64, true, false, false) => {
            instruction!("movbe qword ptr [rdi], rax", "rax", "rdi")
        }
        (Width::U16, false, false, true) => instruction!("movbe ax, word ptr [rax]", "rax", "rdi"),
        (Width::U32, false, false, true) => {
            instruction!("movbe eax, dword ptr [rax]", "rax", "rdi")
        }
        (Width::U64, false, false, true) => {
            instruction!("movbe rax, qword ptr [rax]", "rax", "rdi")
        }
        (Width::U16, true, false, true) => instruction!("movbe word ptr [rax], ax", "rax", "rdi"),
        (Width::U32, true, false, true) => instruction!("movbe dword ptr [rax], eax", "rax", "rdi"),
        (Width::U64, true, false, true) => instruction!("movbe qword ptr [rax], rax", "rax", "rdi"),
        (Width::U16, false, true, false) => instruction!("movbe r8w, word ptr [r9]", "r8", "r9"),
        (Width::U32, false, true, false) => instruction!("movbe r8d, dword ptr [r9]", "r8", "r9"),
        (Width::U64, false, true, false) => instruction!("movbe r8, qword ptr [r9]", "r8", "r9"),
        (Width::U16, true, true, false) => instruction!("movbe word ptr [r9], r8w", "r8", "r9"),
        (Width::U32, true, true, false) => instruction!("movbe dword ptr [r9], r8d", "r8", "r9"),
        (Width::U64, true, true, false) => instruction!("movbe qword ptr [r9], r8", "r8", "r9"),
        (Width::U16, false, true, true) => instruction!("movbe r8w, word ptr [r8]", "r8", "r9"),
        (Width::U32, false, true, true) => instruction!("movbe r8d, dword ptr [r8]", "r8", "r9"),
        (Width::U64, false, true, true) => instruction!("movbe r8, qword ptr [r8]", "r8", "r9"),
        (Width::U16, true, true, true) => instruction!("movbe word ptr [r8], r8w", "r8", "r9"),
        (Width::U32, true, true, true) => instruction!("movbe dword ptr [r8], r8d", "r8", "r9"),
        (Width::U64, true, true, true) => instruction!("movbe qword ptr [r8], r8", "r8", "r9"),
        _ => unreachable!(),
    }
    (value, flags)
}

#[test]
#[cfg(target_arch = "x86_64")]
fn native_memory_values_partial_registers_aliases_unaligned_access_and_all_flags() {
    if !has_movbe() {
        eprintln!("native MOVBE oracle unavailable: CPUID.MOVBE=0");
        return;
    }
    let mut comparisons = 0;
    for width in [Width::U16, Width::U32, Width::U64] {
        for store in [false, true] {
            for high in [false, true] {
                let reg = if high { 8 } else { 0 };
                for alias in [false, true] {
                    let base = if alias {
                        reg
                    } else if high {
                        9
                    } else {
                        7
                    };
                    let program = x86::lift(&code(width, store, reg, base), 0, 0).unwrap();
                    for offset in [0, 1, 3, 7] {
                        for value in [
                            0,
                            1,
                            u64::MAX,
                            0x1234_5678_9abc_def0,
                            0x8000_0000_8000_8000,
                            0xffff_ffff_0000_0001,
                        ] {
                            for pattern in 0..64 {
                                let mut memory = [0u8; 24];
                                for (i, byte) in memory.iter_mut().enumerate() {
                                    *byte = (i * 37 + 13) as u8;
                                }
                                let datum = value.rotate_left(13) ^ 0x1020_3040_5060_7080;
                                memory[offset..offset + 8].copy_from_slice(&datum.to_le_bytes());
                                let origin = memory.as_mut_ptr() as u64;
                                let address = origin + offset as u64;
                                let mut registers: Vec<_> = (0..x86::REGISTER_COUNT)
                                    .map(|i| 0x8765_4321_1234_5678u64.wrapping_add(i as u64))
                                    .collect();
                                let seed = seed_flags(&mut registers, pattern);
                                registers[reg as usize] = if alias { address } else { value };
                                registers[base as usize] = address;
                                let initial = registers[reg as usize];
                                let actual = program
                                    .execute_with_memory(&registers, origin, &memory, 2)
                                    .unwrap();
                                let (native_value, flags) =
                                    native_movbe(width, store, high, alias, initial, address, seed);
                                assert_eq!(
                                    actual.memory, memory,
                                    "{width:?} store={store} high={high} alias={alias} offset={offset}"
                                );
                                assert_eq!(actual.registers[reg as usize], native_value);
                                assert_eq!(flags & 0x8d5, seed & 0x8d5);
                                for flag in [x86::CF, x86::PF, x86::ZF, x86::SF, x86::OF] {
                                    assert_eq!(actual.registers[flag], registers[flag]);
                                }
                                for (other, before) in registers.iter().enumerate().take(16) {
                                    if other != reg as usize || store {
                                        assert_eq!(
                                            actual.registers[other],
                                            before.wrapping_add(u64::from(other == x86::RSP) * 8)
                                        );
                                    }
                                }
                                comparisons += 1;
                            }
                        }
                    }
                }
            }
        }
    }
    println!("{comparisons} native MOVBE comparisons");
}

#[test]
fn faults_have_exact_read_or_write_width_and_preserve_the_successful_prefix() {
    for width in [Width::U16, Width::U32, Width::U64] {
        for store in [false, true] {
            for address in [0xfff, 0x1000 + 17 - width.bytes() as u64, u64::MAX] {
                let mut bytes = vec![0xc6, 0x06, 0x5a]; // MOV byte [RSI],0x5a commits first.
                bytes.extend(code(width, store, 0, 7));
                let program = x86::lift(&bytes, 0, 0).unwrap();
                let mut registers = vec![0; x86::REGISTER_COUNT];
                registers[x86::RAX] = 0x1234_5678_9abc_def0;
                registers[x86::RSI] = 0x1000;
                registers[x86::RDI] = address;
                seed_flags(&mut registers, 63);
                let report = program
                    .run_with_memory(&registers, 0x1000, &[0; 16], 3)
                    .unwrap();
                assert!(
                    matches!(report.status, RunStatus::Fault(fault) if fault.access == if store { AccessKind::Write } else { AccessKind::Read } && fault.width == width && fault.address == address)
                );
                let mut expected = vec![0; 16];
                expected[0] = 0x5a;
                assert_eq!(report.state.memory, expected);
                assert_eq!(report.state.trace, [0, 3]);
                assert_eq!(report.state.registers[..21], registers[..21]);
            }
            // An access ending exactly at the bound succeeds, with one full-width access.
            let program = x86::lift(&code(width, store, 0, 7), 0, 0).unwrap();
            let mut registers = vec![0; x86::REGISTER_COUNT];
            registers[x86::RDI] = 0x1000 + 16 - width.bytes() as u64;
            program
                .execute_with_memory(&registers, 0x1000, &[0x39; 16], 2)
                .unwrap();
        }
    }
}

#[test]
fn flags_are_preserved_instead_of_defined_and_rip_relative_addresses_include_the_opcode() {
    for width in [Width::U16, Width::U32, Width::U64] {
        for store in [false, true] {
            for condition in [0, 2, 4, 8, 10] {
                let mut bytes = code(width, store, 0, 7);
                bytes.pop();
                bytes.extend([0x70 | condition, 0, 0xc3]);
                assert!(matches!(
                    x86::lift(&bytes, 0, 0),
                    Err(LiftError::UndefinedFlags { .. })
                ));
                bytes.splice(0..0, [0x39, 0xd2]);
                assert!(x86::lift(&bytes, 0, 0).is_ok());
            }
            let mut bytes = Vec::new();
            match width {
                Width::U16 => bytes.push(0x66),
                Width::U64 => bytes.push(0x48),
                _ => {}
            }
            bytes.extend([
                0x0f,
                0x38,
                if store { 0xf1 } else { 0xf0 },
                0x05,
                16,
                0,
                0,
                0,
                0xc3,
            ]);
            let next = bytes.len() - 1;
            let program = x86::lift(&bytes, 0x1000, 0x1000).unwrap();
            let mut registers = vec![0; x86::REGISTER_COUNT];
            registers[x86::RAX] = 0x1234_5678_9abc_def0;
            let memory: Vec<_> = (0..64).map(|i| i as u8).collect();
            let actual = program
                .execute_with_memory(&registers, 0x1000, &memory, 2)
                .unwrap();
            let mut expected = memory.clone();
            if store {
                let value = registers[x86::RAX] & width.mask();
                let mut swapped = value.to_le_bytes()[..width.bytes()].to_vec();
                swapped.reverse();
                expected[next + 16..next + 16 + width.bytes()].copy_from_slice(&swapped);
                assert_eq!(actual.memory, expected);
            } else {
                let value = memory[next + 16..next + 16 + width.bytes()]
                    .iter()
                    .fold(0u64, |n, byte| (n << 8) | u64::from(*byte));
                let expected = if width == Width::U16 {
                    (registers[x86::RAX] & !width.mask()) | value
                } else {
                    value
                };
                assert_eq!(actual.value, expected);
            }
        }
    }
}

fn target_object(
    source: &std::path::Path,
    output: &std::path::Path,
    optimization: &str,
    entry: &str,
) {
    let result = std::process::Command::new("cc")
        .args([
            "-std=c11",
            "-Wall",
            "-Wextra",
            "-Werror",
            "-pedantic",
            "-fno-lto",
            "-mmovbe",
            optimization,
        ])
        .arg(format!("-DFIXTURE_ENTRY={entry}"))
        .arg("-c")
        .arg(source)
        .arg("-o")
        .arg(output)
        .output()
        .unwrap();
    std::fs::write(output.with_extension("compiler-stderr"), &result.stderr).unwrap();
    assert!(
        result.status.success(),
        "{optimization} -mmovbe: {}",
        String::from_utf8_lossy(&result.stderr)
    );
}

fn digest(memory: &[u8]) -> u64 {
    memory.iter().fold(0xcbf29ce484222325, |hash, byte| {
        (hash ^ u64::from(*byte)).wrapping_mul(0x100000001b3)
    })
}

fn harness(call: &str) -> String {
    format!(
        r#"
#include <inttypes.h>
#include <stdio.h>
#include <string.h>
int main(void) {{
    uint64_t input[4];
    while (scanf("%" SCNu64 " %" SCNu64 " %" SCNu64 " %" SCNu64,
                 &input[0], &input[1], &input[2], &input[3]) == 4) {{
        uint64_t r[32] = {{0}};
        uint8_t memory[65536];
        memset(memory, 0, sizeof(memory));
        r[7] = UINT64_C(8192); r[4] = UINT64_C(65536);
        for (unsigned i = 0; i < 4; ++i)
            for (unsigned j = 0; j < 8; ++j) memory[4096 + i * 8 + j] = (uint8_t)(input[i] >> (j * 8));
        uint64_t result = {call};
        for (unsigned i = 0; i < 4; ++i) {{
            input[i] = 0;
            for (unsigned j = 0; j < 8; ++j) input[i] |= (uint64_t)memory[4096 + i * 8 + j] << (j * 8);
        }}
        uint64_t hash = UINT64_C(14695981039346656037);
        for (unsigned i = 0; i < sizeof(memory); ++i) hash = (hash ^ memory[i]) * UINT64_C(1099511628211);
        printf("%" PRIu64 " %" PRIu64 " %" PRIu64 " %" PRIu64 " %" PRIu64 " %" PRIu64 "\n",
               result, input[0], input[1], input[2], input[3], hash);
    }}
    return 0;
}}
"#
    )
}

#[test]
#[cfg(target_arch = "x86_64")]
fn movbe_target_c_fixture_matches_native_ir_and_recompiled_c_full_memory() {
    use nirvana::{emit, frontend, readable};
    use std::fmt::Write as _;
    if !has_movbe() {
        eprintln!("native MOVBE fixture unavailable: CPUID.MOVBE=0");
        return;
    }
    let directory = evidence_directory("fixture");
    let mut inputs = Vec::new();
    for count in [0, 1, 2, 7, 8, 15, 16, 31, 32, 63, 64, 65, 255, u64::MAX] {
        for value in [0, 1, u64::MAX, 0x1234_5678_9abc_def0, 0x8000_8000_8000_8080] {
            inputs.push([value, count, !value, value.rotate_left(17)]);
        }
    }
    let mut text = String::new();
    for input in &inputs {
        writeln!(text, "{} {} {} {}", input[0], input[1], input[2], input[3]).unwrap();
    }
    let root = native::fixture_root();
    for optimization in ["-O0", "-O2"] {
        let directory = directory.join(optimization);
        std::fs::create_dir(&directory).unwrap();
        let original_object = directory.join("move-endian.o");
        target_object(
            &root.join("recovery/move-endian.c"),
            &original_object,
            optimization,
            "fixture",
        );
        let original_harness = directory.join("harness.o");
        native::object(
            &root.join("harness.c"),
            &original_harness,
            optimization,
            "fixture",
        );
        let original = directory.join("original");
        native::link(&[&original_object, &original_harness], &original);
        let function =
            frontend::lift_elf(&std::fs::read(&original_object).unwrap(), "fixture").unwrap();
        let decoded = x86::decode_reachable(
            &function.image.bytes,
            function.image.address,
            function.image.address,
        )
        .unwrap();
        let forms: Vec<_> = decoded
            .iter()
            .filter_map(|instruction| match instruction.operation {
                Operation::Movbe {
                    destination,
                    source,
                } => Some((
                    matches!(destination, Operand::Memory { .. }),
                    destination.width().unwrap(),
                    source.width().unwrap(),
                )),
                _ => None,
            })
            .collect();
        assert!(
            forms
                .iter()
                .all(|(_, destination, source)| destination == source)
        );
        if optimization == "-O2" {
            assert!(!forms.is_empty(), "-O2 -mmovbe did not generate MOVBE");
            assert!(forms.iter().any(|(store, _, _)| *store));
            assert!(forms.iter().any(|(store, _, _)| !*store));
        }
        println!("{optimization} native MOVBE forms (store,width,width): {forms:?}");
        let expected = native::run(&original, &text);
        let mut memory_expected = Vec::new();
        for (input, expected) in inputs.iter().zip(&expected) {
            let mut registers = vec![0; x86::REGISTER_COUNT];
            registers[x86::RSP] = 65536;
            registers[x86::RDI] = 8192;
            let mut memory = vec![0; 65536];
            for (i, value) in input.iter().enumerate() {
                memory[4096 + i * 8..4096 + i * 8 + 8].copy_from_slice(&value.to_le_bytes());
            }
            let actual = function
                .program
                .execute_with_memory(&registers, 4096, &memory, 10_000)
                .unwrap();
            let mut visible = vec![actual.value];
            for i in 0..4 {
                visible.push(u64::from_le_bytes(
                    actual.memory[4096 + i * 8..4096 + i * 8 + 8]
                        .try_into()
                        .unwrap(),
                ));
            }
            assert_eq!(&visible, expected, "{optimization} {input:?}");
            visible.push(digest(&actual.memory));
            memory_expected.push(visible);
        }
        let raw = emit::emit_c(&function.program).unwrap();
        let mut rendered = vec![(
            "raw",
            raw.code,
            "nirvana_fn(r, memory, UINT64_C(4096), sizeof(memory))".to_owned(),
        )];
        for compact in [false, true] {
            let output = readable::emit_readable_c_with_options(
                &function.program,
                readable::ReadableOptions {
                    stack_register: Some(nirvana::ir::Reg(x86::RSP)),
                    recover_objects: true,
                    coalesce_locals: true,
                    compact_memory: compact,
                },
            )
            .unwrap();
            let mut args: Vec<_> = output
                .parameters
                .iter()
                .map(|reg| format!("r[{}]", reg.0))
                .collect();
            if output.uses_memory {
                args.extend(["memory", "UINT64_C(4096)", "sizeof(memory)"].map(String::from));
            }
            rendered.push((
                if compact { "compact" } else { "readable" },
                output.code,
                format!("nirvana_readable({})", args.join(", ")),
            ));
        }
        for (style, code, call) in rendered {
            let source = directory.join(format!("{style}.c"));
            std::fs::write(&source, code + &harness(&call)).unwrap();
            for c_optimization in ["-O0", "-O2"] {
                let object = directory.join(format!("{style}{c_optimization}.o"));
                let binary = directory.join(format!("{style}{c_optimization}"));
                native::object(&source, &object, c_optimization, "unused");
                native::link(&[&object], &binary);
                assert_eq!(
                    native::run_fields(&binary, &text, 6),
                    memory_expected,
                    "{optimization} {style} {c_optimization}"
                );
            }
        }
    }
}

#[test]
#[cfg(target_arch = "x86_64")]
fn scaled_index_alias_uses_the_old_full_register_even_when_the_address_wraps() {
    if !has_movbe() {
        eprintln!("native MOVBE oracle unavailable: CPUID.MOVBE=0");
        return;
    }
    use std::arch::asm;
    for width in [Width::U16, Width::U32, Width::U64] {
        for store in [false, true] {
            let mut bytes = Vec::new();
            if width == Width::U16 {
                bytes.push(0x66);
            }
            bytes.extend([
                if width == Width::U64 { 0x4f } else { 0x47 },
                0x0f,
                0x38,
                if store { 0xf1 } else { 0xf0 },
                0x04,
                0xc1,
                0xc3,
            ]); // [R9 + R8*8], register R8
            let program = x86::lift(&bytes, 0, 0).unwrap();
            for input in [0, 1, u64::MAX, 0x1234_5678_9abc_def0, 1 << 63] {
                let mut memory = [0x39u8; 32];
                memory[3..11].copy_from_slice(&0x1234_5678_9abc_def0u64.to_le_bytes());
                let origin = memory.as_mut_ptr() as u64;
                let base = origin.wrapping_add(3).wrapping_sub(input.wrapping_mul(8));
                let mut registers = vec![0; x86::REGISTER_COUNT];
                registers[8] = input;
                registers[9] = base;
                let seed = seed_flags(&mut registers, 63);
                let actual = program
                    .execute_with_memory(&registers, origin, &memory, 2)
                    .unwrap();
                let mut native = input;
                let flags: u64;
                macro_rules! instruction {
                    ($op:literal) => { unsafe { asm!("push {seed}", "popfq", $op, "pushfq", "pop rdx", seed=in(reg) seed, inout("r8") native, in("r9") base, lateout("rdx") flags); } };
                }
                match (width, store) {
                    (Width::U16, false) => instruction!("movbe r8w, word ptr [r9 + r8*8]"),
                    (Width::U32, false) => instruction!("movbe r8d, dword ptr [r9 + r8*8]"),
                    (Width::U64, false) => instruction!("movbe r8, qword ptr [r9 + r8*8]"),
                    (Width::U16, true) => instruction!("movbe word ptr [r9 + r8*8], r8w"),
                    (Width::U32, true) => instruction!("movbe dword ptr [r9 + r8*8], r8d"),
                    (Width::U64, true) => instruction!("movbe qword ptr [r9 + r8*8], r8"),
                    _ => unreachable!(),
                }
                assert_eq!(actual.memory, memory);
                assert_eq!(actual.registers[8], native);
                assert_eq!(actual.registers[9], base);
                assert_eq!(flags & 0x8d5, seed & 0x8d5);
            }
        }
    }
}

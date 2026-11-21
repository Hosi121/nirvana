//! Intel SDM vol. 2B, RCL/RCR/ROL/ROR; independent native instruction oracle.
use nirvana::ir::{AccessKind, Reg, RunStatus, Width};
use nirvana::x86::{self, LiftError, Operand, Operation, Rotate};

use crate::support::native;

fn code(width: Width, right: bool, rm: u8, memory: bool, count: Option<u8>) -> Vec<u8> {
    let mut code = Vec::new();
    match width {
        Width::U16 => code.push(0x66),
        Width::U64 => code.push(0x48),
        _ => {}
    }
    code.push(match (width == Width::U8, count) {
        (true, Some(_)) => 0xc0,
        (false, Some(_)) => 0xc1,
        (true, None) => 0xd2,
        (false, None) => 0xd3,
    });
    code.push((if memory { 0 } else { 0xc0 }) | (u8::from(right) * 8) | rm);
    if let Some(count) = count {
        code.push(count);
    }
    code.push(0xc3);
    code
}

#[cfg(target_arch = "x86_64")]
fn native_rotate(
    width: Width,
    right: bool,
    high: bool,
    rcx: bool,
    value: u64,
    count: u8,
    seed: u64,
) -> (u64, u64) {
    use std::arch::asm;
    let mut value = value;
    let flags: u64;
    macro_rules! rotate {
        ($op:literal) => {
            // Only ordinary user-modifiable arithmetic flag bits are seeded.
            unsafe {
                asm!("push {seed}", "popfq", $op, "pushfq", "pop rdx",
                    seed = in(reg) seed, inout("rax") value,
                    in("rcx") u64::from(count), lateout("rdx") flags);
            }
        };
    }
    macro_rules! alias {
        ($op:literal) => {
            unsafe {
                asm!("push {seed}", "popfq", $op, "pushfq", "pop rdx",
                    seed = in(reg) seed, inout("rcx") value, lateout("rdx") flags);
            }
        };
    }
    match (width, right, high, rcx) {
        (Width::U8, false, false, false) => rotate!("rol al, cl"),
        (Width::U8, true, false, false) => rotate!("ror al, cl"),
        (Width::U8, false, true, false) => rotate!("rol ah, cl"),
        (Width::U8, true, true, false) => rotate!("ror ah, cl"),
        (Width::U16, false, _, false) => rotate!("rol ax, cl"),
        (Width::U16, true, _, false) => rotate!("ror ax, cl"),
        (Width::U32, false, _, false) => rotate!("rol eax, cl"),
        (Width::U32, true, _, false) => rotate!("ror eax, cl"),
        (Width::U64, false, _, false) => rotate!("rol rax, cl"),
        (Width::U64, true, _, false) => rotate!("ror rax, cl"),
        (Width::U8, false, false, true) => alias!("rol cl, cl"),
        (Width::U8, true, false, true) => alias!("ror cl, cl"),
        (Width::U8, false, true, true) => alias!("rol ch, cl"),
        (Width::U8, true, true, true) => alias!("ror ch, cl"),
        (Width::U16, false, _, true) => alias!("rol cx, cl"),
        (Width::U16, true, _, true) => alias!("ror cx, cl"),
        (Width::U32, false, _, true) => alias!("rol ecx, cl"),
        (Width::U32, true, _, true) => alias!("ror ecx, cl"),
        (Width::U64, false, _, true) => alias!("rol rcx, cl"),
        (Width::U64, true, _, true) => alias!("ror rcx, cl"),
    }
    (value, flags)
}

fn seed_flags(registers: &mut [u64], seed: u64) {
    for (reg, bit) in [
        (x86::CF, 0),
        (x86::PF, 2),
        (x86::ZF, 6),
        (x86::SF, 7),
        (x86::OF, 11),
    ] {
        registers[reg] = (seed >> bit) & 1;
    }
}

#[test]
#[cfg(target_arch = "x86_64")]
fn native_register_rotates_match_values_flags_aliases_and_masked_counts() {
    let values = [
        0,
        1,
        u64::MAX,
        0x1234_5678_9abc_def0,
        0x8000_8000_8000_8080,
        0x7fff_7fff_7fff_7f7f,
    ];
    let counts = [0, 1, 2, 7, 8, 9, 15, 16, 17, 31, 32, 33, 63, 64, 65, 255];
    for width in [Width::U8, Width::U16, Width::U32, Width::U64] {
        for right in [false, true] {
            for high in [false, true]
                .into_iter()
                .filter(|high| !high || width == Width::U8)
            {
                for alias in [false, true] {
                    for immediate in [false, true]
                        .into_iter()
                        .filter(|immediate| !alias || !immediate)
                    {
                        for count in counts {
                            let rm = u8::from(alias) + if high { 4 } else { 0 };
                            let program = x86::lift(
                                &code(width, right, rm, false, immediate.then_some(count)),
                                0,
                                0,
                            )
                            .unwrap();
                            for value in values {
                                let value = if alias {
                                    (value & !255) | u64::from(count)
                                } else {
                                    value
                                };
                                for seed in [0x202, 0xad7, 0xa03, 0x2d6] {
                                    let mut registers = vec![0; x86::REGISTER_COUNT];
                                    registers[x86::RAX] = value;
                                    registers[x86::RCX] =
                                        if alias { value } else { u64::from(count) };
                                    seed_flags(&mut registers, seed);
                                    let actual = program.execute(&registers, 2).unwrap();
                                    let (expected, flags) = native_rotate(
                                        width, right, high, alias, value, count, seed,
                                    );
                                    assert_eq!(
                                        actual.registers[if alias { x86::RCX } else { x86::RAX }],
                                        expected,
                                        "{width:?} right={right} high={high} alias={alias} immediate={immediate} count={count} value={value:#x}"
                                    );
                                    let masked = count & if width == Width::U64 { 63 } else { 31 };
                                    for (reg, bit) in [
                                        (x86::CF, 0),
                                        (x86::PF, 2),
                                        (x86::ZF, 6),
                                        (x86::SF, 7),
                                        (x86::OF, 11),
                                    ] {
                                        if reg != x86::OF || masked <= 1 {
                                            assert_eq!(
                                                actual.registers[reg],
                                                (flags >> bit) & 1,
                                                "{width:?} right={right} count={count} flag={reg} value={value:#x} seed={seed:#x}"
                                            );
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn opcode_forms_and_rex_byte_registers_decode_without_accepting_through_carry() {
    for (opcode, byte) in [
        (0xc0, true),
        (0xc1, false),
        (0xd0, true),
        (0xd1, false),
        (0xd2, true),
        (0xd3, false),
    ] {
        for group in 0..4 {
            let bytes = [opcode, 0xc0 | (group * 8), 1];
            if group >= 2 {
                assert!(x86::decode_at(&bytes, 0).is_err());
                continue;
            }
            let instruction = x86::decode_at(&bytes, 0).unwrap();
            let Operation::Rotate {
                kind,
                destination,
                count,
            } = instruction.operation
            else {
                panic!()
            };
            assert_eq!(
                kind,
                if group == 0 {
                    Rotate::Left
                } else {
                    Rotate::Right
                }
            );
            assert_eq!(
                destination.width(),
                Some(if byte { Width::U8 } else { Width::U32 })
            );
            if opcode == 0xd0 || opcode == 0xd1 {
                assert_eq!(count, Operand::Immediate(1));
            }
        }
    }
    let Operation::Rotate {
        destination: Operand::Register(reg),
        ..
    } = x86::decode_at(&[0x40, 0xd0, 0xc4], 0).unwrap().operation
    else {
        panic!()
    };
    assert_eq!((reg.index, reg.shift), (4, 0)); // SPL with REX, AH without it.
    assert!(x86::decode_at(&[0xf0, 0xd0, 0x07], 0).is_err());
}

fn flag_program(
    width: Width,
    count: Option<u8>,
    seeded: bool,
    condition: u8,
) -> Result<nirvana::ir::Program, LiftError> {
    let mut bytes = if seeded { vec![0x39, 0xd2] } else { Vec::new() }; // cmp edx,edx
    let mut rotate = code(width, false, 0, false, count);
    rotate.pop();
    bytes.extend(rotate);
    bytes.extend([0x0f, 0x90 | condition, 0xc3, 0xc3]); // SETcc BL; RET
    x86::lift(&bytes, 0, 0)
}

#[test]
fn undefined_flag_checker_uses_masked_count_before_small_width_modulo() {
    for width in [Width::U8, Width::U16, Width::U32, Width::U64] {
        for count in [0, 1, 8, 9, 16, 17, 31, 32, 63, 64, 255] {
            let masked = count & if width == Width::U64 { 63 } else { 31 };
            for seeded in [false, true] {
                assert_eq!(
                    flag_program(width, Some(count), seeded, 2).is_ok(),
                    seeded || masked != 0,
                    "CF {width:?} {count}"
                );
                assert_eq!(
                    flag_program(width, Some(count), seeded, 0).is_ok(),
                    masked == 1 || (masked == 0 && seeded),
                    "OF {width:?} {count}"
                );
                for condition in [4, 8, 10] {
                    // ZF, SF, PF
                    assert_eq!(
                        flag_program(width, Some(count), seeded, condition).is_ok(),
                        seeded
                    );
                }
            }
        }
        assert!(flag_program(width, None, true, 2).is_ok());
        assert!(flag_program(width, None, false, 2).is_err());
        assert!(flag_program(width, None, true, 0).is_err());
        assert!(flag_program(width, None, false, 4).is_err());
        assert!(flag_program(width, None, true, 4).is_ok());
    }
}

#[test]
fn memory_rotates_preserve_neighbours_and_zero_count_read_fault_prefix() {
    for width in [Width::U8, Width::U16, Width::U32, Width::U64] {
        for right in [false, true] {
            for count in [0, 1, width.bits() as u8, 31, 32, 63, 64, 255] {
                let program = x86::lift(&code(width, right, 7, true, Some(count)), 0, 0).unwrap();
                let mut registers = vec![0; x86::REGISTER_COUNT];
                registers[x86::RDI] = 0x1003;
                let original: Vec<u8> = (0..24).map(|i| (i * 37 + 13) as u8).collect();
                let result = program
                    .execute_with_memory(&registers, 0x1000, &original, 2)
                    .unwrap();
                let value = original[3..3 + width.bytes()]
                    .iter()
                    .rev()
                    .fold(0u64, |v, byte| (v << 8) | u64::from(*byte));
                let bits = width.bits();
                let count = u32::from(count & if width == Width::U64 { 63 } else { 31 }) % bits;
                let expected = if count == 0 {
                    value
                } else if right {
                    (value >> count) | (value << (bits - count))
                } else {
                    (value << count) | (value >> (bits - count))
                } & width.mask();
                let mut memory = original.clone();
                memory[3..3 + width.bytes()]
                    .copy_from_slice(&expected.to_le_bytes()[..width.bytes()]);
                assert_eq!(result.memory, memory);
            }
            // An earlier byte store commits; zero-count rotate then faults on its
            // destination read, before flags or the rotate store can execute.
            let mut bytes = vec![0xc6, 0x06, 0x5a]; // mov byte [rsi],0x5a
            bytes.extend(code(width, right, 7, true, Some(0)));
            let program = x86::lift(&bytes, 0, 0).unwrap();
            let mut registers = vec![0; x86::REGISTER_COUNT];
            registers[x86::RDI] = 0x2000;
            registers[x86::RSI] = 0x1000;
            seed_flags(&mut registers, 0xad7);
            let report = program
                .run_with_memory(&registers, 0x1000, &[0; 16], 3)
                .unwrap();
            assert!(
                matches!(report.status, RunStatus::Fault(fault) if fault.access == AccessKind::Read && fault.address == 0x2000 && fault.width == width)
            );
            assert_eq!(report.state.memory[0], 0x5a);
            assert_eq!(report.state.trace, vec![0, 3]);
            for reg in [x86::CF, x86::OF, x86::ZF, x86::SF, x86::PF] {
                assert_eq!(report.state.registers[reg], registers[reg]);
            }
        }
    }
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
fn real_o0_and_o2_c_rotate_fixture_matches_native_ir_and_recompiled_c_full_memory() {
    use nirvana::{emit, frontend, readable};
    use std::fmt::Write as _;
    let nonce = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    // Retain the objects, rendered C and executables as reproducible evidence.
    let directory = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("target/rotate-tests")
        .join(format!("{}-{nonce}", std::process::id()));
    std::fs::create_dir_all(&directory).unwrap();
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
        let original_object = directory.join("rotates.o");
        native::object(
            &root.join("recovery/rotates.c"),
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
        let rotations: Vec<_> = decoded
            .iter()
            .filter_map(|instruction| match instruction.operation {
                Operation::Rotate {
                    kind, destination, ..
                } => Some((kind, destination.width().unwrap())),
                _ => None,
            })
            .collect();
        assert!(
            !rotations.is_empty(),
            "{optimization} did not produce any rotate instructions"
        );
        println!("{optimization} native rotate forms: {rotations:?}");
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
                    stack_register: Some(Reg(x86::RSP)),
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
fn implicit_one_and_extended_register_destinations_match_native() {
    for width in [Width::U8, Width::U16, Width::U32, Width::U64] {
        for right in [false, true] {
            let mut implicit = code(width, right, 0, false, Some(1));
            let opcode = implicit.len() - 4;
            implicit[opcode] = if width == Width::U8 { 0xd0 } else { 0xd1 };
            implicit.remove(opcode + 2);
            let mut extended = code(width, right, 0, false, None);
            if width == Width::U64 {
                extended[0] = 0x49;
            } else {
                extended.insert(usize::from(width == Width::U16), 0x41);
            }
            for (bytes, reg, count) in [(implicit, x86::RAX, 1), (extended, 8, 255)] {
                let program = x86::lift(&bytes, 0, 0).unwrap();
                for value in [0, 1, 0x1234_5678_9abc_def0, u64::MAX] {
                    let mut registers = vec![0; x86::REGISTER_COUNT];
                    registers[reg] = value;
                    registers[x86::RCX] = count;
                    let actual = program.execute(&registers, 2).unwrap();
                    let expected =
                        native_rotate(width, right, false, false, value, count as u8, 0x202);
                    assert_eq!(actual.registers[reg], expected.0);
                }
            }
        }
    }
}

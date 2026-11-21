//! BSWAP is register-only and preserves flags. Native assembly is the oracle.
use nirvana::ir::{Reg, Width};
use nirvana::x86::{self, LiftError, Operation};
use std::fmt::Write as _;
use std::path::PathBuf;

use crate::support::native;

fn code(width: Width, register: u8) -> Vec<u8> {
    let mut bytes = Vec::new();
    let rex = 0x40 | if width == Width::U64 { 8 } else { 0 } | (register >> 3);
    if rex != 0x40 {
        bytes.push(rex);
    }
    bytes.extend([0x0f, 0xc8 | (register & 7), 0xc3]);
    bytes
}

fn evidence_directory(label: &str) -> PathBuf {
    let nonce = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("target/bswap-tests")
        .join(format!("{label}-{}-{nonce}", std::process::id()));
    std::fs::create_dir_all(&path).unwrap();
    path
}

#[test]
fn decodes_opcode_registers_widths_rex_b_and_ignored_rex_r_x() {
    for width in [Width::U32, Width::U64] {
        for register in 0..16 {
            for ignored in [0, 2, 4, 6] {
                let mut bytes = code(width, register);
                if bytes[0] == 0x0f {
                    bytes.insert(0, 0x40 | ignored);
                } else {
                    bytes[0] |= ignored;
                }
                let decoded = x86::decode_at(&bytes, 0x1000).unwrap();
                let Operation::ByteSwap { destination } = decoded.operation else {
                    panic!()
                };
                assert_eq!(
                    (destination.index, destination.width, destination.shift),
                    (register, width, 0)
                );
                assert_eq!(decoded.size as usize, bytes.len() - 1);
            }
        }
    }
    for rex in [None, Some(0x40), Some(0x41), Some(0x44), Some(0x47)] {
        let mut bytes = vec![0x66];
        bytes.extend(rex);
        bytes.extend([0x0f, 0xc8]);
        assert!(x86::decode_at(&bytes, 0).is_err());
    }
    // REX.W takes precedence over 66: this has a defined 64-bit result.
    let Operation::ByteSwap { destination } = x86::decode_at(&[0x66, 0x49, 0x0f, 0xcf], 0)
        .unwrap()
        .operation
    else {
        panic!()
    };
    assert_eq!((destination.index, destination.width), (15, Width::U64));
    for bytes in [&[0x0f][..], &[0x48, 0x0f], &[0xf0, 0x0f, 0xc8]] {
        assert!(x86::decode_at(bytes, 0).is_err());
    }
}

#[test]
fn preserves_flag_availability_instead_of_defining_entry_flags() {
    for width in [Width::U32, Width::U64] {
        for condition in [0, 2, 4, 8, 10] {
            // OF CF ZF SF PF
            let mut bytes = code(width, 8);
            bytes.pop();
            bytes.extend([0x0f, 0x90 | condition, 0xc3, 0xc3]); // SETcc BL; RET
            assert!(matches!(
                x86::lift(&bytes, 0, 0),
                Err(LiftError::UndefinedFlags { .. })
            ));
            bytes.splice(0..0, [0x39, 0xd2]); // CMP EDX,EDX makes every flag available.
            let program = x86::lift(&bytes, 0, 0).unwrap();
            let actual = program.execute(&[0; x86::REGISTER_COUNT], 5).unwrap();
            assert_eq!(
                actual.registers[x86::RBX],
                u64::from(condition == 4 || condition == 10)
            );
        }
    }
}

#[cfg(all(target_arch = "x86_64", target_os = "linux"))]
fn native_oracle(directory: &std::path::Path) -> PathBuf {
    const REGISTERS: [&str; 16] = [
        "rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi", "r8", "r9", "r10", "r11", "r12",
        "r13", "r14", "r15",
    ];
    let mut assembly = String::from(".intel_syntax noprefix\n.text\n");
    let mut source = String::from("#include <inttypes.h>\n#include <stdio.h>\n");
    let mut functions = Vec::new();
    for bits in [32, 64] {
        for (reg, name) in REGISTERS.iter().enumerate() {
            let function = format!("oracle_{bits}_{reg}");
            let pointer = if reg == 10 { "r9" } else { "r10" };
            let stack = if reg == 11 { "r8" } else { "r11" };
            writeln!(
                assembly,
                ".global {function}\n.type {function}, @function\n{function}:"
            )
            .unwrap();
            // Preserve SysV callee-saved registers and real RSP, even when the
            // instruction under test targets RSP/RBP. No memory access occurs
            // while the tested RSP contains an arbitrary input/result.
            assembly.push_str("push rbx\npush rbp\npush r12\npush r13\npush r14\npush r15\n");
            writeln!(
                assembly,
                "mov {pointer}, rdx\nmov {stack}, rsp\npush rsi\npopfq\nmov {name}, rdi"
            )
            .unwrap();
            if bits == 64 || reg >= 8 {
                writeln!(
                    assembly,
                    ".byte {}",
                    0x40 | if bits == 64 { 8 } else { 0 } | (reg >> 3)
                )
                .unwrap();
            }
            writeln!(assembly, ".byte 15, {}\nmov rax, {name}\nmov rsp, {stack}\npushfq\npop rdx\nmov [{pointer}], rdx", 0xc8 | (reg & 7)).unwrap();
            assembly.push_str("pop r15\npop r14\npop r13\npop r12\npop rbp\npop rbx\nret\n");
            writeln!(assembly, ".size {function}, .-{function}").unwrap();
            writeln!(
                source,
                "extern uint64_t {function}(uint64_t, uint64_t, uint64_t *);"
            )
            .unwrap();
            functions.push(function);
        }
    }
    assembly.push_str(".section .note.GNU-stack,\"\",@progbits\n");
    writeln!(
        source,
        "static uint64_t (*const functions[])(uint64_t,uint64_t,uint64_t*) = {{{}}};",
        functions.join(",")
    )
    .unwrap();
    source.push_str(
        r#"
int main(void) {
    unsigned index;
    uint64_t input, seed;
    while (scanf("%u %" SCNu64 " %" SCNu64, &index, &input, &seed) == 3) {
        if (index >= 32) return 2;
        uint64_t flags;
        uint64_t value = functions[index](input, seed, &flags);
        printf("%" PRIu64 " %" PRIu64 "\n", value, flags);
    }
    return 0;
}
"#,
    );
    let asm_path = directory.join("oracle.S");
    let c_path = directory.join("oracle.c");
    std::fs::write(&asm_path, assembly).unwrap();
    std::fs::write(&c_path, source).unwrap();
    let assembly_object = directory.join("oracle-asm.o");
    let compiled = native::compile_output(
        std::process::Command::new("cc")
            .arg("-c")
            .arg(&asm_path)
            .arg("-o")
            .arg(&assembly_object),
    );
    assert!(
        compiled.status.success(),
        "{}",
        String::from_utf8_lossy(&compiled.stderr)
    );
    let object = directory.join("oracle.o");
    let binary = directory.join("oracle");
    native::object(&c_path, &object, "-O2", "unused");
    native::link(&[&object, &assembly_object], &binary);
    binary
}

#[test]
#[cfg(all(target_arch = "x86_64", target_os = "linux"))]
fn every_gp_register_at_both_widths_matches_native_and_poison_flags() {
    let directory = evidence_directory("native");
    let oracle = native_oracle(&directory);
    let mut values = vec![
        0,
        1,
        u64::MAX,
        0x0123_4567_89ab_cdef,
        0x8000_0000_0000_0000,
        0xdead_beef_0000_0001,
        0x0000_0000_ffff_ffff,
    ];
    let mut random = 0x1d8e_4e27_c47d_124fu64;
    for _ in 0..32 {
        random ^= random << 13;
        random ^= random >> 7;
        random ^= random << 17;
        values.push(random);
    }
    let mut input = String::new();
    let mut cases = Vec::new();
    for width in [Width::U32, Width::U64] {
        for reg in 0..16 {
            let program = x86::lift(&code(width, reg), 0, 0).unwrap();
            for value in &values {
                for pattern in 0u64..32 {
                    let mut seed = 0x202 | ((pattern & 1) << 4); // AF is also poisoned.
                    let mut registers: Vec<_> = (0..x86::REGISTER_COUNT)
                        .map(|r| 0x1020_3040_5060_7080u64.wrapping_mul(r as u64 + 1))
                        .collect();
                    for (i, (flag, bit)) in [
                        (x86::CF, 0),
                        (x86::PF, 2),
                        (x86::ZF, 6),
                        (x86::SF, 7),
                        (x86::OF, 11),
                    ]
                    .into_iter()
                    .enumerate()
                    {
                        registers[flag] = (pattern >> i) & 1;
                        seed |= registers[flag] << bit;
                    }
                    registers[reg as usize] = *value;
                    let actual = program.execute(&registers, 2).unwrap();
                    let index = usize::from(width == Width::U64) * 16 + reg as usize;
                    writeln!(input, "{index} {value} {seed}").unwrap();
                    cases.push((width, reg as usize, *value, seed, registers, actual));
                }
            }
        }
    }
    std::fs::write(directory.join("inputs.txt"), &input).unwrap();
    let expected = native::run_fields(&oracle, &input, 2);
    for ((width, reg, value, seed, before, actual), expected) in cases.iter().zip(expected) {
        assert_eq!(
            actual.registers[*reg],
            expected[0].wrapping_add(u64::from(*reg == x86::RSP) * 8),
            "{width:?} reg={reg} value={value:#x}"
        );
        for (flag, bit) in [
            (x86::CF, 0),
            (x86::PF, 2),
            (x86::ZF, 6),
            (x86::SF, 7),
            (x86::OF, 11),
        ] {
            assert_eq!(actual.registers[flag], (expected[1] >> bit) & 1);
            assert_eq!((expected[1] >> bit) & 1, (*seed >> bit) & 1);
        }
        assert_eq!(expected[1] & 0x10, seed & 0x10); // Hardware also preserves AF.
        for (other, initial) in before.iter().enumerate().take(16) {
            if other != *reg {
                assert_eq!(
                    actual.registers[other],
                    initial.wrapping_add(u64::from(other == x86::RSP) * 8)
                );
            }
        }
        assert_eq!(actual.trace.len(), 2);
        assert!(actual.memory.is_empty());
    }
    println!("{} native BSWAP/flag comparisons", cases.len());
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
fn real_o0_and_o2_c_bswap_fixture_matches_native_ir_and_recompiled_c_full_memory() {
    use nirvana::{emit, frontend, readable};
    use std::fmt::Write as _;
    let nonce = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    // Retain the objects, rendered C and executables as reproducible evidence.
    let directory = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("target/bswap-tests")
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
        let original_object = directory.join("byte-swap.o");
        native::object(
            &root.join("recovery/byte-swap.c"),
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
                Operation::ByteSwap { destination } => Some(destination.width),
                _ => None,
            })
            .collect();
        assert!(
            !rotations.is_empty(),
            "{optimization} did not produce any BSWAP instructions"
        );
        assert!(rotations.contains(&Width::U32) && rotations.contains(&Width::U64));
        println!("{optimization} native BSWAP forms: {rotations:?}");
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

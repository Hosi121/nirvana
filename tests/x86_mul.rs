//! Intel SDM Vol.2B MUL, printed pp.4-146/147 (PDF pp.148/149).
//! Unsigned full products are checked independently with Rust u128 and native
//! scalar MUL. Only defined CF/OF are compared; SF/ZF/PF remain unavailable.

use nirvana::ir::{AccessKind, Expr, RunStatus, Width};
use nirvana::x86::{self, LiftError, Operand, Operation};

#[allow(dead_code)]
#[path = "support/native.rs"]
mod native;

const WIDTHS: [Width; 4] = [Width::U8, Width::U16, Width::U32, Width::U64];
const VALUES: [u64; 14] = [
    0,
    1,
    2,
    127,
    128,
    255,
    256,
    65535,
    65536,
    0xffff_ffff,
    0x1_0000_0000,
    1 << 63,
    0xfedc_ba98_7654_3210,
    u64::MAX,
];

fn register_code(width: Width, index: u8, high8: bool) -> Vec<u8> {
    assert!(!high8 || (width == Width::U8 && index < 4));
    let mut code = Vec::new();
    if width == Width::U16 {
        code.push(0x66);
    }
    let rex = 0x40 | if width == Width::U64 { 8 } else { 0 } | (index >> 3);
    if rex != 0x40 || (width == Width::U8 && index >= 4 && !high8) {
        code.push(rex);
    }
    code.extend([
        if width == Width::U8 { 0xf6 } else { 0xf7 },
        0xe0 | if high8 { index + 4 } else { index & 7 },
        0xc3,
    ]);
    code
}

fn memory_code(width: Width, base: u8) -> Vec<u8> {
    let mut code = Vec::new();
    if width == Width::U16 {
        code.push(0x66);
    }
    let rex = 0x40 | if width == Width::U64 { 8 } else { 0 } | (base >> 3);
    if rex != 0x40 {
        code.push(rex);
    }
    code.extend([
        if width == Width::U8 { 0xf6 } else { 0xf7 },
        0x60 | (base & 7),
    ]);
    if base & 7 == 4 {
        code.push(0x24);
    }
    code.extend([0, 0xc3]);
    code
}

#[test]
fn decodes_only_unsigned_mul_with_implicit_width_and_correct_byte_register_bank() {
    for width in WIDTHS {
        for index in 0..16 {
            let bytes = register_code(width, index, false);
            let decoded = x86::decode_at(&bytes, 0).unwrap();
            assert_eq!(decoded.size as usize, bytes.len() - 1);
            let Operation::Mul {
                source: Operand::Register(actual),
            } = decoded.operation
            else {
                panic!()
            };
            assert_eq!(
                (actual.index, actual.width, actual.shift),
                (index, width, 0)
            );
            let bytes = memory_code(width, index);
            let decoded = x86::decode_at(&bytes, 0).unwrap();
            let Operation::Mul {
                source:
                    Operand::Memory {
                        address,
                        width: actual,
                    },
            } = decoded.operation
            else {
                panic!()
            };
            assert_eq!(
                (address.base, address.index, address.displacement, actual),
                (Some(index), None, 0, width)
            );
        }
    }
    for index in 0..4 {
        let decoded = x86::decode_at(&register_code(Width::U8, index, true), 0).unwrap();
        let Operation::Mul {
            source: Operand::Register(actual),
        } = decoded.operation
        else {
            panic!()
        };
        assert_eq!(
            (actual.index, actual.width, actual.shift),
            (index, Width::U8, 8)
        );
    }
    for prefix in [0x40, 0x44, 0x48] {
        let Operation::Mul {
            source: Operand::Register(actual),
        } = x86::decode_at(&[prefix, 0xf6, 0xe4], 0).unwrap().operation
        else {
            panic!()
        };
        assert_eq!(
            (actual.index, actual.width, actual.shift),
            (4, Width::U8, 0),
            "REX changes AH to SPL, including ignored R/W bits"
        );
    }
    let Operation::Mul {
        source: Operand::Register(actual),
    } = x86::decode_at(&[0x45, 0xf7, 0xe0], 0).unwrap().operation
    else {
        panic!()
    };
    assert_eq!(
        (actual.index, actual.width),
        (8, Width::U32),
        "REX.R is not part of /4; REX.B extends the source"
    );
    let Operation::Mul {
        source: Operand::Register(actual),
    } = x86::decode_at(&[0x66, 0x48, 0xf7, 0xe0], 0)
        .unwrap()
        .operation
    else {
        panic!()
    };
    assert_eq!(actual.width, Width::U64);
    let Operation::Mul {
        source: Operand::Memory { address, width },
    } = x86::decode_at(&[0x4b, 0xf7, 0x64, 0xcc, 0xe0], 0)
        .unwrap()
        .operation
    else {
        panic!()
    };
    assert_eq!(
        (
            width,
            address.base,
            address.index,
            address.scale,
            address.displacement
        ),
        (Width::U64, Some(12), Some(9), 8, -32)
    );
    for opcode in [0xf6, 0xf7] {
        for group in [1u8, 5, 6, 7] {
            assert!(x86::decode_at(&[opcode, 0xc0 | (group << 3)], 0).is_err());
        }
        for bytes in [
            vec![0xf0, opcode, 0xe0],
            vec![0xf2, opcode, 0xe0],
            vec![0xf3, opcode, 0xe0],
            vec![opcode],
            vec![opcode, 0x64],
            vec![opcode, 0x65],
            vec![opcode, 0x25],
        ] {
            assert!(x86::decode_at(&bytes, 0).is_err(), "{bytes:02x?}");
        }
    }
}

fn product(width: Width, accumulator: u64, high: u64, source: u64) -> (u64, u64, u64) {
    let wide = u128::from(accumulator & width.mask()) * u128::from(source & width.mask());
    let upper = ((wide >> width.bits()) as u64) & width.mask();
    let low = wide as u64;
    let (accumulator, high) = match width {
        Width::U8 => ((accumulator & !0xffff) | (low & 0xffff), high),
        Width::U16 => (
            (accumulator & !0xffff) | (low & 0xffff),
            (high & !0xffff) | upper,
        ),
        Width::U32 => (low & 0xffff_ffff, upper),
        Width::U64 => (low, upper),
    };
    (accumulator, high, u64::from(upper != 0))
}

fn registers(accumulator: u64, high: u64, source: u64, pattern: u64) -> Vec<u64> {
    let mut registers = (0..x86::REGISTER_COUNT)
        .map(|i| 0x8765_4321_1234_5678u64.wrapping_add(i as u64))
        .collect::<Vec<_>>();
    registers[x86::RAX] = accumulator;
    registers[x86::RDX] = high;
    registers[x86::RCX] = source;
    registers[8] = source;
    for (i, flag) in [x86::CF, x86::OF, x86::ZF, x86::SF, x86::PF]
        .into_iter()
        .enumerate()
    {
        registers[flag] = (pattern >> i) & 1;
    }
    registers
}

fn assert_result(width: Width, input: &[u64], source: u64, actual: &nirvana::ir::Execution) {
    let (ax, dx, overflow) = product(width, input[x86::RAX], input[x86::RDX], source);
    for (i, before) in input.iter().copied().enumerate().take(16) {
        let expected = match i {
            x86::RAX => ax,
            x86::RDX => dx,
            x86::RSP => before.wrapping_add(8),
            _ => before,
        };
        assert_eq!(
            actual.registers[i], expected,
            "{width:?} GPR{i}, source={source:#x}, input={input:02x?}"
        );
    }
    assert_eq!(actual.value, ax);
    assert_eq!(
        (actual.registers[x86::CF], actual.registers[x86::OF]),
        (overflow, overflow)
    );
}

#[test]
fn full_products_and_partial_destination_rules_hold_for_every_register_source() {
    let mut cases = 0;
    for width in WIDTHS {
        let forms = (0..16)
            .map(|i| (i, false))
            .chain((0..4).filter(|_| width == Width::U8).map(|i| (i, true)));
        for (index, high8) in forms {
            let program = x86::lift(&register_code(width, index, high8), 0, 0).unwrap();
            for left in VALUES {
                for right in VALUES {
                    for pattern in [0, 3, 28, 31] {
                        let input = registers(
                            left,
                            right.rotate_left(17) ^ 0x5a5a_1234_ffff_5678,
                            right,
                            pattern,
                        );
                        let source =
                            (input[index as usize] >> if high8 { 8 } else { 0 }) & width.mask();
                        let actual = program.execute(&input, 2).unwrap();
                        assert_result(width, &input, source, &actual);
                        cases += 1;
                    }
                }
            }
        }
    }
    println!("{cases} independent u128/register-source MUL comparisons");
}

#[cfg(target_arch = "x86_64")]
fn native_register(
    width: Width,
    index: u8,
    high8: bool,
    ax: u64,
    dx: u64,
    source: u64,
    seed: u64,
) -> (u64, u64, u64, u64, u64) {
    use std::arch::asm;
    let (mut ax, mut dx, mut cx, mut ext) = (ax, dx, source, source);
    let flags: u64;
    macro_rules! instruction {($op:literal)=>{unsafe{asm!("push {seed}","popfq",$op,"pushfq","pop r11",seed=in(reg)seed,inout("rax")ax,inout("rdx")dx,inout("rcx")cx,inout("r8")ext,lateout("r11")flags);}};}
    match (width, index, high8) {
        (Width::U8, 0, false) => instruction!("mul al"),
        (Width::U8, 0, true) => instruction!("mul ah"),
        (Width::U8, 1, false) => instruction!("mul cl"),
        (Width::U8, 1, true) => instruction!("mul ch"),
        (Width::U8, 2, false) => instruction!("mul dl"),
        (Width::U8, 2, true) => instruction!("mul dh"),
        (Width::U8, 8, false) => instruction!("mul r8b"),
        (Width::U16, 0, false) => instruction!("mul ax"),
        (Width::U16, 1, false) => instruction!("mul cx"),
        (Width::U16, 2, false) => instruction!("mul dx"),
        (Width::U16, 8, false) => instruction!("mul r8w"),
        (Width::U32, 0, false) => instruction!("mul eax"),
        (Width::U32, 1, false) => instruction!("mul ecx"),
        (Width::U32, 2, false) => instruction!("mul edx"),
        (Width::U32, 8, false) => instruction!("mul r8d"),
        (Width::U64, 0, false) => instruction!("mul rax"),
        (Width::U64, 1, false) => instruction!("mul rcx"),
        (Width::U64, 2, false) => instruction!("mul rdx"),
        (Width::U64, 8, false) => instruction!("mul r8"),
        _ => unreachable!(),
    }
    (ax, dx, cx, ext, flags)
}

#[cfg(target_arch = "x86_64")]
fn seed(pattern: u64) -> u64 {
    0x202
        | (pattern & 1)
        | (((pattern >> 1) & 1) << 11)
        | (((pattern ^ 3) & 1) << 6)
        | (((pattern ^ 1) & 1) << 7)
        | (((pattern ^ 2) & 1) << 2)
}

#[test]
#[cfg(target_arch = "x86_64")]
fn native_mul_matches_u128_and_ir_for_flags_accumulator_high_aliases_and_rex_source() {
    let mut cases = 0;
    for width in WIDTHS {
        let forms = [(0, false), (1, false), (2, false), (8, false)]
            .into_iter()
            .chain(
                [(0, true), (1, true), (2, true)]
                    .into_iter()
                    .filter(|_| width == Width::U8),
            );
        for (index, high8) in forms {
            let program = x86::lift(&register_code(width, index, high8), 0, 0).unwrap();
            for left in VALUES {
                for right in VALUES {
                    for pattern in 0..4 {
                        let input = registers(
                            left,
                            right.rotate_left(17) ^ 0x5a5a_1234_ffff_5678,
                            right,
                            pattern,
                        );
                        let source =
                            (input[index as usize] >> if high8 { 8 } else { 0 }) & width.mask();
                        let expected = product(width, input[x86::RAX], input[x86::RDX], source);
                        let (ax, dx, cx, ext, flags) = native_register(
                            width,
                            index,
                            high8,
                            input[x86::RAX],
                            input[x86::RDX],
                            right,
                            seed(pattern),
                        );
                        assert_eq!(
                            (ax, dx, flags & 1),
                            expected,
                            "{width:?} src={index} high8={high8}, {left:#x}*{source:#x}"
                        );
                        assert_eq!((flags >> 11) & 1, expected.2);
                        assert_eq!((cx, ext), (right, right));
                        let actual = program.execute(&input, 2).unwrap();
                        assert_result(width, &input, source, &actual);
                        cases += 1;
                    }
                }
            }
        }
    }
    // The same ModR/M byte denotes SPL with any REX prefix, not AH. Capture
    // the actual valid host RSP instead of changing the host stack pointer.
    for left in VALUES {
        for prefix in [0x40u8, 0x48] {
            use std::arch::asm;
            let (mut ax, mut dx) = (left, 0xaabb_ccdd_eeff_1234);
            let (sp, flags): (u64, u64);
            unsafe {
                if prefix == 0x40 {
                    asm!("mov r10,rsp",".byte 0x40,0xf6,0xe4","pushfq","pop r11",inout("rax")ax,inout("rdx")dx,lateout("r10")sp,lateout("r11")flags);
                } else {
                    asm!("mov r10,rsp",".byte 0x48,0xf6,0xe4","pushfq","pop r11",inout("rax")ax,inout("rdx")dx,lateout("r10")sp,lateout("r11")flags);
                }
            }
            let mut input = registers(left, 0xaabb_ccdd_eeff_1234, 0, 0);
            input[x86::RSP] = sp;
            assert_eq!(
                (ax, dx, flags & 1),
                product(Width::U8, left, input[x86::RDX], sp)
            );
            assert_eq!((flags >> 11) & 1, flags & 1);
            let actual = x86::lift(&[prefix, 0xf6, 0xe4, 0xc3], 0, 0)
                .unwrap()
                .execute(&input, 2)
                .unwrap();
            assert_result(Width::U8, &input, sp & 255, &actual);
            cases += 1;
        }
    }
    println!("{cases} native MUL register/flag/alias comparisons");
}

#[cfg(target_arch = "x86_64")]
fn native_memory(
    width: Width,
    base: u8,
    ax: u64,
    dx: u64,
    address: u64,
    seed: u64,
) -> (u64, u64, u64) {
    use std::arch::asm;
    let (mut ax, mut dx) = (ax, dx);
    let flags: u64;
    macro_rules! instruction {($op:literal)=>{unsafe{asm!("push {seed}","popfq",$op,"pushfq","pop r11",seed=in(reg)seed,inout("rax")ax,inout("rdx")dx,in("rcx")address,in("r8")address,lateout("r11")flags);}};}
    match (width, base) {
        (Width::U8, 0) => instruction!("mul byte ptr [rax]"),
        (Width::U8, 2) => instruction!("mul byte ptr [rdx]"),
        (Width::U8, 1) => instruction!("mul byte ptr [rcx]"),
        (Width::U8, 8) => instruction!("mul byte ptr [r8]"),
        (Width::U16, 0) => instruction!("mul word ptr [rax]"),
        (Width::U16, 2) => instruction!("mul word ptr [rdx]"),
        (Width::U16, 1) => instruction!("mul word ptr [rcx]"),
        (Width::U16, 8) => instruction!("mul word ptr [r8]"),
        (Width::U32, 0) => instruction!("mul dword ptr [rax]"),
        (Width::U32, 2) => instruction!("mul dword ptr [rdx]"),
        (Width::U32, 1) => instruction!("mul dword ptr [rcx]"),
        (Width::U32, 8) => instruction!("mul dword ptr [r8]"),
        (Width::U64, 0) => instruction!("mul qword ptr [rax]"),
        (Width::U64, 2) => instruction!("mul qword ptr [rdx]"),
        (Width::U64, 1) => instruction!("mul qword ptr [rcx]"),
        (Width::U64, 8) => instruction!("mul qword ptr [r8]"),
        _ => unreachable!(),
    }
    (ax, dx, flags)
}

fn loads(expression: &Expr) -> usize {
    match expression {
        Expr::Load { address, .. } => 1 + loads(address),
        Expr::Binary(_, a, b) => loads(a) + loads(b),
        Expr::Select {
            condition,
            taken,
            not_taken,
        } => loads(condition) + loads(taken) + loads(not_taken),
        _ => 0,
    }
}

#[test]
#[cfg(target_arch = "x86_64")]
fn memory_mul_loads_once_and_native_uses_the_old_aliasing_accumulator_or_high_address() {
    let mut cases = 0;
    for width in WIDTHS {
        for base in [0u8, 1, 2, 8] {
            let program = x86::lift(&memory_code(width, base), 0, 0).unwrap();
            assert_eq!(
                program.instructions()[0]
                    .assignments
                    .iter()
                    .map(|a| loads(&a.value))
                    .sum::<usize>(),
                1
            );
            assert!(
                program.instructions()[0]
                    .assignments
                    .iter()
                    .all(|a| matches!(a.destination, nirvana::ir::Place::Register(_)))
            );
            for offset in [0usize, 1, 3, 7] {
                for value in VALUES {
                    for pattern in 0..4 {
                        let mut memory = vec![0xa5; 32];
                        memory[offset..offset + 8].copy_from_slice(&value.to_le_bytes());
                        let pointer = memory.as_ptr() as u64 + offset as u64;
                        let mut input =
                            registers(0x8123_4567_89ab_cdef, 0xfedc_ba98_7654_3210, 0, pattern);
                        input[base as usize] = pointer;
                        let expected = product(width, input[x86::RAX], input[x86::RDX], value);
                        let (ax, dx, flags) = native_memory(
                            width,
                            base,
                            input[x86::RAX],
                            input[x86::RDX],
                            pointer,
                            seed(pattern),
                        );
                        assert_eq!((ax, dx, flags & 1), expected);
                        assert_eq!((flags >> 11) & 1, expected.2);
                        let actual = program
                            .execute_with_memory(&input, memory.as_ptr() as u64, &memory, 2)
                            .unwrap();
                        assert_result(width, &input, value, &actual);
                        assert_eq!(actual.memory, memory);
                        cases += 1;
                    }
                }
            }
        }
    }
    println!("{cases} native valid-memory MUL comparisons, including old-RAX/RDX source addresses");
}

#[test]
fn checked_source_fault_keeps_destinations_flags_and_prior_memory_writes() {
    for width in WIDTHS {
        let mul = memory_code(width, x86::RSI as u8);
        let mut bytes = vec![0xc6, 0x07, 0x5a]; // an earlier committed byte store
        bytes.extend(mul);
        let program = x86::lift(&bytes, 0, 0).unwrap();
        assert_eq!(
            program.instructions()[1]
                .assignments
                .iter()
                .map(|a| loads(&a.value))
                .sum::<usize>(),
            1
        );
        for address in [0x0fff, 0x1020 - width.bytes() as u64 + 1, 0x1020, u64::MAX] {
            let mut input = registers(u64::MAX, 0x9876_5432_10ab_cdef, 0, 31);
            input[x86::RDI] = 0x1000;
            input[x86::RSI] = address;
            let memory = [0x91; 32];
            let report = program.run_with_memory(&input, 0x1000, &memory, 3).unwrap();
            assert_eq!(
                report.status,
                RunStatus::Fault(nirvana::ir::MemoryFault {
                    access: AccessKind::Read,
                    address,
                    width
                })
            );
            assert_eq!(&report.state.registers[..21], &input[..21]);
            let mut expected = memory;
            expected[0] = 0x5a;
            assert_eq!(report.state.memory, expected);
            assert_eq!(report.state.trace, vec![0, 3]);
            assert_eq!(report.state.instruction, Some(3));
        }
        let mut input = registers(u64::MAX, 0, 0, 0);
        input[x86::RDI] = 0x1000;
        input[x86::RSI] = 0x1020 - width.bytes() as u64;
        assert!(matches!(
            program
                .run_with_memory(&input, 0x1000, &[0x91; 32], 3)
                .unwrap()
                .status,
            RunStatus::Returned(_)
        ));
    }
}

#[test]
fn only_cf_of_become_available_and_previously_known_zero_sign_parity_are_invalidated() {
    for width in WIDTHS {
        for condition in 0..16u8 {
            let mut bytes = vec![0x31, 0xd2]; // all modeled flags known before MUL
            let mul = register_code(width, 1, false);
            bytes.extend_from_slice(&mul[..mul.len() - 1]);
            bytes.extend([0x0f, 0x90 + condition, 0xc1, 0xc3]);
            let valid = condition < 4; // overflow/carry and their inversions
            assert_eq!(
                x86::lift(&bytes, 0, 0).is_ok(),
                valid,
                "{width:?}, condition={condition}"
            );
            if !valid {
                assert!(matches!(
                    x86::lift(&bytes, 0, 0),
                    Err(LiftError::UndefinedFlags { .. })
                ));
            }
        }
    }
}

#[test]
fn actual_unsigned_constant_division_o0_o2_lifts_and_matches_native_and_rust() {
    use std::fmt::Write as _;
    let scratch = native::Scratch::new();
    let mut inputs = Vec::new();
    for value in VALUES
        .into_iter()
        .chain([9, 10, 11, 19, 20, 21, u64::MAX - 1, u64::MAX - 9])
    {
        for word in [0, 9, 10, 11, u64::from(u32::MAX)] {
            inputs.push([value, 0xaaaa_aaaa_aaaa_aaaa, 0x5555_5555_5555_5555, word]);
        }
    }
    let mut text = String::new();
    for row in &inputs {
        writeln!(text, "{} {} {} {}", row[0], row[1], row[2], row[3]).unwrap();
    }
    for opt in ["-O0", "-O2"] {
        let object = scratch.0.join(format!("unsigned-div{opt}.o"));
        native::object(
            &native::fixture_root().join("recovery/unsigned-div-constant.c"),
            &object,
            opt,
            "fixture",
        );
        let lifted =
            nirvana::frontend::lift_elf(&std::fs::read(&object).unwrap(), "fixture").unwrap();
        let decoded = x86::decode_reachable(
            &lifted.image.bytes,
            lifted.image.address,
            lifted.image.address,
        )
        .unwrap();
        assert!(
            decoded
                .iter()
                .any(|i| matches!(i.operation, Operation::Mul { .. })),
            "{opt} must exercise MUL"
        );
        let harness = scratch.0.join(format!("harness{opt}.o"));
        native::object(
            &native::fixture_root().join("harness.c"),
            &harness,
            opt,
            "fixture",
        );
        let binary = scratch.0.join(format!("unsigned-div{opt}"));
        native::link(&[&object, &harness], &binary);
        let rows = native::run(&binary, &text);
        assert_eq!(rows.len(), inputs.len());
        for (input, native) in inputs.iter().zip(rows) {
            let q = input[0] / 10;
            let remainder = input[0] % 10;
            let word = u64::from(input[3] as u32);
            let small = word / 10 + word % 10;
            let expected = vec![q ^ (remainder << 8) ^ small, input[0], q, remainder, small];
            assert_eq!(native, expected);
            let mut registers = vec![0; x86::REGISTER_COUNT];
            registers[x86::RDI] = 0x2000;
            registers[x86::RSP] = 0x10000;
            let mut memory = vec![0x91; 65536];
            for (i, value) in input.iter().enumerate() {
                memory[4096 + i * 8..4096 + i * 8 + 8].copy_from_slice(&value.to_le_bytes());
            }
            let execution = lifted
                .program
                .execute_with_memory(&registers, 4096, &memory, 100_000)
                .unwrap();
            let mut ir = vec![execution.value];
            ir.extend((0..4).map(|i| {
                u64::from_le_bytes(
                    execution.memory[4096 + i * 8..4096 + i * 8 + 8]
                        .try_into()
                        .unwrap(),
                )
            }));
            assert_eq!(ir, expected, "{opt}: {input:?}");
        }
        println!(
            "unsigned-div-constant {opt}: {} native/IR/u64 division-oracle cases",
            inputs.len()
        );
    }
}

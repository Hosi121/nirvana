//! Register-only BT: the base is read-only, CF is defined, and ZF preserved.
use nirvana::ir::Width;
use nirvana::x86::{self, LiftError, Operand, Operation};

fn code(width: Width, base: u8, index: u8, immediate: Option<u8>) -> Vec<u8> {
    let mut bytes = Vec::new();
    if width == Width::U16 {
        bytes.push(0x66);
    }
    let rex = 0x40
        | if width == Width::U64 { 8 } else { 0 }
        | (base >> 3)
        | if immediate.is_none() {
            (index >> 3) << 2
        } else {
            0
        };
    if rex != 0x40 {
        bytes.push(rex);
    }
    bytes.extend([
        0x0f,
        if immediate.is_some() { 0xba } else { 0xa3 },
        0xc0 | if immediate.is_some() {
            0x20
        } else {
            (index & 7) << 3
        } | (base & 7),
    ]);
    bytes.extend(immediate);
    bytes.push(0xc3);
    bytes
}

#[test]
fn decodes_register_widths_rex_base_and_index_without_a_write_operand() {
    for width in [Width::U16, Width::U32, Width::U64] {
        for base in 0..16 {
            for index in 0..16 {
                for immediate in [None, Some(255)] {
                    let bytes = code(width, base, index, immediate);
                    let decoded = x86::decode_at(&bytes, 0).unwrap();
                    let Operation::BitTest {
                        base: actual,
                        index: offset,
                    } = decoded.operation
                    else {
                        panic!()
                    };
                    assert_eq!((actual.index, actual.width, actual.shift), (base, width, 0));
                    match offset {
                        Operand::Immediate(value) => assert_eq!(Some(value as u8), immediate),
                        Operand::Register(actual) => assert_eq!(
                            (actual.index, actual.width, actual.shift),
                            (index, width, 0)
                        ),
                        _ => panic!(),
                    }
                    assert_eq!(decoded.size as usize, bytes.len() - 1);
                }
            }
        }
    }
    // REX.R is ignored for the /4 opcode extension, while REX.B selects R8.
    let Operation::BitTest { base, index } = x86::decode_at(&[0x45, 0x0f, 0xba, 0xe0, 255], 0)
        .unwrap()
        .operation
    else {
        panic!()
    };
    assert_eq!(
        (base.index, base.width, index),
        (8, Width::U32, Operand::Immediate(255))
    );
    // REX.W takes precedence over the 16-bit prefix.
    let Operation::BitTest { base, .. } = x86::decode_at(&[0x66, 0x48, 0x0f, 0xba, 0xe0, 63], 0)
        .unwrap()
        .operation
    else {
        panic!()
    };
    assert_eq!(base.width, Width::U64);
}

#[test]
fn explicitly_rejects_memory_and_modifying_bit_operations() {
    for bytes in [
        &[0x0f, 0xa3, 0x08][..],
        &[0x48, 0x0f, 0xa3, 0x08],
        &[0x0f, 0xba, 0x20, 0],
        &[0x66, 0x0f, 0xba, 0x20, 255],
        &[0x0f, 0xab, 0xc8],
        &[0x0f, 0xb3, 0xc8],
        &[0x0f, 0xbb, 0xc8],
        &[0x0f, 0xba, 0xe8, 0],
        &[0x0f, 0xba, 0xf0, 0],
        &[0x0f, 0xba, 0xf8, 0],
        &[0xf0, 0x0f, 0xa3, 0xc8],
        &[0x0f, 0xba, 0xe0],
    ] {
        assert!(x86::decode_at(bytes, 0).is_err(), "{bytes:02x?}");
    }
}

#[cfg(target_arch = "x86_64")]
fn native_register(
    width: Width,
    high: usize,
    alias: bool,
    base: u64,
    index: u64,
    seed: u64,
) -> (u64, u64, u64) {
    use std::arch::asm;
    let mut base = base;
    let mut index = index;
    let flags: u64;
    macro_rules! instruction {
        ($op:literal, $base:tt, $index:tt) => {
            unsafe { asm!("push {seed}", "popfq", $op, "pushfq", "pop rdx", seed=in(reg) seed, inout($base) base, inout($index) index, lateout("rdx") flags); }
        };
    }
    match (width, high, alias) {
        (Width::U16, 0, false) => instruction!("bt ax, cx", "rax", "rcx"),
        (Width::U32, 0, false) => instruction!("bt eax, ecx", "rax", "rcx"),
        (Width::U64, 0, false) => instruction!("bt rax, rcx", "rax", "rcx"),
        (Width::U16, 0, true) => instruction!("bt ax, ax", "rax", "rcx"),
        (Width::U32, 0, true) => instruction!("bt eax, eax", "rax", "rcx"),
        (Width::U64, 0, true) => instruction!("bt rax, rax", "rax", "rcx"),
        (Width::U16, 1, false) => instruction!("bt r8w, r9w", "r8", "r9"),
        (Width::U32, 1, false) => instruction!("bt r8d, r9d", "r8", "r9"),
        (Width::U64, 1, false) => instruction!("bt r8, r9", "r8", "r9"),
        (Width::U16, 1, true) => instruction!("bt r8w, r8w", "r8", "r9"),
        (Width::U32, 1, true) => instruction!("bt r8d, r8d", "r8", "r9"),
        (Width::U64, 1, true) => instruction!("bt r8, r8", "r8", "r9"),
        (Width::U16, 2, false) => instruction!("bt r15w, r14w", "r15", "r14"),
        (Width::U32, 2, false) => instruction!("bt r15d, r14d", "r15", "r14"),
        (Width::U64, 2, false) => instruction!("bt r15, r14", "r15", "r14"),
        (Width::U16, 2, true) => instruction!("bt r15w, r15w", "r15", "r14"),
        (Width::U32, 2, true) => instruction!("bt r15d, r15d", "r15", "r14"),
        (Width::U64, 2, true) => instruction!("bt r15, r15", "r15", "r14"),
        _ => unreachable!(),
    }
    (base, index, flags)
}

#[cfg(target_arch = "x86_64")]
fn native_immediate<const INDEX: u8>(
    width: Width,
    high: usize,
    base: u64,
    seed: u64,
) -> (u64, u64) {
    use std::arch::asm;
    let mut base = base;
    let flags: u64;
    macro_rules! instruction {
        ($op:literal, $base:tt) => {
            unsafe { asm!("push {seed}", "popfq", $op, "pushfq", "pop rdx", seed=in(reg) seed, offset=const INDEX, inout($base) base, lateout("rdx") flags); }
        };
    }
    match (width, high) {
        (Width::U16, 0) => instruction!("bt ax, {offset}", "rax"),
        (Width::U32, 0) => instruction!("bt eax, {offset}", "rax"),
        (Width::U64, 0) => instruction!("bt rax, {offset}", "rax"),
        (Width::U16, 1) => instruction!("bt r8w, {offset}", "r8"),
        (Width::U32, 1) => instruction!("bt r8d, {offset}", "r8"),
        (Width::U64, 1) => instruction!("bt r8, {offset}", "r8"),
        (Width::U16, 2) => instruction!("bt r15w, {offset}", "r15"),
        (Width::U32, 2) => instruction!("bt r15d, {offset}", "r15"),
        (Width::U64, 2) => instruction!("bt r15, {offset}", "r15"),
        _ => unreachable!(),
    }
    (base, flags)
}

#[cfg(target_arch = "x86_64")]
fn immediate(width: Width, high: usize, base: u64, index: u8, seed: u64) -> (u64, u64) {
    match index {
        0 => native_immediate::<0>(width, high, base, seed),
        1 => native_immediate::<1>(width, high, base, seed),
        15 => native_immediate::<15>(width, high, base, seed),
        16 => native_immediate::<16>(width, high, base, seed),
        17 => native_immediate::<17>(width, high, base, seed),
        31 => native_immediate::<31>(width, high, base, seed),
        32 => native_immediate::<32>(width, high, base, seed),
        33 => native_immediate::<33>(width, high, base, seed),
        63 => native_immediate::<63>(width, high, base, seed),
        64 => native_immediate::<64>(width, high, base, seed),
        65 => native_immediate::<65>(width, high, base, seed),
        255 => native_immediate::<255>(width, high, base, seed),
        _ => unreachable!(),
    }
}

#[test]
#[cfg(target_arch = "x86_64")]
fn native_cf_zf_and_read_only_gprs_match_all_widths_masks_and_aliases() {
    let mut comparisons = 0;
    for width in [Width::U16, Width::U32, Width::U64] {
        let offsets = [
            0,
            1,
            u64::from(width.bits()) - 1,
            u64::from(width.bits()),
            u64::from(width.bits()) + 1,
            63,
            64,
            255,
            u64::MAX,
        ];
        for (high, (base, index_reg)) in [(0, 1), (8, 9), (15, 14)].into_iter().enumerate() {
            for offset in offsets {
                for value in [
                    0,
                    1,
                    u64::MAX,
                    0x1234_5678_9abc_def0,
                    0x8000_0000_8000_8000,
                    0xffff_ffff_0000_0001,
                ] {
                    for form in 0..3 {
                        let alias = form == 1;
                        let value = if alias { offset } else { value };
                        let index = if alias { base } else { index_reg };
                        let count = if form == 2 { Some(offset as u8) } else { None };
                        let program = x86::lift(&code(width, base, index, count), 0, 0).unwrap();
                        for pattern in 0u64..32 {
                            let mut seed = 0x202;
                            let mut registers: Vec<_> = (0..x86::REGISTER_COUNT)
                                .map(|r| 0x8765_4321_1234_5678u64.wrapping_add(r as u64))
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
                            registers[index_reg as usize] = offset;
                            registers[base as usize] = value;
                            let actual = program.execute(&registers, 2).unwrap();
                            let (native_base, native_flags) = if form == 2 {
                                immediate(width, high, value, offset as u8, seed)
                            } else {
                                let (base, index, flags) =
                                    native_register(width, high, alias, value, offset, seed);
                                assert_eq!(index, offset);
                                (base, flags)
                            };
                            assert_eq!(native_base, value);
                            assert_eq!(
                                actual.registers[x86::CF],
                                native_flags & 1,
                                "{width:?} base={base} offset={offset} value={value:#x}"
                            );
                            assert_eq!(actual.registers[x86::ZF], (native_flags >> 6) & 1);
                            assert_eq!((native_flags >> 6) & 1, registers[x86::ZF]);
                            for (r, before) in registers.iter().enumerate().take(16) {
                                assert_eq!(
                                    actual.registers[r],
                                    before.wrapping_add(u64::from(r == x86::RSP) * 8),
                                    "BT wrote GPR{r} at {width:?}"
                                );
                            }
                            comparisons += 1;
                        }
                    }
                }
            }
        }
    }
    println!("{comparisons} native register/immediate BT comparisons");
}

#[test]
fn cf_is_always_available_zf_preserves_availability_and_undefined_branches_reject() {
    for width in [Width::U16, Width::U32, Width::U64] {
        for immediate in [None, Some(0), Some(255)] {
            for seeded in [false, true] {
                for condition in 0..16 {
                    let mut bytes = if seeded { vec![0x39, 0xd2] } else { Vec::new() };
                    let mut operation = code(width, 0, 1, immediate);
                    operation.pop();
                    bytes.extend(operation);
                    bytes.extend([0x70 | condition, 0, 0xc3]);
                    let uses_undefined = matches!(condition, 0..=1 | 8..=15);
                    let needs_zf = matches!(condition, 4..=7);
                    let expected = !uses_undefined && (seeded || !needs_zf);
                    assert_eq!(
                        x86::lift(&bytes, 0, 0).is_ok(),
                        expected,
                        "{width:?} immediate={immediate:?} seeded={seeded} condition={condition}"
                    );
                }
            }
        }
    }
    // No stale pre-BT OF may flow through a join into a signed branch.
    let bytes = [0x39, 0xd2, 0x74, 4, 0x0f, 0xba, 0xe0, 0, 0x70, 0, 0xc3];
    assert!(matches!(
        x86::lift(&bytes, 0, 0),
        Err(LiftError::UndefinedFlags { .. })
    ));
}

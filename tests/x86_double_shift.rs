use nirvana::ir::{AccessKind, RunStatus, Width};
use nirvana::x86::{self, LiftError};

fn code(width: Width, left: bool, count: u8, memory: bool) -> Vec<u8> {
    let mut code = Vec::new();
    if width == Width::U16 {
        code.push(0x66);
    } else if width == Width::U64 {
        code.push(0x48);
    }
    code.extend([
        0x0f,
        if left { 0xa4 } else { 0xac },
        if memory { 0x17 } else { 0xd0 },
        count,
        0xc3,
    ]);
    code
}

#[cfg(target_arch = "x86_64")]
fn native<const N: u8>(
    width: Width,
    left: bool,
    mut value: u64,
    source: u64,
    seed: u64,
) -> (u64, u64) {
    use std::arch::asm;
    let flags: u64;
    macro_rules! shift {($op:literal)=>{unsafe {
        asm!("push {seed}","popfq",$op,"pushfq","pop rsi",
            seed=in(reg)seed,count=const N,inout("rax")value,in("rdx")source,lateout("rsi")flags);
    }};}
    match (width, left) {
        (Width::U16, true) => shift!("shld ax, dx, {count}"),
        (Width::U16, false) => shift!("shrd ax, dx, {count}"),
        (Width::U32, true) => shift!("shld eax, edx, {count}"),
        (Width::U32, false) => shift!("shrd eax, edx, {count}"),
        (_, true) => shift!("shld rax, rdx, {count}"),
        (_, false) => shift!("shrd rax, rdx, {count}"),
    }
    (value, flags)
}

#[test]
#[cfg(target_arch = "x86_64")]
fn values_and_defined_flags_match_native_at_mask_and_width_boundaries() {
    let mut comparisons = 0;
    for width in [Width::U16, Width::U32, Width::U64] {
        for left in [false, true] {
            for count in [0, 1, 15, 16, 17, 31, 32, 63, 64, 127, 255] {
                let n = count & if width == Width::U64 { 63 } else { 31 };
                if u32::from(n) > width.bits() {
                    assert!(x86::lift(&code(width, left, count, false), 0, 0).is_err());
                    continue;
                }
                let program = x86::lift(&code(width, left, count, false), 0, 0).unwrap();
                for a in [
                    0,
                    1,
                    u64::MAX,
                    0x8000_0000,
                    0x8000_0000_0000_0000,
                    0x1234_5678_9abc_def0,
                ] {
                    for b in [0, 1, u64::MAX, 0x5555_aaaa_5555_aaaa] {
                        for seed in [0x202, 0xad7] {
                            let (value, flags) = match count {
                                0 => native::<0>(width, left, a, b, seed),
                                1 => native::<1>(width, left, a, b, seed),
                                15 => native::<15>(width, left, a, b, seed),
                                16 => native::<16>(width, left, a, b, seed),
                                17 => native::<17>(width, left, a, b, seed),
                                31 => native::<31>(width, left, a, b, seed),
                                32 => native::<32>(width, left, a, b, seed),
                                63 => native::<63>(width, left, a, b, seed),
                                64 => native::<64>(width, left, a, b, seed),
                                127 => native::<127>(width, left, a, b, seed),
                                _ => native::<255>(width, left, a, b, seed),
                            };
                            let mut input = vec![0; x86::REGISTER_COUNT];
                            input[x86::RAX] = a;
                            input[x86::RDX] = b;
                            for (reg, bit) in [
                                (x86::CF, 0),
                                (x86::PF, 2),
                                (x86::ZF, 6),
                                (x86::SF, 7),
                                (x86::OF, 11),
                            ] {
                                input[reg] = (seed >> bit) & 1;
                            }
                            let result = program.execute(&input, 2).unwrap();
                            assert_eq!(
                                result.value, value,
                                "{width:?} left={left} count={count} a={a:#x} b={b:#x}"
                            );
                            assert_eq!(result.registers[x86::RDX], b);
                            for (reg, bit) in [
                                (x86::CF, 0),
                                (x86::PF, 2),
                                (x86::ZF, 6),
                                (x86::SF, 7),
                                (x86::OF, 11),
                            ] {
                                if reg != x86::OF || n <= 1 {
                                    assert_eq!(
                                        result.registers[reg],
                                        (flags >> bit) & 1,
                                        "{width:?} left={left} count={count} flag={reg}"
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
    println!("double shifts: {comparisons} native value/defined-flag comparisons");
}

#[test]
fn undefined_overflow_is_rejected_and_one_bit_overflow_is_available() {
    for count in [0, 1, 2, 63] {
        let mut bytes = code(Width::U64, true, count, false);
        bytes.pop();
        bytes.extend([0x0f, 0x90, 0xc0, 0xc3]);
        if count == 1 {
            assert!(x86::lift(&bytes, 0, 0).is_ok());
        } else {
            assert!(matches!(
                x86::lift(&bytes, 0, 0),
                Err(LiftError::UndefinedFlags { .. })
            ));
        }
    }
    for opcode in [0xa5, 0xad] {
        assert!(x86::decode_at(&[0x48, 0x0f, opcode, 0xd0], 0).is_err());
    }
}

#[test]
fn memory_destination_snapshots_the_address_and_checks_the_first_read() {
    let program = x86::lift(&code(Width::U64, true, 3, true), 0, 0).unwrap();
    let mut memory = vec![0; 16];
    memory[..8].copy_from_slice(&0x1234u64.to_le_bytes());
    for address in [4096, 4105, u64::MAX] {
        let mut input = vec![0; x86::REGISTER_COUNT];
        input[x86::RDI] = address;
        input[x86::RDX] = u64::MAX;
        let result = program.run_with_memory(&input, 4096, &memory, 4).unwrap();
        if address == 4096 {
            assert_eq!(
                u64::from_le_bytes(result.state.memory[..8].try_into().unwrap()),
                (0x1234u64 << 3) | 7
            );
        } else {
            let RunStatus::Fault(f) = result.status else {
                panic!("{result:?}")
            };
            assert_eq!(
                (f.address, f.access, f.width),
                (address, AccessKind::Read, Width::U64)
            );
            assert_eq!(result.state.memory, memory);
        }
    }
}

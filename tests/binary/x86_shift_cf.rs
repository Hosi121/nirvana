//! Variable shifts preserve CF availability when every masked nonzero count is
//! below the operand width. Compare only native-defined data and carry uses;
//! complete register comparisons below concern IR versus its generated C.
use nirvana::ir::Width;
use nirvana::x86::{self, LiftError, Shift};

#[derive(Clone, Copy, Debug)]
enum Seed {
    Clear,
    Set,
    Mul,
}

#[derive(Clone, Copy, Debug)]
enum Consumer {
    Setb,
    Adc,
}

#[derive(Clone, Copy, Debug)]
struct Profile {
    width: Width,
    shift: Shift,
    seed: Seed,
    consumer: Consumer,
}

fn shift(width: Width, kind: Shift) -> Vec<u8> {
    let mut code = match width {
        Width::U16 => vec![0x66],
        Width::U64 => vec![0x48],
        _ => Vec::new(),
    };
    code.push(if width == Width::U8 { 0xd2 } else { 0xd3 });
    code.push(match kind {
        Shift::Left => 0xe7,
        Shift::Right => 0xef,
        Shift::ArithmeticRight => 0xff,
    }); // destination RDI/EDI/DI/BH; the negative byte cases use BH.
    code
}

fn consume(consumer: Consumer) -> &'static [u8] {
    match consumer {
        Consumer::Setb => &[0x0f, 0x92, 0xc2, 0x0f, 0xb6, 0xc2], // SETB DL; MOVZX EAX,DL
        Consumer::Adc => &[0xb8, 0, 0, 0, 0, 0x48, 0x83, 0xd0, 0], // MOV EAX,0; ADC RAX,0
    }
}

impl Profile {
    fn code(self) -> Vec<u8> {
        let mut code = match self.seed {
            Seed::Clear => vec![0x31, 0xc0],              // XOR EAX,EAX
            Seed::Set => vec![0x31, 0xc0, 0x83, 0xf8, 1], // CMP EAX,1
            Seed::Mul => vec![0x48, 0xf7, 0xe6],          // MUL RSI
        };
        code.extend(shift(self.width, self.shift));
        code.extend(consume(self.consumer));
        code.push(0xc3);
        code
    }
}

fn unavailable(code: &[u8]) {
    assert!(matches!(
        x86::lift(code, 0, 0),
        Err(LiftError::UndefinedFlags { .. })
    ));
}

#[test]
fn zero_counts_do_not_define_unknown_carry_and_undefined_flags_stay_unavailable() {
    for width in [Width::U32, Width::U64] {
        for kind in [Shift::Left, Shift::Right, Shift::ArithmeticRight] {
            for consumer in [Consumer::Setb, Consumer::Adc] {
                let mut code = shift(width, kind);
                code.extend(consume(consumer));
                code.push(0xc3);
                unavailable(&code);
            }
            let mut code = vec![0x31, 0xc0];
            code.extend(shift(width, kind));
            code.extend([0x0f, 0x90, 0xc0, 0xc3]); // SETO AL
            unavailable(&code);
        }
    }
    for width in [Width::U8, Width::U16] {
        for kind in [Shift::Left, Shift::Right] {
            let mut code = vec![0x31, 0xc0];
            code.extend(shift(width, kind));
            code.extend(consume(Consumer::Setb));
            code.push(0xc3);
            unavailable(&code);
        }
    }
    // Undefined MUL ZF cannot become available through a possibly zero shift.
    let mut code = vec![0x48, 0xf7, 0xe6];
    code.extend(shift(Width::U64, Shift::Left));
    code.extend([0x0f, 0x94, 0xc0, 0xc3]); // SETZ AL
    unavailable(&code);
}

#[test]
fn div_undefined_carry_and_join_inputs_remain_unavailable() {
    use crate::support::native;
    use nirvana::{linked_elf::LinkedOptions, module_ir};
    use std::fmt::Write as _;
    use std::process::Command;

    // DIV uses the module model. Compile all validation controls into one
    // linked image; none of these potentially trapping bodies is executed.
    let mut assembly = String::from(".text\n");
    let mut cases = Vec::new();
    for width in [Width::U32, Width::U64] {
        for kind in [Shift::Left, Shift::Right, Shift::ArithmeticRight] {
            for join in [false, true] {
                for valid in [false, true] {
                    let mut code = if join {
                        // CMP EDI,0; JZ join; MUL RSI (valid) or DIV RSI.
                        // Only the fallthrough predecessor loses CF in the
                        // negative case; the other predecessor preserves it.
                        vec![
                            0x83,
                            0xff,
                            0,
                            0x74,
                            3,
                            0x48,
                            0xf7,
                            if valid { 0xe6 } else { 0xf6 },
                        ]
                    } else {
                        // MOV EAX,1; XOR EDX,EDX; DIV RSI.
                        vec![0xb8, 1, 0, 0, 0, 0x31, 0xd2, 0x48, 0xf7, 0xf6]
                    };
                    let mut operation = shift(width, kind);
                    if !join && valid {
                        // A definite one-bit shift establishes CF after DIV;
                        // a CL shift must retain the unavailable input case.
                        operation[usize::from(width == Width::U64)] = 0xd1;
                    }
                    code.extend(operation);
                    code.extend(consume(Consumer::Setb));
                    code.push(0xc3);
                    let name = format!("control_{}", cases.len());
                    writeln!(assembly, ".globl {name}\n.type {name},@function\n{name}:").unwrap();
                    for byte in code {
                        writeln!(assembly, ".byte {byte}").unwrap();
                    }
                    writeln!(assembly, ".size {name},.-{name}").unwrap();
                    cases.push((name, valid));
                }
            }
        }
    }
    assembly.push_str(".section .note.GNU-stack,\"\",@progbits\n");
    let scratch = native::Scratch::new();
    let source = scratch.0.join("availability.S");
    let binary = scratch.0.join("availability");
    std::fs::write(&source, assembly).unwrap();
    native::compile(
        Command::new("cc")
            .args(["-nostdlib", "-no-pie", "-Wl,-e,control_0"])
            .arg(&source)
            .arg("-o")
            .arg(&binary),
    );
    let bytes = std::fs::read(binary).unwrap();
    for (name, valid) in cases {
        let result = module_ir::lift_elf(
            &bytes,
            &name,
            LinkedOptions {
                load_bias: 0,
                stack_size: 4096,
            },
        );
        assert_eq!(result.is_ok(), valid, "{name}: {result:?}");
        if !valid {
            assert!(result.unwrap_err().to_string().contains("flag"), "{name}");
        }
    }
}

#[cfg(target_arch = "x86_64")]
fn native(profile: Profile, mut value: u64, count: u64, accumulator: u64) -> (u64, u64) {
    use std::arch::asm;
    let result: u64;
    macro_rules! instruction {
        ($op:literal, $($seed:literal),+) => {{
            match profile.consumer {
                Consumer::Setb => unsafe {
                    asm!($($seed,)+ $op, "setb dl", "movzx eax,dl",
                        inout("rdi") value, in("rcx") count,
                        inout("rax") accumulator => result, in("rsi") 2u64,
                        lateout("rdx") _, options(nostack));
                },
                Consumer::Adc => unsafe {
                    asm!($($seed,)+ $op, "mov eax,0", "adc rax,0",
                        inout("rdi") value, in("rcx") count,
                        inout("rax") accumulator => result, in("rsi") 2u64,
                        lateout("rdx") _, options(nostack));
                },
            }
        }};
    }
    macro_rules! seeded {
        ($op:literal) => {
            match profile.seed {
                Seed::Clear => instruction!($op, "xor eax,eax"),
                Seed::Set => instruction!($op, "xor eax,eax", "cmp eax,1"),
                Seed::Mul => instruction!($op, "mul rsi"),
            }
        };
    }
    match (profile.width, profile.shift) {
        (Width::U32, Shift::Left) => seeded!("shl edi,cl"),
        (Width::U32, Shift::Right) => seeded!("shr edi,cl"),
        (Width::U32, Shift::ArithmeticRight) => seeded!("sar edi,cl"),
        (Width::U64, Shift::Left) => seeded!("shl rdi,cl"),
        (Width::U64, Shift::Right) => seeded!("shr rdi,cl"),
        (Width::U64, Shift::ArithmeticRight) => seeded!("sar rdi,cl"),
        _ => unreachable!(),
    }
    (value, result)
}

#[cfg(target_arch = "x86_64")]
fn append_c(code: &mut String, body: &str, prefix: &str) {
    use std::collections::BTreeSet;
    use std::fmt::Write as _;
    // Preprocessor namespacing preserves generated C tokens and lets every
    // profile share one compile/run, including their private scalar helpers.
    let names: BTreeSet<_> = body
        .split(|c: char| !c.is_ascii_alphanumeric() && c != '_')
        .filter(|name| name.starts_with("nirvana_"))
        .collect();
    for name in &names {
        writeln!(code, "#define {name} {prefix}_{name}").unwrap();
    }
    code.push_str(body);
    for name in &names {
        writeln!(code, "#undef {name}").unwrap();
    }
}

#[test]
#[cfg(target_arch = "x86_64")]
fn native_ir_and_generated_c_preserve_seeded_carry_for_every_cl() {
    use crate::support::native;
    use nirvana::{emit, readable};
    use std::fmt::Write as _;
    use std::process::Command;
    use std::time::Duration;

    let scratch = native::Scratch::new();
    let mut c = String::from("#include <stdint.h>\n#include <stdio.h>\n#include <string.h>\n");
    let mut dispatch = String::new();
    let mut input = Vec::new();
    let mut expected = Vec::new();
    let mut profiles = 0;
    let mut cases = 0;
    for width in [Width::U32, Width::U64] {
        for kind in [Shift::Left, Shift::Right, Shift::ArithmeticRight] {
            for seed in [Seed::Clear, Seed::Set, Seed::Mul] {
                for consumer in [Consumer::Setb, Consumer::Adc] {
                    let profile = Profile {
                        width,
                        shift: kind,
                        seed,
                        consumer,
                    };
                    let program = x86::lift(&profile.code(), 0, 0).unwrap();
                    let raw = emit::emit_c(&program).unwrap();
                    let high = readable::emit_readable_c(&program).unwrap();
                    assert!(!high.uses_memory);
                    append_c(&mut c, &raw.code, &format!("p{profiles}_raw"));
                    append_c(&mut c, &high.code, &format!("p{profiles}_high"));
                    let args = high
                        .parameters
                        .iter()
                        .map(|r| format!("row[{}]", r.0 + 1))
                        .collect::<Vec<_>>()
                        .join(",");
                    writeln!(dispatch, "case {profiles}: out[0]=p{profiles}_raw_nirvana_fn(r); out[1]=p{profiles}_high_nirvana_readable({args}); break;").unwrap();
                    let counts = (0..=255u64)
                        .chain([0, 1, 31, 32, 63, 64, 255].map(|n| 0x1234_5678_9abc_de00 | n));
                    for count in counts {
                        for value in [
                            0,
                            1,
                            width.mask(),
                            1 << (width.bits() - 1),
                            (1 << (width.bits() - 1)) - 1,
                            0x9371_cafe_7890_fedc,
                        ] {
                            let accumulators: &[u64] = if matches!(seed, Seed::Mul) {
                                &[1, u64::MAX]
                            } else {
                                &[0x8765_4321_abcd_ef01]
                            };
                            for &accumulator in accumulators {
                                let seeded = match seed {
                                    Seed::Clear => 0,
                                    Seed::Set => 1,
                                    Seed::Mul => u64::from(accumulator > u64::MAX / 2),
                                };
                                let mut registers =
                                    vec![0x9876_5432_1234_5678; x86::REGISTER_COUNT];
                                for flag in [x86::CF, x86::ZF, x86::SF, x86::OF, x86::PF] {
                                    registers[flag] = 1;
                                }
                                registers[x86::CF] = seeded ^ 1;
                                registers[x86::RDI] = value;
                                registers[x86::RCX] = count;
                                registers[x86::RAX] = accumulator;
                                registers[x86::RSI] = 2;
                                let actual = program.execute(&registers, 16).unwrap();
                                let (native_value, native_carry) =
                                    native(profile, value, count, accumulator);
                                let masked = count & u64::from(width.bits() - 1);
                                let carry = if masked == 0 {
                                    seeded
                                } else {
                                    ((value & width.mask())
                                        >> match kind {
                                            Shift::Left => u64::from(width.bits()) - masked,
                                            _ => masked - 1,
                                        })
                                        & 1
                                };
                                assert_eq!(
                                    native_carry, carry,
                                    "{profile:?} count={count:#x} value={value:#x}"
                                );
                                assert_eq!(
                                    (actual.registers[x86::RDI], actual.value),
                                    (native_value, native_carry),
                                    "{profile:?} count={count:#x} value={value:#x}"
                                );
                                for word in std::iter::once(profiles as u64)
                                    .chain(registers.iter().copied())
                                {
                                    input.extend_from_slice(&word.to_ne_bytes());
                                }
                                for word in [actual.value, actual.value]
                                    .into_iter()
                                    .chain(actual.registers)
                                {
                                    expected.extend_from_slice(&word.to_ne_bytes());
                                }
                                cases += 1;
                            }
                        }
                    }
                    profiles += 1;
                }
            }
        }
    }
    writeln!(c, "int main(void) {{ uint64_t row[33],r[32],out[34]; while(fread(row,sizeof(row),1,stdin)==1) {{ memcpy(r,row+1,sizeof(r)); switch(row[0]) {{ {dispatch} default:return 2; }} memcpy(out+2,r,sizeof(r)); if(fwrite(out,sizeof(out),1,stdout)!=1)return 3; }} return ferror(stdin)?4:0; }}").unwrap();
    let source = scratch.0.join("shifts.c");
    std::fs::write(&source, c).unwrap();
    for optimization in ["-O0", "-O2"] {
        let binary = scratch.0.join(format!("shifts{optimization}"));
        native::compile(
            Command::new("cc")
                .args([
                    "-std=c11",
                    "-Wall",
                    "-Wextra",
                    "-Werror",
                    optimization,
                    "-fsanitize=undefined",
                    "-fno-sanitize-recover=undefined",
                ])
                .arg(&source)
                .arg("-o")
                .arg(&binary),
        );
        let output = native::run_output_bytes(&binary, Some(&input), Duration::from_secs(15));
        assert!(
            output.status.success(),
            "{optimization}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(output.stdout.len(), expected.len(), "{optimization}");
        assert!(
            output.stdout == expected,
            "{optimization}: raw full-register/readable return mismatch"
        );
    }
    println!(
        "{profiles} shift/seed/consumer profiles, {cases} native/IR cases and {} raw/readable C comparisons",
        cases * 4
    );
}

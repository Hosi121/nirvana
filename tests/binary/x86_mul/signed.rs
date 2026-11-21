//! Intel SDM Vol.2A IMUL, printed pp.3-501..504 (PDF pp.611..614).
//! <https://cdrdv2-public.intel.com/789581/325383-sdm-vol-2abcd.pdf#page=611>
//! Full signed products, partial writes and defined CF/OF.
use super::*;

fn code(mut bytes: Vec<u8>) -> Vec<u8> {
    let opcode = bytes.iter().position(|&b| b == 0xf6 || b == 0xf7).unwrap();
    bytes[opcode + 1] |= 8; // ModR/M /4 MUL -> /5 IMUL, independent of REX.R.
    bytes
}
fn points(width: Width) -> Vec<u64> {
    let sign = 1u64 << (width.bits() - 1);
    let mut values = VALUES.to_vec();
    values.extend([sign - 1, sign, sign + 1, width.mask() - 1, width.mask()]);
    values.sort_unstable();
    values.dedup();
    values
}
fn signed_product(width: Width, ax: u64, dx: u64, source: u64) -> (u64, u64, u64) {
    let shift = 64 - width.bits();
    let sign = |value: u64| ((value << shift) as i64 >> shift) as i128;
    let product = sign(ax) * sign(source);
    let half = 1i128 << (width.bits() - 1);
    product_state(
        width,
        ax,
        dx,
        product as u128,
        !(-half..half).contains(&product),
    )
}

#[test]
fn signed_forms_decode_every_width_register_bank_and_memory_source() {
    for width in WIDTHS {
        for index in 0..16 {
            let Operation::SignedMul {
                source: Operand::Register(reg),
            } = x86::decode_at(&code(register_code(width, index, false)), 0)
                .unwrap()
                .operation
            else {
                panic!()
            };
            assert_eq!((reg.index, reg.width, reg.shift), (index, width, 0));
            let Operation::SignedMul {
                source:
                    Operand::Memory {
                        address,
                        width: actual,
                    },
            } = x86::decode_at(&code(memory_code(width, index)), 0)
                .unwrap()
                .operation
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
        let Operation::SignedMul {
            source: Operand::Register(reg),
        } = x86::decode_at(&code(register_code(Width::U8, index, true)), 0)
            .unwrap()
            .operation
        else {
            panic!()
        };
        assert_eq!((reg.index, reg.width, reg.shift), (index, Width::U8, 8));
    }
    for prefix in [0x40, 0x44, 0x48] {
        let Operation::SignedMul {
            source: Operand::Register(reg),
        } = x86::decode_at(&[prefix, 0xf6, 0xec], 0).unwrap().operation
        else {
            panic!()
        };
        assert_eq!((reg.index, reg.width, reg.shift), (4, Width::U8, 0));
    }
}

#[test]
#[cfg(target_arch = "x86_64")]
fn signed_full_products_match_i128_and_native_register_aliases_and_flags() {
    let mut ir_cases = 0;
    for width in WIDTHS {
        let forms = (0..16)
            .map(|i| (i, false))
            .chain((0..4).filter(|_| width == Width::U8).map(|i| (i, true)));
        for (index, high8) in forms {
            let program = x86::lift(&code(register_code(width, index, high8)), 0, 0).unwrap();
            for left in points(width) {
                for right in points(width) {
                    for pattern in [0, 31] {
                        let mut input = registers(left, right, right, pattern);
                        if high8 {
                            input[index as usize] =
                                (input[index as usize] & !0xff00) | ((right & 255) << 8);
                        } else if index != 0 {
                            input[index as usize] = right;
                        }
                        let source =
                            (input[index as usize] >> if high8 { 8 } else { 0 }) & width.mask();
                        let expected =
                            signed_product(width, input[x86::RAX], input[x86::RDX], source);
                        assert_product_result(
                            width,
                            &input,
                            source,
                            &program.execute(&input, 2).unwrap(),
                            expected,
                        );
                        ir_cases += 1;
                    }
                }
            }
        }
    }
    println!("{ir_cases} i128/IR signed products covering every register source");
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
            let program = x86::lift(&code(register_code(width, index, high8)), 0, 0).unwrap();
            for left in points(width) {
                for right in points(width) {
                    for pattern in 0..4 {
                        let encoded_source = if high8 { (right & 255) << 8 } else { right };
                        let ax = if high8 && index == 0 {
                            (left & !0xff00) | encoded_source
                        } else {
                            left
                        };
                        let dx = if high8 && index == 2 {
                            encoded_source
                        } else {
                            right
                        };
                        let input = registers(ax, dx, encoded_source, pattern);
                        let source =
                            (input[index as usize] >> if high8 { 8 } else { 0 }) & width.mask();
                        let expected =
                            signed_product(width, input[x86::RAX], input[x86::RDX], source);
                        let (ax, dx, cx, ext, flags) = native_register(
                            width,
                            (index, high8),
                            ax,
                            dx,
                            encoded_source,
                            seed(pattern),
                            true,
                        );
                        assert_eq!(
                            (ax, dx, flags & 1),
                            expected,
                            "{width:?}, {left:#x} * {source:#x}"
                        );
                        assert_eq!((flags >> 11) & 1, expected.2);
                        assert_eq!((cx, ext), (encoded_source, encoded_source));
                        let actual = program.execute(&input, 2).unwrap();
                        assert_product_result(width, &input, source, &actual, expected);
                        cases += 1;
                    }
                }
            }
        }
    }
    // REX selects SPL rather than AH, including an otherwise ignored W bit.
    for left in points(Width::U8) {
        for prefix in [0x40u8, 0x48] {
            use std::arch::asm;
            let (mut ax, mut dx) = (left, 0xaabb_ccdd_eeff_1234);
            let (sp, flags): (u64, u64);
            unsafe {
                if prefix == 0x40 {
                    asm!("mov r10,rsp",".byte 0x40,0xf6,0xec","pushfq","pop r11",inout("rax")ax,inout("rdx")dx,lateout("r10")sp,lateout("r11")flags);
                } else {
                    asm!("mov r10,rsp",".byte 0x48,0xf6,0xec","pushfq","pop r11",inout("rax")ax,inout("rdx")dx,lateout("r10")sp,lateout("r11")flags);
                }
            }
            let mut input = registers(left, 0xaabb_ccdd_eeff_1234, 0, 0);
            input[x86::RSP] = sp;
            let expected = signed_product(Width::U8, left, input[x86::RDX], sp);
            assert_eq!((ax, dx, flags & 1), expected);
            assert_eq!((flags >> 11) & 1, expected.2);
            let program = x86::lift(&[prefix, 0xf6, 0xec, 0xc3], 0, 0).unwrap();
            assert_product_result(
                Width::U8,
                &input,
                sp & 255,
                &program.execute(&input, 2).unwrap(),
                expected,
            );
        }
    }
    println!("{cases} native/i128/IR signed full-product register cases");
}

#[test]
#[cfg(target_arch = "x86_64")]
fn signed_memory_source_loads_once_before_changing_its_address_registers() {
    for width in WIDTHS {
        for base in [0u8, 1, 2, 8] {
            let program = x86::lift(&code(memory_code(width, base)), 0, 0).unwrap();
            assert_eq!(
                program.instructions()[0]
                    .assignments
                    .iter()
                    .map(|a| loads(&a.value))
                    .sum::<usize>(),
                1
            );
            for value in points(width) {
                for pattern in [0, 31] {
                    let mut memory = [0x91; 32];
                    memory[1..9].copy_from_slice(&value.to_le_bytes());
                    let address = memory.as_ptr() as u64 + 1;
                    let mut input =
                        registers(0x8123_4567_89ab_cdef, 0xfedc_ba98_7654_3210, 0, pattern);
                    input[base as usize] = address;
                    let expected = signed_product(width, input[x86::RAX], input[x86::RDX], value);
                    let (ax, dx, flags) = native_memory(
                        width,
                        base,
                        input[x86::RAX],
                        input[x86::RDX],
                        address,
                        seed(pattern),
                        true,
                    );
                    assert_eq!((ax, dx, flags & 1), expected);
                    assert_eq!((flags >> 11) & 1, expected.2);
                    let actual = program
                        .execute_with_memory(&input, memory.as_ptr() as u64, &memory, 2)
                        .unwrap();
                    assert_product_result(width, &input, value, &actual, expected);
                    assert_eq!(actual.memory, memory);
                }
            }
        }
    }
}

#[test]
fn signed_source_fault_keeps_destinations_flags_and_an_earlier_store() {
    for width in WIDTHS {
        let mut bytes = vec![0xc6, 0x07, 0x5a];
        bytes.extend(code(memory_code(width, x86::RSI as u8)));
        let program = x86::lift(&bytes, 0, 0).unwrap();
        for address in [0x0fff, 0x1020 - width.bytes() as u64 + 1, 0x1020, u64::MAX] {
            let mut input = registers(u64::MAX, 0x8123_4567_89ab_cdef, 0, 31);
            input[x86::RDI] = 0x1000;
            input[x86::RSI] = address;
            let report = program
                .run_with_memory(&input, 0x1000, &[0x91; 32], 3)
                .unwrap();
            assert_eq!(
                report.status,
                RunStatus::Fault(nirvana::ir::MemoryFault {
                    access: AccessKind::Read,
                    address,
                    width
                })
            );
            assert_eq!(&report.state.registers[..21], &input[..21]);
            let mut expected = [0x91; 32];
            expected[0] = 0x5a;
            assert_eq!(report.state.memory, expected);
            assert_eq!(report.state.trace, vec![0, 3]);
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
fn signed_multiply_invalidates_zero_sign_parity_and_defines_only_carry_overflow() {
    for width in WIDTHS {
        for condition in 0..16u8 {
            let mut bytes = vec![0x31, 0xd2];
            let op = code(register_code(width, 1, false));
            bytes.extend_from_slice(&op[..op.len() - 1]);
            bytes.extend([0x0f, 0x90 + condition, 0xc1, 0xc3]);
            assert_eq!(
                x86::lift(&bytes, 0, 0).is_ok(),
                condition < 4,
                "{width:?}, condition={condition}"
            );
        }
    }
}

#[test]
fn gcc_signed_constant_division_matches_native_ir_and_sanitized_c_at_o0_o2() {
    use std::fmt::Write as _;
    let scratch = native::Scratch::new();
    let mut inputs = Vec::new();
    for value in
        points(Width::U64)
            .into_iter()
            .chain([9, 10, 11, 19, 20, 21, u64::MAX - 9, u64::MAX - 10])
    {
        for small in [0, 9, 10, 11, 0x7fff_ffff, 0x8000_0000, u64::from(u32::MAX)] {
            inputs.push([value, 0xaaaa_aaaa_aaaa_aaaa, 0x5555_5555_5555_5555, small]);
        }
    }
    let mut text = String::new();
    let expected: Vec<_> = inputs
        .iter()
        .map(|input| {
            writeln!(text, "{} {} {} {}", input[0], input[1], input[2], input[3]).unwrap();
            let value = input[0] as i64;
            let q = (value / 10) as u64;
            let rem = (value % 10) as u64;
            let word = input[3] as u32 as i32 as i64;
            let small = (word / 10 + word % 10) as u64;
            vec![q ^ (rem << 8) ^ small, input[0], q, rem, small]
        })
        .collect();
    for opt in ["-O0", "-O2"] {
        let object = scratch.0.join(format!("signed{opt}.o"));
        native::object(
            &native::fixture_root().join("recovery/signed-div-constant.c"),
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
                .any(|i| matches!(i.operation, Operation::SignedMul { .. })),
            "{opt}: must exercise implicit IMUL"
        );
        let harness = scratch.0.join(format!("harness{opt}.o"));
        native::object(
            &native::fixture_root().join("harness.c"),
            &harness,
            opt,
            "fixture",
        );
        let oracle = scratch.0.join(format!("oracle{opt}"));
        native::link(&[&object, &harness], &oracle);
        assert_eq!(native::run(&oracle, &text), expected);
        for (input, expected) in inputs.iter().zip(&expected) {
            let mut registers = vec![0; x86::REGISTER_COUNT];
            registers[x86::RDI] = 0x2000;
            registers[x86::RSP] = 0x10000;
            let mut memory = vec![0x91; 65536];
            for (i, value) in input.iter().enumerate() {
                memory[4096 + i * 8..4096 + i * 8 + 8].copy_from_slice(&value.to_le_bytes());
            }
            let run = lifted
                .program
                .execute_with_memory(&registers, 4096, &memory, 100_000)
                .unwrap();
            let mut row = vec![run.value];
            row.extend((0..4).map(|i| {
                u64::from_le_bytes(
                    run.memory[4096 + i * 8..4096 + i * 8 + 8]
                        .try_into()
                        .unwrap(),
                )
            }));
            assert_eq!(&row, expected, "{opt}: {input:?}");
        }
        let mut code = nirvana::emit::emit_c(&lifted.program).unwrap().code;
        writeln!(
            code,
            "\n#define TEST_REGISTER_COUNT {}",
            lifted.program.register_count()
        )
        .unwrap();
        code.push_str(r#"
#include <inttypes.h>
#include <stdio.h>
#include <string.h>
int main(void) {
    uint64_t state[4];
    while(scanf("%" SCNu64 " %" SCNu64 " %" SCNu64 " %" SCNu64,&state[0],&state[1],&state[2],&state[3])==4) {
        uint8_t memory[65536]; memset(memory,0x91,sizeof(memory));
        uint64_t r[TEST_REGISTER_COUNT]={0}; r[7]=0x2000; r[4]=0x10000; memcpy(memory+4096,state,sizeof(state));
        uint64_t result=nirvana_fn(r,memory,4096,sizeof(memory)); memcpy(state,memory+4096,sizeof(state));
        printf("%" PRIu64 " %" PRIu64 " %" PRIu64 " %" PRIu64 " %" PRIu64 "\n",result,state[0],state[1],state[2],state[3]);
    }
    return 0;
}
"#);
        let source = scratch.0.join(format!("generated{opt}.c"));
        std::fs::write(&source, code).unwrap();
        let binary = scratch.0.join(format!("generated{opt}"));
        native::compile_c(
            &source,
            &binary,
            &[
                opt,
                "-fsanitize=undefined",
                "-fno-sanitize-recover=undefined",
            ],
        );
        assert_eq!(native::run(&binary, &text), expected);
        if opt == "-O2" {
            use crate::support::module_fixture::{self, Case};
            let module = nirvana::module_ir::lift_elf(
                &std::fs::read(&oracle).unwrap(),
                "fixture",
                Default::default(),
            )
            .unwrap();
            let root = module
                .program
                .functions()
                .iter()
                .find(|f| f.name == "fixture")
                .unwrap();
            let mut initial = module.initial_registers();
            for (i, value) in initial.iter_mut().enumerate() {
                if i != x86::RSP {
                    *value = 0x83bd_2a01_0000_0000 + i as u64;
                }
            }
            for flag in [x86::CF, x86::ZF, x86::SF, x86::OF, x86::PF] {
                initial[flag] = 1;
            }
            initial[x86::DF] = 0;
            let mut cases = Vec::new();
            for input in inputs.iter().step_by(19) {
                cases.push(Case {
                    input: *input,
                    pc: module.program.entry(),
                    budget: 10_000,
                    patch: None,
                });
            }
            for instruction in module
                .program
                .instructions()
                .iter()
                .filter(|i| (root.address..root.address + root.size).contains(&i.address()))
            {
                for budget in [0, 1, 3] {
                    cases.push(Case {
                        input: [u64::MAX, 91, 92, 0x8000_0000],
                        pc: instruction.address(),
                        budget,
                        patch: None,
                    });
                }
            }
            let rows: Vec<_> = cases
                .iter()
                .map(|case| module_fixture::expected_with_state(&module, case, Some(&initial)).0)
                .collect();
            let directory = scratch.0.join("module");
            std::fs::create_dir(&directory).unwrap();
            let compared = module_fixture::check_generated_with_state(
                &module,
                &cases,
                &rows,
                &directory,
                true,
                &[1, 64],
                Some(&initial),
            );
            println!("{compared} signed IMUL module state/resume comparisons across all backends");
        }
        println!(
            "{opt}: {} signed division native/i64/IR/C cases",
            inputs.len()
        );
    }
}

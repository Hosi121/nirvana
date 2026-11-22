use crate::support::native;
use native::{Scratch, fixture_root, link, object, run};
use nirvana::ir::{Assignment, BinaryOp, Control, Expr, IrInstruction, Program, Reg, Width};
use nirvana::readable::{ReadableOptions, emit_readable_c_with_options};
use std::fmt::Write as _;

#[test]
fn narrowed_unsigned_locals_preserve_u64_products_above_int_and_u32_limits() {
    let r = |i| Expr::Register(Reg(i));
    let add = |a, b| Expr::binary(BinaryOp::Add, a, b);
    let mul = |a, b| Expr::binary(BinaryOp::Mul, a, b);
    let p = Program::new(
        0,
        4,
        vec![IrInstruction {
            address: 0,
            size: 1,
            assignments: vec![
                Assignment {
                    destination: Reg(1).into(),
                    value: Expr::load(r(0), Width::U16),
                },
                Assignment {
                    destination: Reg(2).into(),
                    value: Expr::load(add(r(0), Expr::Const(2)), Width::U16),
                },
                Assignment {
                    destination: Reg(3).into(),
                    value: Expr::load(r(0), Width::U32),
                },
            ],
            control: Control::Return(add(mul(r(1), r(2)), mul(r(3), r(3)))),
        }],
    )
    .unwrap();
    let scratch = Scratch::new();
    let mut inputs = String::new();
    let mut expected = Vec::new();
    for a in [0, 1, 0x7fff, 0x8000, 0xffff, 0x1ffff, u64::MAX] {
        for b in [0, 1, 0x7fff, 0x8000, 0xffff, 0x1ffff, u64::MAX] {
            writeln!(inputs, "{a} {b} 17 19").unwrap();
            let mut memory = vec![0; 8];
            memory[..2].copy_from_slice(&(a as u16).to_le_bytes());
            memory[2..4].copy_from_slice(&(b as u16).to_le_bytes());
            let result = p
                .execute_with_memory(&[4096, 0, 0, 0], 4096, &memory, 1)
                .unwrap();
            expected.push(vec![result.value, a, b, 17, 19]);
        }
    }
    for views in [false, true] {
        let output = emit_readable_c_with_options(
            &p,
            ReadableOptions {
                stack_register: None,
                recover_objects: views,
                coalesce_locals: true,
                compact_memory: true,
            },
        )
        .unwrap();
        assert!(output.locals.iter().any(|v| v.width == Width::U16));
        assert!(output.locals.iter().any(|v| v.width == Width::U32));
        let args = output
            .parameters
            .iter()
            .map(|r| format!("machine[{}]", r.0))
            .collect::<Vec<_>>()
            .join(", ");
        let wrapper = format!(
            r#"
uint64_t fixture(uint64_t *state) {{
    uint8_t memory[8]={{0}};
    for(unsigned i=0;i<2;++i) {{ memory[i]=(uint8_t)(state[0]>>(i*8)); memory[i+2]=(uint8_t)(state[1]>>(i*8)); }}
    uint64_t machine[4]={{4096,0,0,0}};
    return nirvana_readable({args},memory,UINT64_C(4096),sizeof(memory));
}}
"#
        );
        for opt in ["-O0", "-O2"] {
            let source = scratch.0.join(format!("types{views}{opt}.c"));
            std::fs::write(&source, output.code.clone() + &wrapper).unwrap();
            let compiled = source.with_extension("o");
            let harness = scratch.0.join(format!("harness{views}{opt}.o"));
            let binary = source.with_extension("bin");
            object(&source, &compiled, opt, "fixture");
            object(&fixture_root().join("harness.c"), &harness, opt, "fixture");
            link(&[&compiled, &harness], &binary);
            assert_eq!(run(&binary, &inputs), expected, "{views} {opt}");
        }
    }
}

#[test]
fn signed_storage_decodes_unsigned_reads_and_preserves_wrapping_lazy_loads_and_faults() {
    use crate::support::checked_c;
    use nirvana::ir::{AccessKind, Place, RunStatus, UnaryOp};
    let r = |n| Expr::Register(Reg(n));
    let c = Expr::Const;
    let b = |op, a, z| Expr::binary(op, a, z);
    let address = |n| b(BinaryOp::Add, r(nirvana::x86::RDI), c(n));
    let load = |n| Expr::load(address(n), Width::U64);
    let se = |v| Expr::unary(UnaryOp::SignExtend(Width::U32), v);
    let set = |n, v| Assignment {
        destination: Reg(n).into(),
        value: v,
    };
    let store = |n, v| Assignment {
        destination: Place::Memory {
            address: address(n),
            width: Width::U64,
        },
        value: v,
    };
    let p = Program::new(
        0,
        32,
        vec![
            IrInstruction {
                address: 0,
                size: 1,
                assignments: vec![
                    set(0, load(0)),
                    set(1, se(r(0))),
                    set(2, load(8)),
                    set(3, se(r(2))),
                    store(16, b(BinaryOp::Ult, r(1), r(3))),
                    store(24, b(BinaryOp::Shr, r(1), c(1))),
                    set(4, b(BinaryOp::SDiv, r(1), c((-31i64) as u64))),
                    set(5, b(BinaryOp::SRem, r(3), c(31))),
                    set(
                        6,
                        Expr::select(b(BinaryOp::And, r(0), c(1)), se(load(40)), se(load(48))),
                    ),
                    store(32, r(6)),
                ],
                control: Control::Next,
            },
            IrInstruction {
                address: 1,
                size: 1,
                assignments: vec![set(1, se(b(BinaryOp::Add, r(1), r(3)))), store(8, r(1))],
                control: Control::Return(b(
                    BinaryOp::Add,
                    b(BinaryOp::Add, r(4), r(5)),
                    b(BinaryOp::Mul, r(1), r(3)),
                )),
            },
        ],
    )
    .unwrap();
    let mut unsigned = p.instructions().to_vec();
    unsigned[1].assignments[0].value = Expr::unary(
        UnaryOp::Extract {
            start: 0,
            width: Width::U32,
        },
        r(2),
    );
    let unsigned = Program::new(0, 32, unsigned).unwrap();
    for (case, p) in [("wrap", p), ("unsigned-overwrite", unsigned)] {
        let values = [0, 1, 0x7fff_ffff, 0x8000_0000, 0xffff_ffff, u64::MAX];
        let mut inputs = String::new();
        let mut expected = Vec::new();
        for pointer in [
            4095u64,
            4096,
            4097,
            4104,
            4112,
            4120,
            4144,
            4152,
            4159,
            4160,
            u64::MAX - 7,
            u64::MAX,
        ] {
            for &a in &values {
                for &b in &values {
                    let words = [a, b, a ^ b, 0x8a99_fedc_1122_3344];
                    writeln!(
                        inputs,
                        "{pointer} {} {} {} {}",
                        words[0], words[1], words[2], words[3]
                    )
                    .unwrap();
                    let mut memory: Vec<u8> = (0..64).map(|i| (i * 29 + 7) as u8).collect();
                    for (index, word) in words.into_iter().enumerate() {
                        if let Some(offset) = pointer
                            .checked_add(index as u64 * 8)
                            .and_then(|a| a.checked_sub(4096))
                            .filter(|&n| n <= 56)
                        {
                            memory[offset as usize..offset as usize + 8]
                                .copy_from_slice(&word.to_le_bytes());
                        }
                    }
                    let mut registers = [0; 32];
                    registers[nirvana::x86::RDI] = pointer;
                    registers[nirvana::x86::RSP] = 4160;
                    let report = p.run_with_memory(&registers, 4096, &memory, 20).unwrap();
                    let mut row = match report.status {
                        RunStatus::Returned(v) => vec![0, 0, 0, 0, v],
                        RunStatus::Fault(f) => vec![
                            1,
                            f.address,
                            if f.access == AccessKind::Read { 1 } else { 2 },
                            f.width.bytes() as u64,
                            0,
                        ],
                        other => panic!("{other:?}"),
                    };
                    row.extend(
                        report
                            .state
                            .memory
                            .chunks_exact(8)
                            .map(|bytes| u64::from_le_bytes(bytes.try_into().unwrap())),
                    );
                    expected.push(row);
                }
            }
        }
        let scratch = Scratch::new();
        for objects in [false, true] {
            for coalesce in [false, true] {
                let output = emit_readable_c_with_options(
                    &p,
                    ReadableOptions {
                        stack_register: None,
                        recover_objects: objects,
                        coalesce_locals: coalesce,
                        compact_memory: true,
                    },
                )
                .unwrap();
                assert!(
                    output
                        .locals
                        .iter()
                        .any(|l| l.signed_width == Some(Width::U32)),
                    "{}",
                    output.code
                );
                let source = scratch
                    .0
                    .join(format!("signed-{case}-{objects}-{coalesce}.c"));
                std::fs::write(&source, checked_c::source(&output, 32, 4)).unwrap();
                for opt in ["-O0", "-O2"] {
                    let binary = source.with_extension(format!("{opt}.bin"));
                    native::compile_c(
                        &source,
                        &binary,
                        &[
                            opt,
                            "-fsanitize=undefined",
                            "-fno-sanitize-recover=undefined",
                        ],
                    );
                    assert_eq!(
                        native::run_fields(&binary, &inputs, 13),
                        expected,
                        "{case}/{objects}/{coalesce}/{opt}"
                    );
                }
            }
        }
    }
}

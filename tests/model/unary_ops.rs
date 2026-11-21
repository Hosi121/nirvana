use crate::support::{
    checked_c,
    ir::{c, r, unary_value},
    native,
};
use nirvana::ir::{
    Assignment, BinaryOp as B, Control, Expr, IrInstruction, Place, Program, Reg, RunStatus,
    UnaryOp as U, Width,
};
use std::fmt::Write as _;

const WIDTHS: [Width; 4] = [Width::U8, Width::U16, Width::U32, Width::U64];
fn b(op: B, a: Expr, z: Expr) -> Expr {
    Expr::binary(op, a, z)
}
fn u(width: Width, value: Expr) -> Expr {
    Expr::unary(U::SignExtend(width), value)
}
fn program(value: Expr, count: usize) -> Program {
    Program::new(
        0,
        count,
        vec![IrInstruction {
            address: 0,
            size: 1,
            assignments: vec![],
            control: Control::Return(value),
        }],
    )
    .unwrap()
}
fn boundaries() -> Vec<u64> {
    let mut values = vec![
        0,
        1,
        2,
        127,
        128,
        129,
        255,
        256,
        32767,
        32768,
        65535,
        65536,
        0x7fff_ffff,
        0x8000_0000,
        0xffff_ffff,
        1 << 32,
        (1 << 63) - 1,
        1 << 63,
        u64::MAX,
    ];
    let mut seed = 0x7654_3210_fedc_ba98u64;
    for _ in 0..64 {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        values.push(seed);
    }
    values
}

#[test]
fn sign_extension_preserves_width_and_matches_independent_integer_conversions() {
    let mut compared = 0;
    for width in WIDTHS {
        let op = U::SignExtend(width);
        let p = program(u(width, r(0)), 1);
        let values: Vec<_> = match width {
            Width::U8 => (0..=255).collect(),
            Width::U16 => (0..=65535).collect(),
            _ => boundaries(),
        };
        let mut seed = 0x8123_4567_89ab_cdefu64;
        for value in values {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            let value = value | (seed & !width.mask());
            let expected = unary_value(op, value);
            assert_eq!(op.evaluate(value), expected);
            assert_eq!(p.execute(&[value], 1).unwrap().value, expected);
            assert_eq!(
                nirvana::simplify::simplify(&u(width, c(value))),
                c(expected)
            );
            compared += 1;
        }
    }
    println!("{compared} independent signed integer conversion/IR/folding comparisons");
}

#[cfg(target_arch = "x86_64")]
#[test]
fn explicit_extension_matches_native_movsx_and_movsxd() {
    use std::arch::asm;
    let mut count = 0;
    for width in WIDTHS {
        for value in boundaries() {
            let actual: u64;
            unsafe {
                match width {
                    Width::U8 => {
                        asm!("movsx {result}, {source:l}",result=lateout(reg)actual,source=in(reg)value,options(pure,nomem,nostack,preserves_flags))
                    }
                    Width::U16 => {
                        asm!("movsx {result}, {source:x}",result=lateout(reg)actual,source=in(reg)value,options(pure,nomem,nostack,preserves_flags))
                    }
                    Width::U32 => {
                        asm!("movsxd {result}, {source:e}",result=lateout(reg)actual,source=in(reg)value,options(pure,nomem,nostack,preserves_flags))
                    }
                    Width::U64 => {
                        asm!("mov {result}, {source}",result=lateout(reg)actual,source=in(reg)value,options(pure,nomem,nostack,preserves_flags))
                    }
                }
            }
            assert_eq!(U::SignExtend(width).evaluate(value), actual);
            count += 1;
        }
    }
    println!("{count} native MOVSX/MOVSXD/identity comparisons");
}

#[test]
fn raw_ssa_and_readable_c_keep_unsigned_bit_patterns_without_undefined_conversions() {
    let scratch = native::Scratch::new();
    let mut code = String::from("#include <stdint.h>\n#include <inttypes.h>\n#include <stdio.h>\n");
    let mut names = Vec::new();
    for width in WIDTHS {
        let p = program(u(width, r(0)), 1);
        let graph = nirvana::ssa::SsaFunction::build(&p).unwrap();
        let lowered = nirvana::ssa_destroy::lower(&p, &graph, &Default::default()).unwrap();
        for (mode, text, count) in [
            (
                "raw",
                nirvana::emit::emit_c(&p).unwrap().code,
                p.register_count(),
            ),
            (
                "ssa",
                lowered.emit_c().unwrap().code,
                lowered.program().register_count(),
            ),
            (
                "readable",
                nirvana::readable::emit_readable_c(&p).unwrap().code,
                1,
            ),
        ] {
            let index = names.len();
            let name = format!("probe{index}");
            let prefix = format!("nv{index}_");
            code.push_str(&text.replace("nirvana_", &prefix));
            if mode == "readable" {
                writeln!(
                    code,
                    "uint64_t {name}(uint64_t value) {{ return {prefix}readable(value); }}"
                )
                .unwrap();
            } else {
                writeln!(code,"uint64_t {name}(uint64_t value) {{ uint64_t r[{count}]={{0}};r[0]=value;return {prefix}fn(r); }}").unwrap();
            }
            names.push(name);
        }
    }
    code.push_str("int main(void) { uint64_t value;while(scanf(\"%\" SCNu64,&value)==1) {\n");
    for name in &names {
        writeln!(code, "printf(\"%\" PRIu64 \" \",{name}(value));").unwrap();
    }
    code.push_str("putchar('\\n');}return 0;}\n");
    let mut input = String::new();
    let mut expected = Vec::new();
    for value in boundaries() {
        writeln!(input, "{value}").unwrap();
        expected.push(
            WIDTHS
                .into_iter()
                .flat_map(|w| [unary_value(U::SignExtend(w), value); 3])
                .collect::<Vec<_>>(),
        );
    }
    let path = scratch.0.join("generated.c");
    std::fs::write(&path, code).unwrap();
    for opt in ["-O0", "-O2"] {
        let binary = scratch.0.join(opt);
        native::compile_c(
            &path,
            &binary,
            &[
                opt,
                "-fsanitize=undefined",
                "-fno-sanitize-recover=undefined",
            ],
        );
        assert_eq!(native::run_fields(&binary, &input, names.len()), expected);
    }
}

fn expand(e: &Expr) -> Expr {
    match e {
        Expr::Unary(U::SignExtend(width), value) => {
            let sign = c(1u64 << (width.bits() - 1));
            b(
                B::Sub,
                b(
                    B::Xor,
                    b(B::And, expand(value), c(width.mask())),
                    sign.clone(),
                ),
                sign,
            )
        }
        Expr::Binary(op, a, z) => b(*op, expand(a), expand(z)),
        Expr::Load { address, width } => Expr::load(expand(address), *width),
        Expr::Select {
            condition,
            taken,
            not_taken,
        } => Expr::select(expand(condition), expand(taken), expand(not_taken)),
        value => value.clone(),
    }
}
fn memory_program(width: Width) -> Program {
    let load = |offset| Expr::load(b(B::Add, r(7), c(offset)), Width::U64);
    Program::new(
        0,
        32,
        vec![IrInstruction {
            address: 0,
            size: 1,
            assignments: vec![
                Assignment {
                    destination: Reg(0).into(),
                    value: u(width, b(B::Add, load(0), load(8))),
                },
                Assignment {
                    destination: Place::Memory {
                        address: b(B::Add, r(7), c(16)),
                        width: Width::U64,
                    },
                    value: u(width, Expr::select(load(24), r(0), load(32))),
                },
            ],
            control: Control::Return(b(B::Xor, u(width, load(40)), r(0))),
        }],
    )
    .unwrap()
}

#[test]
fn nested_loads_lazy_arms_and_pre_rhs_store_faults_match_the_expanded_ir_and_c() {
    let scratch = native::Scratch::new();
    let mut comparisons = 0;
    for width in WIDTHS {
        let p = memory_program(width);
        let mut instructions = p.instructions().to_vec();
        for i in &mut instructions {
            for a in &mut i.assignments {
                a.value = expand(&a.value);
            }
            if let Control::Return(e) = &mut i.control {
                *e = expand(e);
            }
        }
        let expanded = Program::new(0, 32, instructions).unwrap();
        let mut text = String::new();
        let mut expected = Vec::new();
        let mut statuses = [0; 3];
        for pointer in [
            4096,
            4097,
            4112,
            4120,
            4128,
            4136,
            4144,
            4152,
            4159,
            u64::MAX,
        ] {
            for flag in [0u64, 1] {
                for value in [0, 127, 128, 32768, 1 << 31, u64::MAX] {
                    let words = [value, 1, 19, flag];
                    writeln!(text, "{pointer} {value} 1 19 {flag}").unwrap();
                    let mut memory: Vec<_> = (0..64usize)
                        .map(|i| i.wrapping_mul(29).wrapping_add(7) as u8)
                        .collect();
                    for (i, word) in words.into_iter().enumerate() {
                        if let Some(offset) = pointer
                            .checked_add(i as u64 * 8)
                            .and_then(|v| v.checked_sub(4096))
                            .filter(|&v| v <= 56)
                        {
                            memory[offset as usize..offset as usize + 8]
                                .copy_from_slice(&word.to_le_bytes());
                        }
                    }
                    let mut regs = [0; 32];
                    regs[7] = pointer;
                    regs[4] = 4160;
                    for limit in 0..3 {
                        assert_eq!(
                            p.run_with_memory(&regs, 4096, &memory, limit).unwrap(),
                            expanded
                                .run_with_memory(&regs, 4096, &memory, limit)
                                .unwrap()
                        );
                    }
                    let report = expanded.run_with_memory(&regs, 4096, &memory, 2).unwrap();
                    let mut row = match report.status {
                        RunStatus::Returned(v) => {
                            statuses[0] += 1;
                            vec![0, 0, 0, 0, v]
                        }
                        RunStatus::Fault(f) => {
                            let access = if f.access == nirvana::ir::AccessKind::Read {
                                1
                            } else {
                                2
                            };
                            statuses[access] += 1;
                            vec![1, f.address, access as u64, f.width.bytes() as u64, 0]
                        }
                        _ => panic!("straight-line source suspended"),
                    };
                    row.extend(
                        report
                            .state
                            .memory
                            .chunks_exact(8)
                            .map(|v| u64::from_le_bytes(v.try_into().unwrap())),
                    );
                    expected.push(row);
                }
            }
        }
        assert!(statuses.into_iter().all(|n| n > 0));
        for coalesce in [false, true] {
            for objects in [false, true] {
                let output = nirvana::readable::emit_readable_c_with_options(
                    &p,
                    nirvana::readable::ReadableOptions {
                        stack_register: Some(Reg(4)),
                        coalesce_locals: coalesce,
                        recover_objects: objects,
                        compact_memory: true,
                    },
                )
                .unwrap();
                let source = scratch
                    .0
                    .join(format!("memory-{}-{coalesce}-{objects}.c", width.bits()));
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
                    assert_eq!(native::run_fields(&binary, &text, 13), expected);
                    comparisons += expected.len();
                }
            }
        }
    }
    println!("{comparisons} sanitized C return/fault/full-RAM comparisons for explicit extensions");
}

use crate::support::ir::{c, insert_value, r};
use nirvana::ir::{Assignment, BinaryOp as B, Control, Expr, IrInstruction, Program, Reg, Width};
use nirvana::known_bits::KnownBits as K;
const WIDTHS: [Width; 4] = [Width::U8, Width::U16, Width::U32, Width::U64];
fn program(value: Expr, assignments: Vec<Assignment>) -> Program {
    Program::new(
        0,
        3,
        vec![IrInstruction {
            address: 0,
            size: 1,
            assignments,
            control: Control::Return(value),
        }],
    )
    .unwrap()
}
fn values() -> Vec<u64> {
    vec![
        0,
        1,
        7,
        127,
        128,
        255,
        256,
        65535,
        65536,
        u32::MAX as u64,
        1 << 32,
        1 << 63,
        u64::MAX,
        0x1234_5678_9abc_def0,
        0xa5a5_5a5a_c3c3_3c3c,
    ]
}
#[test]
fn every_static_insert_matches_independent_per_bit_selection() {
    let mut checked = 0;
    for width in WIDTHS {
        for start in 0..=255u8 {
            let op = B::Insert { start, width };
            let p = program(Expr::binary(op, r(0), r(1)), vec![]);
            for base in values() {
                for value in values() {
                    let expected = insert_value(start, width, base, value);
                    assert_eq!(op.evaluate(base, value), expected);
                    assert_eq!(p.execute(&[base, value, 0], 1).unwrap().value, expected);
                    checked += 1;
                }
            }
        }
    }
    println!(
        "{checked} total insert/per-bit oracle observations across every static position and width"
    );
}
#[test]
fn insert_facts_and_unsigned_bounds_cover_changed_and_preserved_bits() {
    let mut checked = 0;
    let mut seed = 0xcafe_7391_1234_a1b2u64;
    let mut next = || {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        seed
    };
    for width in WIDTHS {
        for start in 0..=255u8 {
            let op = B::Insert { start, width };
            for _ in 0..16 {
                let a = next();
                let b = next();
                let az = next() & !a;
                let ao = next() & a;
                let bz = next() & !b;
                let bo = next() & b;
                let fact = K::binary(op, K::new(az, ao).unwrap(), K::new(bz, bo).unwrap());
                assert!(fact.contains(insert_value(start, width, a, b)));
                checked += 1;
            }
        }
    }
    let mut bounds_checked = 0;
    for width in WIDTHS {
        for start in [0, 1, 7, 8, 15, 16, 31, 32, 63, 64, 255] {
            for a_bits in [0u32, 7, 8, 16, 32, 64] {
                for b_bits in [0u32, 7, 8, 16, 32, 64] {
                    let mask = |n| u64::MAX.checked_shr(64 - n).unwrap_or(0);
                    let assignments = vec![
                        Assignment {
                            destination: Reg(0).into(),
                            value: Expr::binary(B::And, r(0), c(mask(a_bits))),
                        },
                        Assignment {
                            destination: Reg(1).into(),
                            value: Expr::binary(B::And, r(1), c(mask(b_bits))),
                        },
                        Assignment {
                            destination: Reg(2).into(),
                            value: Expr::binary(B::Insert { start, width }, r(0), r(1)),
                        },
                    ];
                    let p = program(r(2), assignments);
                    let expected =
                        64 - insert_value(start, width, mask(a_bits), mask(b_bits)).leading_zeros();
                    let types = nirvana::type_infer::TypeAnalysis::analyze(&p).unwrap();
                    let id = types
                        .graph()
                        .point(nirvana::ssa::Site {
                            instruction: 0,
                            assignment: Some(2),
                        })
                        .unwrap()
                        .definition
                        .unwrap()
                        .0;
                    assert_eq!(u32::from(types.values()[id].maximum_bits), expected);
                    let facts = nirvana::known_bits::analyze_values(&p, types.graph()).unwrap();
                    assert_eq!(64 - facts[id].maximum().leading_zeros(), expected);
                    let storage = nirvana::value_width::ValueWidths::analyze(&p).width(Reg(2));
                    assert_eq!(
                        storage,
                        WIDTHS.into_iter().find(|w| w.bits() >= expected).unwrap()
                    );
                    bounds_checked += 1;
                }
            }
        }
    }
    println!(
        "{checked} sparse insert fact observations and {bounds_checked} shared SSA/type/storage bound checks"
    );
}

#[test]
fn raw_ssa_and_readable_insert_helpers_keep_bits_under_c_optimization_and_ubsan() {
    use crate::support::native;
    use std::fmt::Write as _;
    let scratch = native::Scratch::new();
    let mut code = String::from("#include <stdint.h>\n#include <inttypes.h>\n#include <stdio.h>\n");
    let mut ops = Vec::new();
    let mut names = Vec::new();
    for width in WIDTHS {
        for start in [0, 1, 7, 8, 15, 16, 31, 32, 60, 63, 64, 255] {
            let op = B::Insert { start, width };
            ops.push(op);
            let p = program(Expr::binary(op, r(0), r(1)), vec![]);
            let graph = nirvana::ssa::SsaFunction::build(&p).unwrap();
            let lowered = nirvana::ssa_destroy::lower(&p, &graph, &Default::default()).unwrap();
            let readable = nirvana::readable::emit_readable_c(&p).unwrap();
            let args = readable
                .parameters
                .iter()
                .map(|reg| {
                    if reg.0 == 0 {
                        "base"
                    } else if reg.0 == 1 {
                        "value"
                    } else {
                        panic!()
                    }
                })
                .collect::<Vec<_>>()
                .join(",");
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
                ("readable", readable.code, 3),
            ] {
                let index = names.len();
                let name = format!("probe{index}");
                let prefix = format!("nv{index}_");
                code.push_str(&text.replace("nirvana_", &prefix));
                if mode == "readable" {
                    writeln!(code,"uint64_t {name}(uint64_t base,uint64_t value) {{ (void)base;(void)value;return {prefix}readable({args}); }}").unwrap();
                } else {
                    writeln!(code,"uint64_t {name}(uint64_t base,uint64_t value) {{ uint64_t r[{count}]={{0}};r[0]=base;r[1]=value;return {prefix}fn(r); }}").unwrap();
                }
                names.push(name);
            }
        }
    }
    code.push_str("int main(void) {uint64_t base,value;while(scanf(\"%\" SCNu64 \" %\" SCNu64,&base,&value)==2) {\n");
    for name in &names {
        writeln!(code, "printf(\"%\" PRIu64 \" \",{name}(base,value));").unwrap();
    }
    code.push_str("putchar('\\n');}return 0;}\n");
    let path = scratch.0.join("generated.c");
    std::fs::write(&path, code).unwrap();
    let mut input = String::new();
    let mut expected = Vec::new();
    for base in values() {
        for value in values() {
            writeln!(input, "{base} {value}").unwrap();
            expected.push(
                ops.iter()
                    .flat_map(|op| {
                        let B::Insert { start, width } = *op else {
                            unreachable!()
                        };
                        [insert_value(start, width, base, value); 3]
                    })
                    .collect::<Vec<_>>(),
            );
        }
    }
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
    println!(
        "{} numeric insert C/per-bit comparisons across raw, SSA, readable, O0/O2 and UBSan",
        expected.len() * names.len() * 2
    );
}

#[test]
fn insert_operands_keep_lazy_reads_store_prechecks_full_ram_and_first_faults() {
    use crate::support::{bit_insert, checked_c, native};
    use nirvana::ir::{AccessKind, RunStatus};
    use std::fmt::Write as _;
    let scratch = native::Scratch::new();
    let mut checked = 0;
    for (index, op) in [
        B::Insert {
            start: 0,
            width: Width::U8,
        },
        B::Insert {
            start: 8,
            width: Width::U8,
        },
        B::Insert {
            start: 60,
            width: Width::U16,
        },
        B::Insert {
            start: 64,
            width: Width::U64,
        },
        B::Insert {
            start: 0,
            width: Width::U64,
        },
    ]
    .into_iter()
    .enumerate()
    {
        let source = bit_insert::memory_program(op);
        let expanded = bit_insert::expanded(&source);
        let mut text = String::new();
        let mut expected = Vec::new();
        let mut statuses = [0; 3];
        for pointer in [
            4096u64,
            4097,
            4104,
            4112,
            4120,
            4128,
            4136,
            4152,
            4159,
            u64::MAX,
        ] {
            for flag in [0u64, 1] {
                for value in [0, 1, 128, u64::MAX] {
                    let words = [value, !value, 19, flag];
                    writeln!(
                        text,
                        "{pointer} {} {} {} {}",
                        words[0], words[1], words[2], words[3]
                    )
                    .unwrap();
                    let mut ram: Vec<_> = (0..64u8)
                        .map(|i| i.wrapping_mul(29).wrapping_add(7))
                        .collect();
                    for (word, value) in words.into_iter().enumerate() {
                        if let Some(offset) = pointer
                            .checked_add(word as u64 * 8)
                            .and_then(|p| p.checked_sub(4096))
                            .filter(|p| *p <= 56)
                        {
                            ram[offset as usize..offset as usize + 8]
                                .copy_from_slice(&value.to_le_bytes());
                        }
                    }
                    let mut regs = [0; 32];
                    regs[7] = pointer;
                    regs[4] = 4160;
                    for limit in 0..4 {
                        assert_eq!(
                            source.run_with_memory(&regs, 4096, &ram, limit),
                            expanded.run_with_memory(&regs, 4096, &ram, limit)
                        );
                    }
                    let report = expanded.run_with_memory(&regs, 4096, &ram, 3).unwrap();
                    let mut row = match report.status {
                        RunStatus::Returned(v) => {
                            statuses[0] += 1;
                            vec![0, 0, 0, 0, v]
                        }
                        RunStatus::Fault(f) => {
                            let kind = if f.access == AccessKind::Read { 1 } else { 2 };
                            statuses[kind] += 1;
                            vec![1, f.address, kind as u64, f.width.bytes() as u64, 0]
                        }
                        _ => panic!("straight-line insert must return or fault"),
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
                    &source,
                    nirvana::readable::ReadableOptions {
                        stack_register: Some(Reg(4)),
                        coalesce_locals: coalesce,
                        recover_objects: objects,
                        compact_memory: true,
                    },
                )
                .unwrap();
                let path = scratch
                    .0
                    .join(format!("insert-{index}-{coalesce}-{objects}.c"));
                std::fs::write(&path, checked_c::source(&output, 32, 4)).unwrap();
                for opt in ["-O0", "-O2"] {
                    let binary = path.with_extension(format!("{opt}.bin"));
                    native::compile_c(
                        &path,
                        &binary,
                        &[
                            opt,
                            "-fsanitize=undefined",
                            "-fno-sanitize-recover=undefined",
                        ],
                    );
                    assert_eq!(
                        native::run_fields(&binary, &text, 13),
                        expected,
                        "{op:?}/{coalesce}/{objects}/{opt}"
                    );
                    checked += expected.len();
                }
            }
        }
    }
    println!(
        "{checked} insert C return/full-RAM/first-fault observations with lazy RHS and destination prechecks"
    );
}

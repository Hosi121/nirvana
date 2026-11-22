use crate::support::native;
use nirvana::{frontend, readable, x86};
use std::fmt::Write as _;

#[test]
fn canonical_word_operators_keep_zero_minimum_and_negative_literal_bits_in_c() {
    use crate::support::ir::{c, division_value, r, unary_value};
    use nirvana::ir::{BinaryOp as B, Control, Expr, IrInstruction, Program, UnaryOp, Width};
    let scratch = native::Scratch::new();
    let mut code = String::from("#include <stdint.h>\n#include <stdio.h>\n#include <inttypes.h>\n");
    let mut names = Vec::new();
    let mut cases = Vec::new();
    for width in [Width::U8, Width::U16, Width::U32] {
        for op in [B::SDiv, B::SRem] {
            for divisor in [0, 1, u64::MAX, 1 << 63, 3, 0u64.wrapping_sub(7)] {
                let expression = Expr::binary(
                    B::And,
                    Expr::binary(
                        op,
                        Expr::unary(UnaryOp::SignExtend(width), r(0)),
                        c(divisor),
                    ),
                    c(width.mask()),
                );
                let p = Program::new(
                    0,
                    1,
                    vec![IrInstruction {
                        address: 0,
                        size: 1,
                        assignments: vec![],
                        control: Control::Return(expression),
                    }],
                )
                .unwrap();
                let output = readable::emit_readable_c(&p).unwrap();
                let args = if output.parameters.is_empty() {
                    ""
                } else {
                    assert_eq!(output.parameters, vec![nirvana::ir::Reg(0)]);
                    "x"
                };
                let prefix = format!("case_{}_", names.len());
                code.push_str(&output.code.replace("nirvana_", &prefix));
                let name = format!("probe{}", names.len());
                writeln!(
                    code,
                    "uint64_t {name}(uint64_t x) {{(void)x;return {prefix}readable({args});}}"
                )
                .unwrap();
                names.push(name);
                cases.push((width, op, divisor));
            }
        }
    }
    let mut values = vec![
        0,
        1,
        2,
        127,
        128,
        255,
        32767,
        32768,
        65535,
        (1 << 31) - 1,
        1 << 31,
        u64::MAX,
    ];
    let mut seed = 0x8934_cdd4_287f_fe43;
    for _ in 0..128 {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        values.push(seed);
    }
    writeln!(
        code,
        "static uint64_t (*const probes[])(uint64_t)={{{}}};",
        names.join(",")
    )
    .unwrap();
    code.push_str("int main(void) {uint64_t x;while(scanf(\"%\" SCNu64,&x)==1) {for(unsigned i=0;i<sizeof(probes)/sizeof(probes[0]);++i) printf(\"%\" PRIu64 \" \",probes[i](x));putchar('\\n');}return 0;}\n");
    let mut input = String::new();
    let mut expected = Vec::new();
    for x in values {
        writeln!(input, "{x}").unwrap();
        expected.push(
            cases
                .iter()
                .map(|&(w, op, d)| {
                    division_value(op, unary_value(UnaryOp::SignExtend(w), x), d) & w.mask()
                })
                .collect::<Vec<_>>(),
        );
    }
    let file = scratch.0.join("canonical.c");
    std::fs::write(&file, code).unwrap();
    for opt in ["-O0", "-O2"] {
        let bin = scratch.0.join(opt);
        native::compile_c(
            &file,
            &bin,
            &[
                opt,
                "-fsanitize=undefined",
                "-fno-sanitize-recover=undefined",
            ],
        );
        assert_eq!(native::run_fields(&bin, &input, names.len()), expected);
    }
    println!(
        "{} canonical word C boundary observations",
        expected.len() * names.len() * 2
    );
}

#[test]
fn gcc_word_quotients_remainders_and_widened_returns_keep_machine_bits() {
    let scratch = native::Scratch::new();
    let mut cases = Vec::new();
    for d in [3i64, 5, 7, 10, 11, 13, 15, 17, 19, 31] {
        for neg in [false, true] {
            for rem in [false, true] {
                cases.push((
                    format!(
                        "{}32_{}{d}",
                        if rem { "r" } else { "q" },
                        if neg { "n" } else { "p" }
                    ),
                    if neg { -d } else { d },
                    rem,
                    false,
                ));
            }
        }
    }
    cases.extend([
        ("wide_p7".into(), 7, false, true),
        ("wide_n7".into(), -7, false, true),
    ]);
    let mut values = vec![
        0u64,
        1,
        2,
        3,
        4,
        5,
        6,
        7,
        8,
        0x7fff_ffff,
        0x8000_0000,
        0x8000_0001,
        0xffff_ffff,
        u64::MAX,
        1 << 63,
    ];
    for d in [3u64, 5, 7, 10, 11, 13, 15, 17, 19, 31] {
        for q in [1, 2, 3, 0x7fff_ffff / d] {
            let n = q * d;
            for x in [n - 1, n, n + 1] {
                values.extend([x, 0u64.wrapping_sub(x)]);
            }
        }
    }
    let mut seed = 0x9343_feef_1298_4291u64;
    for _ in 0..512 {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        values.push(seed);
    }
    let mut input = String::new();
    let mut expected = Vec::new();
    for &x in &values {
        writeln!(input, "{x}").unwrap();
        expected.push(
            cases
                .iter()
                .map(|(_, d, rem, wide)| {
                    let x = x as i32 as i64;
                    let y = if *rem { x % d } else { x / d };
                    if *wide { y as u64 } else { y as u32 as u64 }
                })
                .collect::<Vec<_>>(),
        );
    }
    let fixture = native::fixture_root().join("recovery/word-signed-reciprocal.c");
    let mut driver =
        String::from("#include <stdint.h>\n#include <inttypes.h>\n#include <stdio.h>\n");
    for (name, _, _, wide) in &cases {
        writeln!(
            driver,
            "{} {name}(int32_t);",
            if *wide { "int64_t" } else { "uint32_t" }
        )
        .unwrap();
    }
    driver.push_str("int main(void) { uint64_t x;while(scanf(\"%\" SCNu64,&x)==1) {\n");
    for (name, _, _, _) in &cases {
        writeln!(
            driver,
            "printf(\"%\" PRIu64 \" \",(uint64_t){name}((int32_t)(uint32_t)x));"
        )
        .unwrap();
    }
    driver.push_str("putchar('\\n'); }return 0;}\n");
    let driver_file = scratch.0.join("driver.c");
    std::fs::write(&driver_file, driver).unwrap();
    let harness = scratch.0.join("driver.o");
    native::object(&driver_file, &harness, "-O2", "fixture");
    let mut programs = Vec::new();
    for opt in ["-O0", "-O2"] {
        let obj = scratch.0.join(format!("word{opt}.o"));
        native::object(&fixture, &obj, opt, "q32_p3");
        let exe = scratch.0.join(format!("native{opt}"));
        native::link(&[&obj, &harness], &exe);
        assert_eq!(native::run_fields(&exe, &input, cases.len()), expected);
        let bytes = std::fs::read(&obj).unwrap();
        for (i, (name, _, _, _)) in cases.iter().enumerate() {
            let lifted = frontend::lift_elf(&bytes, name).unwrap();
            for (&x, row) in values.iter().zip(&expected) {
                let mut regs = vec![0; lifted.program.register_count()];
                regs[x86::RDI] = x;
                regs[x86::RSP] = 4608;
                let run = lifted
                    .program
                    .execute_with_memory(&regs, 4096, &vec![0x91; 512], 10000)
                    .unwrap();
                assert_eq!(run.value, row[i], "{name}/{opt}/{x}");
            }
            if opt == "-O2" {
                programs.push(lifted.program);
            }
        }
    }
    let mut source =
        String::from("#include <stdint.h>\n#include <inttypes.h>\n#include <stdio.h>\n");
    let mut names = Vec::new();
    for (i, p) in programs.iter().enumerate() {
        let out = readable::emit_readable_c(p).unwrap();
        assert_eq!(out.parameters, vec![nirvana::ir::Reg(x86::RDI)]);
        let body = out.code.split("uint64_t nirvana_readable(").nth(1).unwrap();
        assert!(
            body.contains(if cases[i].3 {
                "nirvana_signed32("
            } else if cases[i].2 {
                "nirvana_srem_word("
            } else {
                "nirvana_sdiv_word("
            }),
            "{}: {}",
            cases[i].0,
            out.code
        );
        let prefix = format!("probe_{i}_");
        source.push_str(&out.code.replace("nirvana_", &prefix));
        names.push(format!("{prefix}readable"));
    }
    writeln!(
        source,
        "static uint64_t (*const probes[])(uint64_t)={{{}}};",
        names.join(",")
    )
    .unwrap();
    source.push_str("int main(void) { uint64_t x;while(scanf(\"%\" SCNu64,&x)==1) { for(unsigned i=0;i<sizeof(probes)/sizeof(probes[0]);++i) printf(\"%\" PRIu64 \" \",probes[i](x));putchar('\\n'); }return 0;}\n");
    let file = scratch.0.join("generated.c");
    std::fs::write(&file, source).unwrap();
    for opt in ["-O0", "-O2"] {
        let exe = scratch.0.join(format!("generated{opt}"));
        native::compile_c(
            &file,
            &exe,
            &[
                opt,
                "-fsanitize=undefined",
                "-fno-sanitize-recover=undefined",
            ],
        );
        assert_eq!(native::run_fields(&exe, &input, cases.len()), expected);
    }
    println!(
        "{} native and raw IR word observations; {} sanitized generated C observations",
        4 * expected.len() * cases.len(),
        2 * expected.len() * cases.len()
    );
}

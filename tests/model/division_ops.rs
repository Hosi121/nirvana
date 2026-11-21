use crate::support::ir::{c, division_value, r};
use crate::support::native;
use nirvana::ir::{BinaryOp as B, Control, Expr, IrInstruction, Program};
use std::fmt::Write as _;
const OPS: [B; 4] = [B::UDiv, B::URem, B::SDiv, B::SRem];
fn program(e: Expr) -> Program {
    Program::new(
        0,
        2,
        vec![IrInstruction {
            address: 0,
            size: 1,
            assignments: vec![],
            control: Control::Return(e),
        }],
    )
    .unwrap()
}
fn values() -> Vec<u64> {
    let mut result = vec![
        0,
        1,
        2,
        3,
        7,
        10,
        31,
        63,
        64,
        65,
        255,
        256,
        0x7fff_ffff,
        0x8000_0000,
        0xffff_ffff,
        1 << 32,
        (1 << 63) - 1,
        1 << 63,
        (1 << 63) + 1,
        u64::MAX - 1,
        u64::MAX,
    ];
    let mut seed = 0x8129_abcf_cdc8_4351;
    for _ in 0..96 {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        result.push(seed);
    }
    result
}

#[test]
fn total_division_bits_match_long_division_ir_and_constant_folding() {
    let values = values();
    let mut count = 0;
    for op in OPS {
        let p = program(Expr::binary(op, r(0), r(1)));
        for &a in &values {
            for &b in &values {
                let expected = division_value(op, a, b);
                assert_eq!(op.evaluate(a, b), expected, "{op:?}/{a}/{b}");
                assert_eq!(p.execute(&[a, b], 1).unwrap().value, expected);
                assert_eq!(
                    nirvana::simplify::simplify(&Expr::binary(op, c(a), c(b))),
                    c(expected)
                );
                count += 1;
            }
        }
    }
    assert_eq!(B::SDiv.evaluate(1 << 63, u64::MAX), 1 << 63);
    assert_eq!(B::SRem.evaluate(1 << 63, u64::MAX), 0);
    assert_eq!(B::SDiv.evaluate(0, 0), u64::MAX);
    assert_eq!(B::SDiv.evaluate(1 << 63, 0), 1);
    println!("{count} restoring-division/IR/folding comparisons including zero and overflow");
}

#[test]
#[cfg(target_arch = "x86_64")]
fn nonfaulting_div_idiv_agree_with_total_ir_on_their_hardware_domain() {
    use std::arch::asm;
    let values = values();
    let mut count = 0;
    for &a in &values {
        for &b in &values {
            if b == 0 {
                continue;
            }
            let q: u64;
            let rem: u64;
            unsafe {
                asm!("xor edx,edx","div {divisor}",divisor=in(reg)b,inout("rax")a=>q,out("rdx")rem,options(nostack));
            }
            assert_eq!((B::UDiv.evaluate(a, b), B::URem.evaluate(a, b)), (q, rem));
            count += 2;
            if a == 1 << 63 && b == u64::MAX {
                continue;
            }
            let q: u64;
            let rem: u64;
            unsafe {
                asm!("cqo","idiv {divisor}",divisor=in(reg)b,inout("rax")a=>q,out("rdx")rem,options(nostack));
            }
            assert_eq!((B::SDiv.evaluate(a, b), B::SRem.evaluate(a, b)), (q, rem));
            count += 2;
        }
    }
    println!("{count} native DIV/IDIV quotient and remainder comparisons");
}

#[test]
fn raw_ssa_and_readable_division_helpers_preserve_total_bits_under_ubsan() {
    let scratch = native::Scratch::new();
    let mut code = String::from("#include <stdint.h>\n#include <inttypes.h>\n#include <stdio.h>\n");
    let mut names = Vec::new();
    let cases: Vec<_> = OPS
        .into_iter()
        .flat_map(|op| {
            [None, Some(0), Some(1), Some(1 << 63), Some(u64::MAX)].map(move |d| (op, d))
        })
        .collect();
    for &(op, divisor) in &cases {
        let p = program(Expr::binary(op, r(0), divisor.map_or_else(|| r(1), c)));
        let graph = nirvana::ssa::SsaFunction::build(&p).unwrap();
        let lowered = nirvana::ssa_destroy::lower(&p, &graph, &Default::default()).unwrap();
        let readable = nirvana::readable::emit_readable_c(&p).unwrap();
        let args = readable
            .parameters
            .iter()
            .map(|reg| match reg.0 {
                0 => "a",
                1 => "b",
                _ => panic!("unexpected parameter"),
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
            ("readable", readable.code, 2),
        ] {
            let index = names.len();
            let name = format!("probe{index}");
            let prefix = format!("nv{index}_");
            code.push_str(&text.replace("nirvana_", &prefix));
            if mode == "readable" {
                writeln!(
                    code,
                    "uint64_t {name}(uint64_t a,uint64_t b) {{(void)a;(void)b;return {prefix}readable({args});}}"
                )
                .unwrap();
            } else {
                writeln!(code,"uint64_t {name}(uint64_t a,uint64_t b) {{uint64_t r[{count}]={{0}};r[0]=a;r[1]=b;return {prefix}fn(r);}}").unwrap();
            }
            names.push(name);
        }
    }
    code.push_str(
        "int main(void) {uint64_t a,b;while(scanf(\"%\" SCNu64 \" %\" SCNu64,&a,&b)==2) {\n",
    );
    for name in &names {
        writeln!(code, "printf(\"%\" PRIu64 \" \",{name}(a,b));").unwrap();
    }
    code.push_str("putchar('\\n');}return 0;}\n");
    let mut text = String::new();
    let mut expected = Vec::new();
    for a in values() {
        for b in values() {
            writeln!(text, "{a} {b}").unwrap();
            expected.push(
                cases
                    .iter()
                    .flat_map(|&(op, d)| [division_value(op, a, d.unwrap_or(b)); 3])
                    .collect::<Vec<_>>(),
            );
        }
    }
    let source = scratch.0.join("division.c");
    std::fs::write(&source, code).unwrap();
    for opt in ["-O0", "-O2"] {
        let executable = scratch.0.join(opt);
        native::compile_c(
            &source,
            &executable,
            &[
                opt,
                "-fsanitize=undefined",
                "-fno-sanitize-recover=undefined",
            ],
        );
        assert_eq!(
            native::run_fields(&executable, &text, names.len()),
            expected
        );
    }
    println!(
        "{} sanitized raw/SSA/readable C division observations",
        2 * expected.len() * names.len()
    );
}

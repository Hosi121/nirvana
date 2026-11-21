#[path = "../../../tests/support/native.rs"]
#[allow(dead_code)]
mod native;

use super::*;
use crate::model::ir::{Control, IrInstruction, Program};
use std::fmt::Write;
use std::process::Command;

const OPS: [B; 15] = [
    B::Add,
    B::Sub,
    B::Mul,
    B::And,
    B::Or,
    B::Xor,
    B::Shl,
    B::Shr,
    B::Eq,
    B::Ne,
    B::Ult,
    B::Ule,
    B::UMulHigh,
    B::SMulHigh,
    B::AShr,
];

fn r(id: usize) -> Expr {
    Expr::Register(Reg(id))
}
fn b(op: B, a: Expr, z: Expr) -> Expr {
    Expr::binary(op, a, z)
}
fn printed(e: &Expr) -> String {
    expression(e, |r| format!("r[{}]", r.0))
}

#[test]
fn formatting_keeps_required_grouping_and_promotes_comparisons() {
    assert_eq!(
        printed(&b(B::Add, r(0), b(B::Mul, r(1), r(2)))),
        "r[0] + r[1] * r[2]"
    );
    assert_eq!(
        printed(&b(B::Sub, r(0), b(B::Sub, r(1), r(2)))),
        "r[0] - (r[1] - r[2])"
    );
    assert_eq!(printed(&b(B::Shl, r(0), Expr::Const(65))), "r[0] << 1");
    assert_eq!(
        printed(&b(B::Shr, r(0), r(1))),
        "r[0] >> (r[1] & UINT64_C(63))"
    );
    assert_eq!(printed(&b(B::Eq, r(0), r(1))), "((uint64_t)(r[0] == r[1]))");
}

fn next(seed: &mut u64) -> u64 {
    *seed = seed
        .wrapping_mul(6364136223846793005)
        .wrapping_add(1442695040888963407);
    *seed
}

fn tree(seed: &mut u64, depth: usize) -> Expr {
    if depth == 0 {
        return if next(seed) & 1 == 0 {
            r((next(seed) % 4) as usize)
        } else {
            Expr::Const(next(seed))
        };
    }
    if next(seed).is_multiple_of(5) {
        Expr::select(
            tree(seed, depth - 1),
            tree(seed, depth - 1),
            tree(seed, depth - 1),
        )
    } else {
        b(
            OPS[(next(seed) % 13) as usize],
            tree(seed, depth - 1),
            tree(seed, depth - 1),
        )
    }
}

#[test]
fn compiled_compact_expressions_match_ir_at_unsigned_boundaries() {
    let mut cases = Vec::new();
    for outer in OPS {
        for inner in OPS {
            cases.push(b(outer, b(inner, r(0), r(1)), r(2)));
            cases.push(b(outer, r(0), b(inner, r(1), r(2))));
        }
    }
    for count in [0, 1, 31, 32, 63, 64, 65, 127, u64::MAX] {
        cases.push(b(
            B::Shl,
            b(B::Sub, b(B::Eq, r(0), r(1)), b(B::Eq, r(2), r(3))),
            Expr::Const(count),
        ));
        cases.push(b(B::Shr, r(0), Expr::Const(count)));
    }
    let mut seed = 0x2e71bace785dc317;
    for _ in 0..64 {
        cases.push(tree(&mut seed, 4));
    }
    cases.push(Expr::select(
        Expr::select(r(0), r(1), r(2)),
        Expr::select(r(1), r(2), r(3)),
        Expr::select(r(2), r(3), r(0)),
    ));
    let boundary = [
        0,
        1,
        2,
        31,
        32,
        63,
        64,
        65,
        127,
        255,
        u32::MAX as u64,
        1 << 32,
        (1 << 63) - 1,
        1 << 63,
        u64::MAX - 1,
        u64::MAX,
    ];
    let mut inputs = Vec::new();
    for (i, &value) in boundary.iter().enumerate() {
        inputs.push([
            value,
            boundary[(i * 7 + 3) % boundary.len()],
            boundary[(i + 1) % boundary.len()],
            boundary[(i * 3) % boundary.len()],
        ]);
    }
    for _ in 0..32 {
        inputs.push(std::array::from_fn(|_| next(&mut seed)));
    }
    let programs: Vec<_> = cases
        .iter()
        .map(|e| {
            Program::new(
                0,
                4,
                vec![IrInstruction {
                    address: 0,
                    size: 1,
                    assignments: vec![],
                    control: Control::Return(e.clone()),
                }],
            )
            .unwrap()
        })
        .collect();
    let expected: Vec<Vec<_>> = inputs
        .iter()
        .map(|input| {
            programs
                .iter()
                .map(|p| p.execute_with_memory(input, 0, &[], 1).unwrap().value)
                .collect()
        })
        .collect();
    let mut source =
        String::from("#include <stdint.h>\n#include <inttypes.h>\n#include <stdio.h>\n");
    let bodies: Vec<_> = cases.iter().map(printed).collect();
    source.push_str(&crate::codegen::emit::integer::selected_helpers(
        &bodies.join("\n"),
    ));
    for (i, body) in bodies.iter().enumerate() {
        writeln!(
            source,
            "static uint64_t probe_{i}(const uint64_t *r) {{ (void)r; return {}; }}",
            body
        )
        .unwrap();
    }
    source.push_str("int main(void) { uint64_t r[4]; while(scanf(\"%\" SCNu64 \" %\" SCNu64 \" %\" SCNu64 \" %\" SCNu64,&r[0],&r[1],&r[2],&r[3])==4) {\n");
    for i in 0..cases.len() {
        writeln!(source, "printf(\"%\" PRIu64 \" \",probe_{i}(r));").unwrap();
    }
    source.push_str("putchar('\\n'); } }\n");
    let input = inputs
        .iter()
        .map(|r| format!("{} {} {} {}\n", r[0], r[1], r[2], r[3]))
        .collect::<String>();
    let scratch = native::Scratch::new();
    let file = scratch.0.join("compact.c");
    std::fs::write(&file, source).unwrap();
    for optimization in ["-O0", "-O2"] {
        let binary = scratch.0.join(format!("compact{optimization}"));
        let result = Command::new("cc")
            .args([
                "-std=c11",
                "-Wall",
                "-Wextra",
                "-Werror",
                "-pedantic",
                optimization,
            ])
            // Generated arithmetic trees intentionally include tautologies and
            // comparisons of booleans with large constants. Their numerical
            // behavior is tested here; ordinary backend cohorts keep -Werror.
            .args([
                "-Wno-error=tautological-compare",
                "-Wno-error=bool-compare",
                "-Wno-error=type-limits",
            ])
            .arg("-fsanitize=undefined")
            .arg("-fno-sanitize-recover=undefined")
            .arg(&file)
            .arg("-o")
            .arg(&binary)
            .output()
            .unwrap();
        assert!(
            result.status.success(),
            "{}",
            String::from_utf8_lossy(&result.stderr)
        );
        assert_eq!(
            native::run_fields(&binary, &input, cases.len()),
            expected,
            "{optimization}"
        );
    }
    eprintln!(
        "{} compact C expressions x {} boundary/seed inputs x 2 optimizations = {} IR comparisons with UBSan",
        cases.len(),
        inputs.len(),
        cases.len() * inputs.len() * 2
    );
}

use nirvana::ir;
#[path = "../src/bit_expr.rs"]
mod bit_expr;
#[allow(dead_code)]
#[path = "support/native.rs"]
mod native;

use bit_expr::{BitKind, recognize};
use ir::{BinaryOp, Control, Expr, IrInstruction, Program, Reg, Width};
use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::process::Command;

fn r(id: usize) -> Expr {
    Expr::Register(Reg(id))
}
fn c(value: u64) -> Expr {
    Expr::Const(value)
}
fn b(op: BinaryOp, a: Expr, z: Expr) -> Expr {
    Expr::binary(op, a, z)
}
fn and(value: Expr, mask: u64) -> Expr {
    b(BinaryOp::And, value, c(mask))
}
fn rotate(value: Expr, count: Expr, left: bool) -> Expr {
    let complement = and(b(BinaryOp::Sub, c(0), count.clone()), 63);
    let (a, z) = if left {
        (BinaryOp::Shl, BinaryOp::Shr)
    } else {
        (BinaryOp::Shr, BinaryOp::Shl)
    };
    b(
        BinaryOp::Or,
        b(a, value.clone(), count),
        b(z, value, complement),
    )
}
fn stage(value: Expr, shift: u64, mask: u64, bare_right: bool, truncate_input: bool) -> Expr {
    let left = b(BinaryOp::Shl, and(value.clone(), mask), c(shift));
    let right = b(
        BinaryOp::Shr,
        if truncate_input {
            and(value, 0xffff_ffff)
        } else {
            value
        },
        c(shift),
    );
    b(
        BinaryOp::Or,
        left,
        if bare_right { right } else { and(right, mask) },
    )
}
fn swap(value: Expr, wide: bool, truncate_input: bool) -> Expr {
    let value = stage(
        value,
        8,
        if wide {
            0x00ff_00ff_00ff_00ff
        } else {
            0x00ff_00ff
        },
        false,
        truncate_input,
    );
    let value = stage(
        value,
        16,
        if wide { 0x0000_ffff_0000_ffff } else { 0xffff },
        !wide,
        false,
    );
    if wide {
        stage(value, 32, 0xffff_ffff, true, false)
    } else {
        value
    }
}
fn evaluate(expression: Expr, input: &[u64]) -> u64 {
    Program::new(
        0,
        input.len(),
        vec![IrInstruction {
            address: 0,
            size: 1,
            assignments: vec![],
            control: Control::Return(expression),
        }],
    )
    .unwrap()
    .execute(input, 1)
    .unwrap()
    .value
}
fn oracle(kind: BitKind, value: u64, count: u64) -> u64 {
    match kind {
        BitKind::Rol64 => value.rotate_left((count & 63) as u32),
        BitKind::Ror64 => value.rotate_right((count & 63) as u32),
        BitKind::Bswap32 => u64::from((value as u32).swap_bytes()),
        BitKind::Bswap64 => value.swap_bytes(),
    }
}
const VALUES: [u64; 10] = [
    0,
    1,
    127,
    255,
    65535,
    0xffff_ffff,
    1 << 31,
    1 << 63,
    0x0123_4567_89ab_cdef,
    u64::MAX,
];
const COUNTS: [u64; 6] = [0, 1, 63, 64, 127, u64::MAX];

#[test]
fn exact_pure_patterns_match_independent_rust_oracles_at_wrapping_boundaries() {
    let patterns = [
        (BitKind::Rol64, rotate(r(0), r(1), true)),
        (BitKind::Ror64, rotate(r(0), and(r(1), 63), false)),
        (
            BitKind::Rol64,
            b(
                BinaryOp::Or,
                b(BinaryOp::Shl, r(0), r(1)),
                b(BinaryOp::Shr, r(0), b(BinaryOp::Sub, c(0), and(r(1), 63))),
            ),
        ),
        (BitKind::Bswap32, swap(r(0), false, false)),
        (BitKind::Bswap32, swap(r(0), false, true)),
        (BitKind::Bswap64, swap(r(0), true, false)),
    ];
    for (kind, expression) in patterns {
        let before = expression.clone();
        let view = recognize(&expression).unwrap();
        assert_eq!(view.kind, kind);
        assert_eq!(view.value, &r(0));
        assert_eq!(
            view.count.is_some(),
            matches!(kind, BitKind::Rol64 | BitKind::Ror64)
        );
        for value in VALUES {
            for count in COUNTS {
                let data = evaluate(view.value.clone(), &[value, count]);
                let shift = view.count.map_or(0, |count_expr| {
                    evaluate(count_expr.clone(), &[value, count])
                });
                assert_eq!(
                    evaluate(expression.clone(), &[value, count]),
                    oracle(kind, data, shift)
                );
            }
        }
        assert_eq!(expression, before);
    }
    for count in COUNTS {
        let expression = b(
            BinaryOp::Or,
            b(BinaryOp::Shl, r(0), c(count)),
            b(BinaryOp::Shr, r(0), c(count.wrapping_neg() & 63)),
        );
        let view = recognize(&expression).unwrap();
        for value in VALUES {
            assert_eq!(
                evaluate(expression.clone(), &[value]),
                oracle(view.kind, value, count)
            );
        }
    }
}

#[test]
fn common_values_require_identical_raw_subtrees_and_views_borrow_original_operands() {
    let expression = rotate(b(BinaryOp::Add, r(0), c(0)), r(1), true);
    let Expr::Binary(_, first, _) = &expression else {
        unreachable!()
    };
    let Expr::Binary(_, value, count) = &**first else {
        unreachable!()
    };
    let view = recognize(&expression).unwrap();
    assert!(std::ptr::eq(view.value, &**value));
    assert!(std::ptr::eq(view.count.unwrap(), &**count));
    let mismatch = b(
        BinaryOp::Or,
        b(BinaryOp::Shl, b(BinaryOp::Add, r(0), c(0)), r(1)),
        b(BinaryOp::Shr, r(0), and(b(BinaryOp::Sub, c(0), r(1)), 63)),
    );
    assert!(recognize(&mismatch).is_none());
    let complex = Expr::select(r(2), r(0), b(BinaryOp::Xor, r(0), c(7)));
    let expression = swap(complex.clone(), true, false);
    let view = recognize(&expression).unwrap();
    assert_eq!(view.value, &complex);
    for choose in [0, 1] {
        for value in VALUES {
            let input = [value, 0, choose];
            assert_eq!(
                evaluate(expression.clone(), &input),
                evaluate(complex.clone(), &input).swap_bytes()
            );
        }
    }
    assert!(
        recognize(&rotate(r(usize::MAX), c(7), true)).is_some(),
        "no dense register-ID indexing"
    );
}

#[test]
fn loads_even_in_untaken_select_arms_and_wrong_masks_counts_or_narrow_rotates_decline() {
    let load = Expr::load(r(2), Width::U64);
    for expression in [
        rotate(load.clone(), r(1), true),
        rotate(r(0), load.clone(), false),
        swap(load, true, false),
        rotate(
            Expr::select(c(1), r(0), Expr::load(c(u64::MAX), Width::U8)),
            r(1),
            true,
        ),
    ] {
        assert!(recognize(&expression).is_none());
    }
    let wrong_count = b(
        BinaryOp::Or,
        b(BinaryOp::Shl, r(0), c(1)),
        b(BinaryOp::Shr, r(0), c(62)),
    );
    assert!(recognize(&wrong_count).is_none());
    let narrow = b(
        BinaryOp::Or,
        b(BinaryOp::Shl, and(r(0), 0xffff), c(3)),
        b(BinaryOp::Shr, and(r(0), 0xffff), c(13)),
    );
    assert!(
        recognize(&narrow).is_none(),
        "contextual truncation cannot make a whole u64 expression a rotate"
    );
    let wrong = stage(
        stage(
            stage(r(0), 8, 0x00ff_00ff_00ff_00fe, false, false),
            16,
            0x0000_ffff_0000_ffff,
            false,
            false,
        ),
        32,
        0xffff_ffff,
        true,
        false,
    );
    assert!(recognize(&wrong).is_none());
    let wrong = stage(
        stage(r(0), 8, 0x00ff_00ff, true, false),
        16,
        0xffff,
        true,
        false,
    );
    assert!(
        recognize(&wrong).is_none(),
        "first right shift still needs its lane mask"
    );
    assert!(
        recognize(&b(
            BinaryOp::Or,
            b(BinaryOp::Shl, r(0), c(1)),
            b(BinaryOp::Shr, r(2), c(63))
        ))
        .is_none()
    );
}

#[test]
fn depth_and_node_caps_are_checked_over_the_whole_expression_before_matching() {
    let mut value = r(0);
    for _ in 0..=bit_expr::MAX_DEPTH {
        value = b(BinaryOp::Add, value, c(0));
    }
    assert!(recognize(&rotate(value, c(1), true)).is_none());
    fn balanced(leaves: usize) -> Expr {
        if leaves == 1 {
            return c(0);
        }
        b(
            BinaryOp::Add,
            balanced(leaves / 2),
            balanced(leaves - leaves / 2),
        )
    }
    assert!(recognize(&balanced(bit_expr::MAX_NODES)).is_none());
    let malformed = b(
        BinaryOp::Or,
        swap(r(0), true, false),
        balanced(bit_expr::MAX_NODES),
    );
    assert!(recognize(&malformed).is_none());
    const { assert!(bit_expr::MAX_WORK >= bit_expr::MAX_NODES) };
}

#[test]
fn actual_four_fixture_presentations_contain_pure_matchable_operands() {
    let scratch = native::Scratch::new();
    for name in ["rotates", "byte-swap"] {
        for optimization in ["-O0", "-O2"] {
            let object = scratch.0.join(format!("{name}{optimization}.o"));
            native::object(
                &native::fixture_root().join(format!("recovery/{name}.c")),
                &object,
                optimization,
                "fixture",
            );
            let lifted =
                nirvana::frontend::lift_elf(&std::fs::read(object).unwrap(), "fixture").unwrap();
            let reduced = nirvana::reduce::reduce(&lifted.program).unwrap();
            let webs = nirvana::web::split(reduced.program()).unwrap();
            nirvana::web_verify::validate(reduced.program(), webs.program()).unwrap();
            let program = webs.program();
            let widths = nirvana::value_width::ValueWidths::analyze(program);
            let width = |reg| {
                if reduced.parameters().contains(&reg) {
                    Width::U64
                } else {
                    widths.width(reg)
                }
            };
            let mut counts = BTreeMap::new();
            fn visit(value: &Expr, counts: &mut BTreeMap<BitKind, usize>) {
                if let Some(view) = recognize(value) {
                    *counts.entry(view.kind).or_default() += 1;
                    return;
                }
                match value {
                    Expr::Binary(_, a, z) => {
                        visit(a, counts);
                        visit(z, counts);
                    }
                    Expr::Select {
                        condition,
                        taken,
                        not_taken,
                    } => {
                        visit(condition, counts);
                        visit(taken, counts);
                        visit(not_taken, counts);
                    }
                    Expr::Load { .. } | Expr::Register(_) | Expr::Const(_) => {}
                }
            }
            for instruction in program.instructions() {
                for assignment in &instruction.assignments {
                    visit(
                        &nirvana::presentation::normalize(&assignment.value, width),
                        &mut counts,
                    );
                }
            }
            if name == "rotates" {
                assert!(
                    counts.get(&BitKind::Rol64).copied().unwrap_or(0) >= 1,
                    "{optimization}: {counts:?}"
                );
                assert!(
                    counts.get(&BitKind::Ror64).copied().unwrap_or(0) >= 1,
                    "{optimization}: {counts:?}"
                );
            } else {
                assert!(
                    counts.get(&BitKind::Bswap64).copied().unwrap_or(0) >= 2,
                    "{optimization}: {counts:?}"
                );
                assert!(
                    counts.get(&BitKind::Bswap32).copied().unwrap_or(0) >= 2,
                    "{optimization}: {counts:?}"
                );
            }
            println!("{name} {optimization}: {counts:?}");
        }
    }
}

#[test]
fn c_helpers_match_rust_oracles_at_o0_o2_and_ubsan_without_shift_undefined_behavior() {
    let scratch = native::Scratch::new();
    let mut source =
        String::from("#include <stdint.h>\n#include <stdio.h>\n#include <inttypes.h>\n");
    for kind in [
        BitKind::Rol64,
        BitKind::Ror64,
        BitKind::Bswap32,
        BitKind::Bswap64,
    ] {
        source.push_str(kind.c_helper());
        assert!(kind.c_helper().contains(kind.helper_name()));
    }
    source.push_str("int main(void){uint64_t x,n;while(scanf(\"%\" SCNu64 \" %\" SCNu64,&x,&n)==2){printf(\"%\" PRIu64 \" %\" PRIu64 \" %\" PRIu64 \" %\" PRIu64 \"\\n\",nirvana_rol64(x,n),nirvana_ror64(x,n),nirvana_bswap32(x),nirvana_bswap64(x));}}\n");
    let path = scratch.0.join("helpers.c");
    std::fs::write(&path, source).unwrap();
    let mut input = String::new();
    let mut expected = Vec::new();
    for value in VALUES {
        for count in COUNTS {
            writeln!(input, "{value} {count}").unwrap();
            expected.push(vec![
                oracle(BitKind::Rol64, value, count),
                oracle(BitKind::Ror64, value, count),
                oracle(BitKind::Bswap32, value, count),
                oracle(BitKind::Bswap64, value, count),
            ]);
        }
    }
    for optimization in ["-O0", "-O2"] {
        for sanitize in [false, true] {
            let binary = scratch.0.join(format!("helpers{optimization}{sanitize}"));
            let mut command = Command::new("cc");
            command.args([
                "-std=c11",
                "-Wall",
                "-Wextra",
                "-Werror",
                "-pedantic",
                optimization,
            ]);
            if sanitize {
                command.args(["-fsanitize=undefined", "-fno-sanitize-recover=undefined"]);
            }
            let compiled = command.arg(&path).arg("-o").arg(&binary).output().unwrap();
            assert!(
                compiled.status.success(),
                "{}",
                String::from_utf8_lossy(&compiled.stderr)
            );
            assert_eq!(
                native::run_fields(&binary, &input, 4),
                expected,
                "{optimization}, UBSan={sanitize}"
            );
        }
    }
}

use crate::support::native;
use nirvana::ir;
use nirvana::narrow_rotate;

use ir::{BinaryOp as B, Control, Expr, IrInstruction, Program, Width};
use narrow_rotate::{Direction, NarrowRotate, NarrowWidth, recognize_masked};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::process::Command;

use crate::support::ir::c;
use crate::support::ir::r;
fn b(op: B, a: Expr, z: Expr) -> Expr {
    Expr::binary(op, a, z)
}
fn and(a: Expr, mask: u64) -> Expr {
    b(B::And, a, c(mask))
}
fn core(value: Expr, width: NarrowWidth, direction: Direction, count: Expr, other: Expr) -> Expr {
    let (primary, secondary) = match direction {
        Direction::Left => (B::Shl, B::Shr),
        Direction::Right => (B::Shr, B::Shl),
    };
    b(
        B::Or,
        b(primary, and(value.clone(), width.mask()), count),
        b(secondary, and(value, width.mask()), other),
    )
}
fn pattern(value: Expr, width: NarrowWidth, direction: Direction, count: Expr) -> Expr {
    let other = match &count {
        Expr::Const(n) => c(u64::from(width.bits()) - n),
        _ => and(b(B::Sub, c(0), count.clone()), u64::from(width.bits() - 1)),
    };
    and(core(value, width, direction, count, other), width.mask())
}
fn partial(value: Expr, width: NarrowWidth, direction: Direction, count: Expr) -> Expr {
    and(
        b(
            B::Or,
            and(value.clone(), !width.mask()),
            pattern(value, width, direction, count),
        ),
        width.mask(),
    )
}
fn eval(expression: &Expr, input: &[u64]) -> u64 {
    Program::new(
        0,
        input.len(),
        vec![IrInstruction {
            address: 0,
            size: 1,
            assignments: vec![],
            control: Control::Return(expression.clone()),
        }],
    )
    .unwrap()
    .execute(input, 1)
    .unwrap()
    .value
}
fn oracle(width: NarrowWidth, direction: Direction, value: u64, count: u64) -> u64 {
    let count = (count & u64::from(width.bits() - 1)) as u32;
    match (width, direction) {
        (NarrowWidth::U8, Direction::Left) => u64::from((value as u8).rotate_left(count)),
        (NarrowWidth::U8, Direction::Right) => u64::from((value as u8).rotate_right(count)),
        (NarrowWidth::U16, Direction::Left) => u64::from((value as u16).rotate_left(count)),
        (NarrowWidth::U16, Direction::Right) => u64::from((value as u16).rotate_right(count)),
        (NarrowWidth::U32, Direction::Left) => u64::from((value as u32).rotate_left(count)),
        (NarrowWidth::U32, Direction::Right) => u64::from((value as u32).rotate_right(count)),
    }
}
const WIDTHS: [NarrowWidth; 3] = [NarrowWidth::U8, NarrowWidth::U16, NarrowWidth::U32];
const DIRECTIONS: [Direction; 2] = [Direction::Left, Direction::Right];
const VALUES: [u64; 10] = [
    0,
    1,
    0x80,
    0xff,
    0x8000,
    0xffff,
    0x8000_0000,
    1 << 63,
    0x0123_4567_89ab_cdef,
    u64::MAX,
];
const COUNTS: [u64; 9] = [0, 1, 7, 15, 31, 63, 64, 127, u64::MAX];

#[test]
fn whole_u64_values_match_independent_narrow_rust_rotates_without_width_assumptions() {
    let mut checks = 0;
    for width in WIDTHS {
        for direction in DIRECTIONS {
            for count in [
                c(0),
                c(1),
                c(u64::from(width.bits() - 1)),
                and(r(1), u64::from(width.bits() - 1)),
            ] {
                for expression in [
                    pattern(r(0), width, direction, count.clone()),
                    partial(r(0), width, direction, count.clone()),
                ] {
                    let original = expression.clone();
                    let view = recognize_masked(&expression).unwrap();
                    assert_eq!((view.width, view.direction), (width, direction));
                    for value in VALUES {
                        for n in COUNTS {
                            let input = [value, n];
                            assert_eq!(
                                eval(&expression, &input),
                                oracle(
                                    width,
                                    direction,
                                    eval(view.value, &input),
                                    eval(view.count, &input)
                                ),
                                "{width:?} {direction:?} x={value} n={n}"
                            );
                            checks += 1;
                        }
                    }
                    assert_eq!(expression, original);
                }
            }
        }
    }
    println!("{checks} complete-u64 IR/Rust comparisons");
}

#[test]
fn exact_raw_values_are_borrowed_and_pure_dependencies_are_retained() {
    fn registers(e: &Expr, into: &mut BTreeSet<usize>) {
        match e {
            Expr::Unary(_, value) => registers(value, into),
            Expr::Register(r) => {
                into.insert(r.0);
            }
            Expr::Binary(_, a, b) => {
                registers(a, into);
                registers(b, into);
            }
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => {
                registers(condition, into);
                registers(taken, into);
                registers(not_taken, into);
            }
            Expr::Const(_) => {}
            Expr::Load { .. } => panic!("pure test"),
        }
    }
    let value = Expr::select(r(2), b(B::Add, r(0), c(0)), b(B::Xor, r(0), c(7)));
    let width = NarrowWidth::U16;
    let expression = partial(value.clone(), width, Direction::Right, and(r(1), 15));
    let view = recognize_masked(&expression).unwrap();
    assert_eq!(view.value, &value);
    // Inspect the original low branch: returned operands are borrowed subtrees.
    let Expr::Binary(_, body, _) = &expression else {
        panic!()
    };
    let Expr::Binary(_, _, low) = &**body else {
        panic!()
    };
    let Expr::Binary(_, shifts, _) = &**low else {
        panic!()
    };
    let Expr::Binary(_, first, _) = &**shifts else {
        panic!()
    };
    let Expr::Binary(_, masked_value, count) = &**first else {
        panic!()
    };
    let Expr::Binary(_, base, _) = &**masked_value else {
        panic!()
    };
    assert!(std::ptr::eq(view.value, &**base));
    assert!(std::ptr::eq(view.count, &**count));
    let mut before = BTreeSet::new();
    let mut after = BTreeSet::new();
    registers(&expression, &mut before);
    registers(view.value, &mut after);
    registers(view.count, &mut after);
    assert_eq!(before, after);
    for choose in [0, 2, u64::MAX] {
        for value in VALUES {
            let input = [value, u64::MAX, choose];
            assert_eq!(
                eval(&expression, &input),
                oracle(
                    width,
                    view.direction,
                    eval(view.value, &input),
                    eval(view.count, &input)
                )
            );
        }
    }
    assert!(
        recognize_masked(&pattern(
            r(usize::MAX),
            NarrowWidth::U8,
            Direction::Left,
            c(1)
        ))
        .is_some()
    );
}

#[test]
fn exact_complement_wrappers_and_commuted_masks_are_supported() {
    for width in WIDTHS {
        let mask = u64::from(width.bits() - 1);
        let count = and(r(1), mask);
        for complement in [
            and(b(B::Sub, c(0), r(1)), mask),
            and(b(B::Sub, c(u64::from(width.bits())), count.clone()), mask),
            b(B::Sub, c(u64::from(width.bits())), count.clone()),
        ] {
            let expression = b(
                B::And,
                c(width.mask()),
                core(r(0), width, Direction::Left, count.clone(), complement),
            );
            let view = recognize_masked(&expression).unwrap();
            for value in VALUES {
                for n in COUNTS {
                    assert_eq!(
                        eval(&expression, &[value, n]),
                        oracle(width, view.direction, value, n)
                    );
                }
            }
        }
        let zero = and(core(r(0), width, Direction::Left, c(0), c(0)), width.mask());
        assert!(recognize_masked(&zero).is_some());
    }
}

#[test]
fn missing_masks_wrong_values_counts_and_any_load_decline() {
    let width = NarrowWidth::U16;
    let valid = pattern(r(0), width, Direction::Left, c(3));
    let Expr::Binary(_, body, _) = &valid else {
        panic!()
    };
    let bad = [
        (**body).clone(),
        and((**body).clone(), 0xff),
        and(
            b(B::Or, b(B::Shl, r(0), c(3)), b(B::Shr, r(0), c(13))),
            width.mask(),
        ),
        and(
            b(
                B::Or,
                b(B::Shl, and(r(0), width.mask()), c(3)),
                b(B::Shr, and(r(2), width.mask()), c(13)),
            ),
            width.mask(),
        ),
        and(
            core(
                r(0),
                width,
                Direction::Left,
                r(1),
                and(b(B::Sub, c(0), r(1)), 15),
            ),
            width.mask(),
        ),
        and(
            core(
                r(0),
                width,
                Direction::Left,
                and(r(1), 31),
                and(b(B::Sub, c(0), r(1)), 15),
            ),
            width.mask(),
        ),
        and(
            core(r(0), width, Direction::Left, c(64), c(16)),
            width.mask(),
        ),
        and(
            core(r(0), width, Direction::Left, c(3), c(12)),
            width.mask(),
        ),
        and(b(B::Or, and(r(2), !width.mask()), valid), width.mask()),
        pattern(Expr::load(r(2), Width::U16), width, Direction::Left, c(3)),
        pattern(
            r(0),
            width,
            Direction::Left,
            and(Expr::load(r(2), Width::U8), 15),
        ),
        pattern(
            Expr::select(c(1), r(0), Expr::load(c(u64::MAX), Width::U8)),
            width,
            Direction::Left,
            c(3),
        ),
        and(
            b(
                B::Or,
                and(Expr::load(r(2), Width::U64), !width.mask()),
                pattern(r(0), width, Direction::Left, c(3)),
            ),
            width.mask(),
        ),
    ];
    for expression in bad {
        assert!(recognize_masked(&expression).is_none(), "{expression:?}");
    }
    // A C uint32_t destination cannot justify a missing explicit input mask.
    let o0_word = and(
        b(B::Or, b(B::Shl, r(0), c(5)), b(B::Shr, r(0), c(27))),
        0xffff_ffff,
    );
    assert!(recognize_masked(&o0_word).is_none());
    assert_ne!(
        eval(&o0_word, &[1 << 32]),
        oracle(NarrowWidth::U32, Direction::Left, 1 << 32, 5)
    );
}

#[test]
fn whole_tree_depth_node_and_work_caps_precede_matching() {
    let mut deep = r(0);
    for _ in 0..=narrow_rotate::MAX_DEPTH {
        deep = b(B::Add, deep, c(0));
    }
    assert!(recognize_masked(&pattern(deep, NarrowWidth::U8, Direction::Left, c(1))).is_none());
    fn balanced(n: usize) -> Expr {
        if n == 1 {
            return r(0);
        }
        b(B::Add, balanced(n / 2), balanced(n - n / 2))
    }
    let wide = balanced(narrow_rotate::MAX_NODES);
    assert!(recognize_masked(&pattern(wide, NarrowWidth::U8, Direction::Left, c(1))).is_none());
    const { assert!(narrow_rotate::MAX_WORK >= narrow_rotate::MAX_NODES) };
}

fn actual_patterns(optimization: &str) -> Vec<Expr> {
    let scratch = native::Scratch::new();
    let object = scratch.0.join("rotates.o");
    native::object(
        &native::fixture_root().join("recovery/rotates.c"),
        &object,
        optimization,
        "fixture",
    );
    let lifted = nirvana::frontend::lift_elf(&std::fs::read(object).unwrap(), "fixture").unwrap();
    let reduced = nirvana::reduce::reduce(&lifted.program).unwrap();
    let webs = nirvana::web::split(reduced.program()).unwrap();
    nirvana::web_verify::validate(reduced.program(), webs.program()).unwrap();
    let widths = nirvana::value_width::ValueWidths::analyze(webs.program());
    webs.program()
        .instructions()
        .iter()
        .flat_map(|i| &i.assignments)
        .map(|a| {
            nirvana::presentation::normalize(&a.value, |reg| {
                if reduced.parameters().contains(&reg) {
                    Width::U64
                } else {
                    widths.width(reg)
                }
            })
        })
        .filter(|e| recognize_masked(e).is_some())
        .collect()
}

#[test]
fn actual_o2_three_normalized_assignment_expressions_match_and_o0_declines() {
    let expressions = actual_patterns("-O2");
    let mut counts = BTreeMap::new();
    for expression in &expressions {
        let view = recognize_masked(expression).unwrap();
        *counts.entry((view.width, view.direction)).or_insert(0) += 1;
        assert!(matches!(view.value, Expr::Register(_)));
    }
    assert_eq!(
        counts,
        BTreeMap::from([
            ((NarrowWidth::U8, Direction::Right), 1),
            ((NarrowWidth::U16, Direction::Left), 1),
            ((NarrowWidth::U32, Direction::Left), 1),
        ])
    );
    assert!(actual_patterns("-O0").is_empty());
    println!(
        "rotates O2 normalized assignments: {counts:?}; O0: none (no inferred input-width/equality facts)"
    );
}

#[test]
fn uint64_c_helpers_match_rust_at_o0_o2_and_ubsan_with_zero_and_large_counts() {
    let scratch = native::Scratch::new();
    let mut source =
        String::from("#include <stdint.h>\n#include <stdio.h>\n#include <inttypes.h>\n");
    for width in WIDTHS {
        for direction in DIRECTIONS {
            let e = pattern(r(0), width, direction, c(0));
            let view = recognize_masked(&e).unwrap();
            source.push_str(view.c_helper());
            assert!(view.c_helper().contains(view.helper_name()));
        }
    }
    source.push_str("int main(void){uint64_t x,n;while(scanf(\"%\" SCNu64 \" %\" SCNu64,&x,&n)==2){printf(\"%\" PRIu64 \" %\" PRIu64 \" %\" PRIu64 \" %\" PRIu64 \" %\" PRIu64 \" %\" PRIu64 \"\\n\",nirvana_rol8(x,n),nirvana_ror8(x,n),nirvana_rol16(x,n),nirvana_ror16(x,n),nirvana_rol32(x,n),nirvana_ror32(x,n));}}\n");
    let path = scratch.0.join("helpers.c");
    std::fs::write(&path, source).unwrap();
    let mut input = String::new();
    let mut expected = Vec::new();
    for value in VALUES {
        for count in COUNTS {
            writeln!(input, "{value} {count}").unwrap();
            expected.push(
                WIDTHS
                    .into_iter()
                    .flat_map(|w| {
                        DIRECTIONS
                            .into_iter()
                            .map(move |d| oracle(w, d, value, count))
                    })
                    .collect::<Vec<_>>(),
            );
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
            let compiled = native::compile_output(command.arg(&path).arg("-o").arg(&binary));
            assert!(
                compiled.status.success(),
                "{}",
                String::from_utf8_lossy(&compiled.stderr)
            );
            assert_eq!(
                native::run_fields(&binary, &input, 6),
                expected,
                "{optimization}, UBSan={sanitize}"
            );
        }
    }
}

// Fragment proof only: no claim about presentation normalization, CFG, memory,
// or C compilation. Unknown/timeout is a failure, never a passing proof.
fn canonical(view: NarrowRotate<'_>) -> Expr {
    let value = and(view.value.clone(), view.width.mask());
    let count = and(view.count.clone(), u64::from(view.width.bits() - 1));
    let other = b(B::Sub, c(u64::from(view.width.bits())), count.clone());
    let (a, z) = match view.direction {
        Direction::Left => (B::Shl, B::Shr),
        Direction::Right => (B::Shr, B::Shl),
    };
    Expr::select(
        b(B::Eq, count.clone(), c(0)),
        value.clone(),
        and(
            b(B::Or, b(a, value.clone(), count), b(z, value, other)),
            view.width.mask(),
        ),
    )
}

#[test]
#[ignore = "requires NIRVANA_Z3, pinned optional solver; strict pure-u64-v1 obligations"]
fn z3_checks_whole_u64_zero_guarded_width_masked_models_and_replays_broken_variants() {
    use nirvana::verify::{Solver, Verdict};
    let solver = Solver::new(std::env::var_os("NIRVANA_Z3").expect("set NIRVANA_Z3"));
    let mut equivalent = 0;
    for width in WIDTHS {
        for direction in DIRECTIONS {
            let count = and(r(1), u64::from(width.bits() - 1));
            for expression in [
                pattern(r(0), width, direction, count.clone()),
                partial(r(0), width, direction, count),
            ] {
                let view = recognize_masked(&expression).unwrap();
                assert_eq!(
                    solver.check(&expression, &canonical(view)),
                    Verdict::EquivalentUnderModel
                );
                equivalent += 1;
            }
        }
    }
    for expression in actual_patterns("-O2") {
        assert_eq!(
            solver.check(
                &expression,
                &canonical(recognize_masked(&expression).unwrap())
            ),
            Verdict::EquivalentUnderModel
        );
        equivalent += 1;
    }
    let good = pattern(r(0), NarrowWidth::U16, Direction::Left, and(r(1), 15));
    let model = canonical(recognize_masked(&good).unwrap());
    let missing_input = and(
        b(
            B::Or,
            b(B::Shl, r(0), and(r(1), 15)),
            b(B::Shr, r(0), and(b(B::Sub, c(0), r(1)), 15)),
        ),
        0xffff,
    );
    let unmasked_count = and(
        core(
            r(0),
            NarrowWidth::U16,
            Direction::Left,
            r(1),
            and(b(B::Sub, c(0), r(1)), 15),
        ),
        0xffff,
    );
    for broken in [missing_input, unmasked_count] {
        assert!(matches!(
            solver.check(&broken, &model),
            Verdict::Counterexample(_)
        ));
    }
    assert_eq!(equivalent, 15);
    println!(
        "{equivalent} strict whole-u64 equalities, 2 SAT broken variants replayed by existing Solver; no CFG/memory/C proof"
    );
}

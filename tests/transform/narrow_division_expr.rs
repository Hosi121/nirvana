use crate::support::native;
use nirvana::{ir, narrow_division_expr};

use ir::{BinaryOp as B, Control, Expr, IrInstruction, Program, Reg, Width};
use narrow_division_expr::{NarrowDivisionEvidence, NarrowDivisionView, recognize, validate};
use std::collections::BTreeSet;
use std::fmt::Write as _;
use std::process::Command;

#[derive(Clone, Copy)]
struct Case {
    mask: u64,
    m: u64,
    s: u64,
    d: u64,
}
const CASES: [Case; 10] = [
    Case {
        mask: 0xff,
        m: 205,
        s: 11,
        d: 10,
    },
    Case {
        mask: 0xffff,
        m: 52429,
        s: 19,
        d: 10,
    },
    Case {
        mask: 0xffff_ffff,
        m: 0xcccc_cccd,
        s: 35,
        d: 10,
    },
    Case {
        mask: 0x55,
        m: 205,
        s: 11,
        d: 10,
    },
    Case {
        mask: 0xff,
        m: 171,
        s: 9,
        d: 3,
    },
    Case {
        mask: 0xff,
        m: 293,
        s: 11,
        d: 7,
    },
    Case {
        mask: u64::MAX,
        m: 1,
        s: 63,
        d: 1 << 63,
    },
    Case {
        mask: 0,
        m: 1,
        s: 1,
        d: 2,
    },
    Case {
        mask: 0xffff_ffff,
        m: 0xcccc_cccd,
        s: 34,
        d: 5,
    },
    Case {
        mask: 0xffff,
        m: 43691,
        s: 17,
        d: 3,
    },
];
const VALUES: [u64; 19] = [
    0,
    1,
    2,
    7,
    8,
    9,
    10,
    11,
    127,
    128,
    255,
    256,
    65535,
    65536,
    0xffff_ffff,
    0x1_0000_0000,
    1 << 63,
    u64::MAX,
    0x1234_5678_9abc_def0,
];
use crate::support::ir::c;
use crate::support::ir::r;
fn b(op: B, a: Expr, z: Expr) -> Expr {
    Expr::binary(op, a, z)
}
fn and(value: Expr, mask: u64) -> Expr {
    b(B::And, value, c(mask))
}
fn raw(value: Expr, m: u64, s: u64, commute: bool) -> Expr {
    b(
        B::Shr,
        if commute {
            b(B::Mul, c(m), value)
        } else {
            b(B::Mul, value, c(m))
        },
        c(s),
    )
}
fn pattern(case: Case, commute_product: bool, commute_mask: bool) -> Expr {
    raw(
        if commute_mask {
            b(B::And, c(case.mask), r(0))
        } else {
            and(r(0), case.mask)
        },
        case.m,
        case.s,
        commute_product,
    )
}
fn operand(expression: &Expr) -> &Expr {
    let Expr::Binary(B::Shr, product, _) = expression else {
        panic!()
    };
    let Expr::Binary(B::Mul, a, z) = &**product else {
        panic!()
    };
    if matches!(&**a, Expr::Const(_)) { z } else { a }
}
fn evaluate(expression: &Expr, inputs: &[u64]) -> u64 {
    Program::new(
        0,
        inputs.len(),
        vec![IrInstruction {
            address: 0,
            size: 1,
            assignments: vec![],
            control: Control::Return(expression.clone()),
        }],
    )
    .unwrap()
    .execute(inputs, 1)
    .unwrap()
    .value
}
fn dependencies(e: &Expr) -> BTreeSet<usize> {
    let mut set = BTreeSet::new();
    let mut pending = vec![e];
    while let Some(e) = pending.pop() {
        match e {
            Expr::Register(Reg(i)) => {
                set.insert(*i);
            }
            Expr::Unary(_, value) => pending.push(value),
            Expr::Binary(_, a, b) => pending.extend([&**a, &**b]),
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => pending.extend([&**condition, &**taken, &**not_taken]),
            Expr::Load { address, .. } => pending.push(address),
            _ => {}
        }
    }
    set
}

#[test]
fn masks_are_retained_and_whole_u64_inputs_match_ir_and_independent_division() {
    let mut count = 0;
    for case in CASES {
        for commute_product in [false, true] {
            for commute_mask in [false, true] {
                let expression = pattern(case, commute_product, commute_mask);
                let before = expression.clone();
                let view = recognize(&expression).unwrap();
                assert!(validate(&expression, &view));
                assert!(std::ptr::eq(view.value, operand(&expression)));
                assert!(matches!(view.value, Expr::Binary(B::And, ..)));
                assert_eq!(view.divisor, case.d);
                assert_eq!(view.evidence.maximum, case.mask);
                assert_eq!(
                    view.evidence.product_bound,
                    u128::from(case.mask) * u128::from(case.m)
                );
                assert_eq!(dependencies(&expression), dependencies(view.value));
                for value in VALUES.into_iter().chain(0..256) {
                    let expected = (value & case.mask) / case.d;
                    assert_eq!(evaluate(&expression, &[value]), expected);
                    assert_eq!(
                        ((u128::from(value & case.mask) * u128::from(case.m)) >> case.s) as u64,
                        expected
                    );
                    count += 1;
                }
                assert_eq!(expression, before);
            }
        }
    }
    println!("{count} full-u64 source/IR/u128/division comparisons");
}

#[test]
fn complex_total_values_keep_lazy_structure_and_all_register_dependencies() {
    let value = Expr::select(
        r(2),
        b(B::Add, r(0), c(u64::MAX)),
        b(B::UMulHigh, r(0), r(1)),
    );
    let expression = raw(and(value, 0xffff_ffff), 0xcccc_cccd, 35, false);
    let view = recognize(&expression).unwrap();
    assert_eq!(dependencies(view.value), BTreeSet::from([0, 1, 2]));
    assert_eq!(dependencies(&expression), dependencies(view.value));
    for x in VALUES {
        for choose in [0, 1, u64::MAX] {
            let inputs = [x, 0xfedc_ba98_7654_3210, choose];
            assert_eq!(
                evaluate(&expression, &inputs),
                evaluate(view.value, &inputs) / 10
            );
        }
    }
    let sparse = raw(and(r(usize::MAX), 255), 205, 11, false);
    assert!(recognize(&sparse).is_some(), "no dense register-ID domain");
    // Each literal can bound a constant And, while the parser selects the
    // right literal deterministically in both matcher and validator.
    for value in [and(c(15), 255), b(B::And, c(255), c(15))] {
        let expression = raw(value, 205, 11, false);
        assert!(validate(&expression, &recognize(&expression).unwrap()));
    }
}

#[test]
fn overflowing_products_missing_masks_wrapped_shifts_and_bad_error_bounds_decline() {
    for expression in [
        raw(r(0), 0xcccc_cccd, 35, false),
        raw(b(B::And, r(0), r(1)), 0xcccc_cccd, 35, false),
        raw(and(r(0), u64::MAX), 2, 63, false),
        raw(and(r(0), 0x1_ffff_ffff), 0xcccc_cccd, 35, false),
        raw(and(r(0), 15), 3, 3, false),
        raw(and(r(0), 7), 3, 3, false), // error bound equals P: conservatively declined
        raw(and(r(0), 255), 0, 11, false),
        raw(and(r(0), 255), 1, 0, false),
        raw(and(r(0), 255), 1, 64, false),
        raw(and(r(0), 255), 1, 127, false),
        raw(and(r(0), 255), 1, u64::MAX, false),
        b(B::Shr, b(B::UMulHigh, and(r(0), 255), c(205)), c(11)),
        b(B::Shr, b(B::Mul, and(r(0), 255), c(205)), r(1)),
    ] {
        assert!(recognize(&expression).is_none(), "{expression:?}");
    }
    // Omitting the product proof changes an actual low-u64 multiplication.
    let overflow = raw(and(r(0), u64::MAX), 2, 63, false);
    assert_eq!(evaluate(&overflow, &[1 << 63]), 0);
    assert_eq!((1u64 << 63) / (1u64 << 62), 2);
    // Omitting only the quotient error bound is also unsound, even though this
    // small product fits u64: 3*8>>3=3, while 8/3=2.
    let error = raw(and(r(0), 15), 3, 3, false);
    assert_eq!(evaluate(&error, &[8]), 3);
    assert_eq!(8u64 / 3, 2);
    // Dropping the input mask lets high input bits affect the original kernel.
    let no_mask = raw(r(0), 0xcccc_cccd, 35, false);
    assert_ne!(evaluate(&no_mask, &[u64::MAX]), u64::MAX / 10);
}

#[test]
fn forged_certificates_cannot_change_masks_values_operands_or_any_bound() {
    let expression = pattern(CASES[2], false, false);
    let good = recognize(&expression).unwrap();
    let mut variants = Vec::new();
    for maximum in [0, 65535, u64::MAX] {
        let mut v = good;
        v.evidence.maximum = maximum;
        variants.push(v);
    }
    for multiplier in [0, 1, u64::MAX, good.evidence.multiplier ^ 1] {
        let mut v = good;
        v.evidence.multiplier = multiplier;
        variants.push(v);
    }
    for shift in [0, 34, 36, 63, 64, u32::MAX] {
        let mut v = good;
        v.evidence.shift = shift;
        variants.push(v);
    }
    for divisor in [0, 1, 5, 9, 11, u64::MAX] {
        let mut v = good;
        v.divisor = divisor;
        variants.push(v);
    }
    for excess in [0, 1, 3, u64::MAX] {
        let mut v = good;
        v.evidence.excess = excess;
        variants.push(v);
    }
    for product_bound in [
        0,
        u128::MAX,
        good.evidence.product_bound - 1,
        good.evidence.product_bound + 1,
    ] {
        let mut v = good;
        v.evidence.product_bound = product_bound;
        variants.push(v);
    }
    for error_bound in [
        0,
        u128::MAX,
        good.evidence.error_bound - 1,
        good.evidence.error_bound + 1,
    ] {
        let mut v = good;
        v.evidence.error_bound = error_bound;
        variants.push(v);
    }
    for variant in variants {
        assert!(!validate(&expression, &variant));
    }
    let clone = good.value.clone();
    assert!(!validate(
        &expression,
        &NarrowDivisionView {
            value: &clone,
            ..good
        }
    ));
    let Expr::Binary(B::And, tree, _) = good.value else {
        panic!()
    };
    assert!(
        !validate(
            &expression,
            &NarrowDivisionView {
                value: tree,
                ..good
            }
        ),
        "mask cannot be dropped"
    );
    for changed in [
        raw(and(r(0), 0xffff), 0xcccc_cccd, 35, false),
        raw(and(r(0), 0xffff_ffff), 0xcccc_cccd ^ 1, 35, false),
        raw(and(r(0), 0xffff_ffff), 0xcccc_cccd, 34, false),
    ] {
        let forged = NarrowDivisionView {
            value: operand(&changed),
            ..good
        };
        assert!(!validate(&changed, &forged));
    }
    let overflow = raw(and(r(0), u64::MAX), 2, 63, false);
    let forged = NarrowDivisionView {
        value: operand(&overflow),
        divisor: 1 << 62,
        evidence: NarrowDivisionEvidence {
            maximum: u64::MAX,
            multiplier: 2,
            shift: 63,
            excess: 0,
            product_bound: u128::from(u64::MAX) * 2,
            error_bound: (1u128 << 63) - 2,
        },
    };
    assert!(
        !validate(&overflow, &forged),
        "a correct error proof cannot excuse low-product overflow"
    );
}

#[test]
fn all_syntactic_loads_and_oversized_or_deep_inputs_decline_before_matching() {
    for value in [
        Expr::load(r(0), Width::U64),
        Expr::select(c(1), r(0), Expr::load(c(u64::MAX), Width::U8)),
    ] {
        for mask in [0, 0xffff_ffff] {
            assert!(recognize(&raw(and(value.clone(), mask), 0xcccc_cccd, 35, false)).is_none());
        }
    }
    let mut deep = r(0);
    for _ in 0..=narrow_division_expr::MAX_DEPTH {
        deep = b(B::Add, deep, c(0));
    }
    assert!(recognize(&raw(and(deep, 255), 205, 11, false)).is_none());
    fn balanced(n: usize) -> Expr {
        if n == 1 {
            return r(0);
        }
        b(B::Add, balanced(n / 2), balanced(n - n / 2))
    }
    assert!(
        recognize(&raw(
            and(balanced(narrow_division_expr::MAX_NODES), 0),
            1,
            1,
            false
        ))
        .is_none()
    );
    const {
        assert!(narrow_division_expr::MAX_WORK >= narrow_division_expr::MAX_NODES);
    }
}

#[test]
fn small_word_model_checks_selected_masks_and_exhausts_multipliers_shifts_and_inputs() {
    let (mut accepted, mut compared) = (0usize, 0usize);
    for w in 2..=10 {
        let n = (1u64 << w) - 1;
        let mut masks = (0..=w).map(|bits| (1u64 << bits) - 1).collect::<Vec<_>>();
        masks.extend([0x55 & n, 0xaa & n]);
        masks.sort_unstable();
        masks.dedup();
        for maximum in masks {
            for m in 1..=n {
                for s in 0..w {
                    let product_bound = u128::from(maximum) * u128::from(m);
                    if product_bound > u128::from(n) {
                        continue;
                    }
                    let p = 1u128 << s;
                    let d = p.div_ceil(u128::from(m));
                    let e = u128::from(m) * d - p;
                    let error = if d >= 2 {
                        (u128::from(maximum) / d) * e + u128::from(m) * (d - 1)
                    } else {
                        p
                    };
                    let expected = d >= 2 && e < d && error < p;
                    let expression = raw(and(r(0), maximum), m, s, false);
                    let got = recognize(&expression);
                    assert_eq!(got.is_some(), expected, "w{w} max{maximum} m{m} s{s}");
                    if let Some(view) = got {
                        assert_eq!(u128::from(view.divisor), d);
                        assert!(validate(&expression, &view));
                        accepted += 1;
                        for x in 0..=n {
                            let value = x & maximum;
                            let observed = ((value * m) & n) >> s;
                            assert_eq!(
                                observed,
                                value / view.divisor,
                                "w{w} max{maximum} m{m} s{s} x{x}"
                            );
                            compared += 1;
                        }
                    }
                }
            }
        }
    }
    println!(
        "small words2..10: {accepted} accepted mask/M/S tuples, {compared} exhaustive raw-input checks"
    );
}

fn actual_candidates(opt: &str) -> Vec<Expr> {
    let scratch = native::Scratch::new();
    let object = scratch.0.join(format!("unsigned-div{opt}.o"));
    native::object(
        &native::fixture_root().join("recovery/unsigned-div-constant.c"),
        &object,
        opt,
        "fixture",
    );
    let lifted = nirvana::frontend::lift_elf(&std::fs::read(object).unwrap(), "fixture").unwrap();
    let reduced = nirvana::reduce::reduce(&lifted.program).unwrap();
    let webs = nirvana::web::split(reduced.program()).unwrap();
    nirvana::web_verify::validate(reduced.program(), webs.program()).unwrap();
    let widths = nirvana::value_width::ValueWidths::analyze(webs.program());
    let mut found = Vec::new();
    fn visit(e: &Expr, found: &mut Vec<Expr>) {
        if recognize(e).is_some() {
            found.push(e.clone());
            return;
        }
        match e {
            Expr::Unary(_, value) => visit(value, found),
            Expr::Binary(_, a, b) => {
                visit(a, found);
                visit(b, found)
            }
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => {
                for x in [condition, taken, not_taken] {
                    visit(x, found)
                }
            }
            Expr::Load { address, .. } => visit(address, found),
            _ => {}
        }
    }
    for i in webs.program().instructions() {
        for a in &i.assignments {
            let normalized = nirvana::presentation::normalize(&a.value, |r| {
                if reduced.parameters().contains(&r) {
                    Width::U64
                } else {
                    widths.width(r)
                }
            });
            visit(&normalized, &mut found);
        }
    }
    found
}

#[test]
fn actual_o2_word_lane_retains_its_explicit_bound_and_o0_conservatively_declines() {
    let found = actual_candidates("-O2");
    assert_eq!(found.len(), 2);
    for expression in &found {
        let view = recognize(expression).unwrap();
        assert!(validate(expression, &view));
        assert_eq!(view.divisor, 10);
        assert_eq!(
            (
                view.evidence.maximum,
                view.evidence.multiplier,
                view.evidence.shift
            ),
            (0xffff_ffff, 0xcccc_cccd, 35)
        );
        assert!(matches!(
            view.value,
            Expr::Unary(
                ir::UnaryOp::Extract {
                    start: 0,
                    width: Width::U32
                },
                _
            )
        ));
    }
    assert!(actual_candidates("-O0").is_empty());
}

#[test]
fn c11_low_product_and_borrowed_masked_division_match_ir_oracles_with_ubsan() {
    let scratch = native::Scratch::new();
    let mut source =
        String::from("#include <stdint.h>\n#include <stdio.h>\n#include <inttypes.h>\n");
    for (i, case) in CASES.into_iter().enumerate() {
        let expression = pattern(case, false, false);
        let view = recognize(&expression).unwrap();
        writeln!(source,"static uint64_t before{i}(uint64_t x) {{ return ((x & UINT64_C({})) * UINT64_C({})) >> {}; }}",case.mask,case.m,case.s).unwrap();
        writeln!(
            source,
            "static uint64_t after{i}(uint64_t x) {{ return (x & UINT64_C({})) / UINT64_C({}); }}",
            view.evidence.maximum, view.divisor
        )
        .unwrap();
    }
    source.push_str("int main(void){uint64_t x;while(scanf(\"%\" SCNu64,&x)==1){printf(");
    source.push_str(
        &(0..CASES.len() * 2)
            .map(|_| "\"%\" PRIu64")
            .collect::<Vec<_>>()
            .join(" \" \" "),
    );
    source.push_str(" \"\\n\"");
    for i in 0..CASES.len() {
        write!(source, ",before{i}(x),after{i}(x)").unwrap();
    }
    source.push_str(");}}\n");
    let path = scratch.0.join("narrow-div.c");
    std::fs::write(&path, &source).unwrap();
    let mut input = String::new();
    let mut expected = Vec::new();
    for value in VALUES.into_iter().chain(0..512) {
        writeln!(input, "{value}").unwrap();
        let mut row = Vec::new();
        for case in CASES {
            let result = (value & case.mask) / case.d;
            row.extend([result, result]);
        }
        expected.push(row);
    }
    if let Some(directory) = std::env::var_os("NIRVANA_NARROW_DIVISION_ARTIFACTS") {
        let directory = std::path::PathBuf::from(directory);
        std::fs::create_dir_all(&directory).unwrap();
        std::fs::write(directory.join("before-after.c"), &source).unwrap();
        std::fs::write(directory.join("inputs.txt"), &input).unwrap();
        std::fs::write(directory.join("expected.json"), format!("{expected:?}\n")).unwrap();
    }
    for optimization in ["-O0", "-O2"] {
        for ubsan in [false, true] {
            let binary = scratch.0.join(format!("narrow-div{optimization}{ubsan}"));
            let mut command = Command::new("cc");
            command.args([
                "-std=c11",
                "-Wall",
                "-Wextra",
                "-Werror",
                "-pedantic",
                optimization,
            ]);
            if ubsan {
                command.args(["-fsanitize=undefined", "-fno-sanitize-recover=undefined"]);
            }
            let output = native::compile_output(command.arg(&path).arg("-o").arg(&binary));
            assert!(
                output.status.success(),
                "{}",
                String::from_utf8_lossy(&output.stderr)
            );
            assert_eq!(
                native::run_fields(&binary, &input, CASES.len() * 2),
                expected,
                "{optimization}, UBSan={ubsan}"
            );
        }
    }
    println!(
        "C11 O0/O2 x UBSan off/on: {} exact scalar before/after/oracle comparisons",
        expected.len() * CASES.len() * 2 * 4
    );
}

#[test]
fn explicit_slices_supply_bounds_without_assuming_an_input_type() {
    let mut checked = 0;
    for width in [Width::U8, Width::U16, Width::U32, Width::U64] {
        for start in [0, 1, 7, 8, 16, 31, 32, 63, 64, 255] {
            let value = Expr::unary(ir::UnaryOp::Extract { start, width }, r(0));
            let maximum = width.mask() & u64::MAX.checked_shr(u32::from(start)).unwrap_or(0);
            for case in CASES.into_iter().take(3) {
                for commute in [false, true] {
                    let expression = raw(value.clone(), case.m, case.s, commute);
                    let candidate = recognize(&expression);
                    if maximum > case.mask {
                        continue;
                    }
                    let view =
                        candidate.expect("a tighter slice preserves the division certificate");
                    assert!(validate(&expression, &view));
                    assert_eq!((view.divisor, view.evidence.maximum), (case.d, maximum));
                    assert!(std::ptr::eq(view.value, operand(&expression)));
                    for x in VALUES {
                        let input = evaluate(&value, &[x]);
                        assert_eq!(evaluate(&expression, &[x]), input / case.d);
                        checked += 1;
                    }
                    let mut stale = view;
                    stale.evidence.maximum ^= 1;
                    assert!(!validate(&expression, &stale));
                }
            }
        }
    }
    println!(
        "{checked} explicit-slice reciprocal observations across all word widths and boundary positions"
    );
}

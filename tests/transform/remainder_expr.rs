use crate::support::ir::c;
use crate::support::ir::r;
use crate::support::native;
use ir::{BinaryOp as B, Control, Expr, IrInstruction, Program, Width};
use nirvana::{ir, narrow_division_expr, remainder_expr};
use remainder_expr::{QuotientEvidence, RemainderView, recognize, validate};
use std::collections::BTreeSet;
use std::fmt::Write as _;
use std::process::Command;
fn b(op: B, a: Expr, z: Expr) -> Expr {
    Expr::binary(op, a, z)
}
fn and(value: Expr, mask: u64, commute: bool) -> Expr {
    if commute {
        b(B::And, c(mask), value)
    } else {
        b(B::And, value, c(mask))
    }
}
fn high(value: Expr, m: u64, s: u32, commute: bool) -> Expr {
    let p = if commute {
        b(B::UMulHigh, c(m), value)
    } else {
        b(B::UMulHigh, value, c(m))
    };
    if s == 0 {
        p
    } else {
        b(B::Shr, p, c(u64::from(s)))
    }
}
fn low(value: Expr, m: u64, s: u32, commute: bool) -> Expr {
    b(
        B::Shr,
        if commute {
            b(B::Mul, c(m), value)
        } else {
            b(B::Mul, value, c(m))
        },
        c(u64::from(s)),
    )
}
fn rem(
    value: Expr,
    q: Expr,
    d: u64,
    product_mask: Option<u64>,
    result_mask: Option<u64>,
    commute: bool,
) -> Expr {
    let mut product = if commute {
        b(B::Mul, c(d), q)
    } else {
        b(B::Mul, q, c(d))
    };
    if let Some(mask) = product_mask {
        product = and(product, mask, commute);
    }
    let mut result = b(B::Sub, value, product);
    if let Some(mask) = result_mask {
        result = and(result, mask, commute);
    }
    result
}
fn eval(e: &Expr, rs: &[u64]) -> u64 {
    match e {
        Expr::Unary(op, value) => crate::support::ir::unary_value(*op, eval(value, rs)),
        Expr::Const(x) => *x,
        Expr::Register(r) => rs[r.0],
        Expr::Select {
            condition,
            taken,
            not_taken,
        } => {
            if eval(condition, rs) != 0 {
                eval(taken, rs)
            } else {
                eval(not_taken, rs)
            }
        }
        Expr::Binary(op, a, z) => {
            let a = eval(a, rs);
            let z = eval(z, rs);
            match op {
                B::Add => a.wrapping_add(z),
                B::Sub => a.wrapping_sub(z),
                B::Mul => a.wrapping_mul(z),
                B::UMulHigh => ((u128::from(a) * u128::from(z)) >> 64) as u64,
                B::SMulHigh => ((i128::from(a as i64) * i128::from(z as i64)) >> 64) as u64,
                B::AShr => ((a as i64) >> (z & 63)) as u64,
                B::UDiv | B::URem | B::SDiv | B::SRem => {
                    crate::support::ir::division_value(*op, a, z)
                }
                B::And => a & z,
                B::Or => a | z,
                B::Xor => a ^ z,
                B::Shl => a.wrapping_shl((z & 63) as u32),
                B::Shr => a.wrapping_shr((z & 63) as u32),
                B::Eq => (a == z) as u64,
                B::Ne => (a != z) as u64,
                B::Ult => (a < z) as u64,
                B::Ule => (a <= z) as u64,
            }
        }
        Expr::Load { .. } => panic!("pure oracle containsLoad"),
    }
}
fn deps(e: &Expr) -> BTreeSet<usize> {
    let mut pending = vec![e];
    let mut out = BTreeSet::new();
    while let Some(e) = pending.pop() {
        match e {
            Expr::Register(r) => {
                out.insert(r.0);
            }
            Expr::Unary(_, value) => pending.push(value),
            Expr::Binary(_, a, b) => pending.extend([&**a, &**b]),
            Expr::Load { address, .. } => pending.push(address),
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => pending.extend([&**condition, &**taken, &**not_taken]),
            _ => {}
        }
    }
    out
}
fn inputs(d: u64) -> Vec<u64> {
    let mut v = BTreeSet::from([
        0,
        1,
        2,
        3,
        d - 1,
        d,
        d.saturating_add(1),
        u32::MAX as u64,
        1 << 63,
        u64::MAX,
    ]);
    for q in [1, 2, 3, 255, u64::MAX / d] {
        if let Some(x) = q.checked_mul(d) {
            for x in [x.checked_sub(1), Some(x), x.checked_add(1)]
                .into_iter()
                .flatten()
            {
                v.insert(x);
            }
        }
    }
    let mut s = 0x7472_0d81_391c_c021_u64;
    for _ in 0..2048 {
        s ^= s << 13;
        s ^= s >> 7;
        s ^= s << 17;
        v.insert(s);
    }
    v.into_iter().collect()
}
const HIGH: [(u64, u64, u32); 9] = [
    (2, 1 << 63, 0),
    (3, 0xaaaa_aaaa_aaaa_aaab, 1),
    (5, 0xcccc_cccc_cccc_cccd, 2),
    (6, 0xaaaa_aaaa_aaaa_aaab, 2),
    (9, 0xe38e_38e3_8e38_e38f, 3),
    (10, 0xcccc_cccc_cccc_cccd, 3),
    (1 << 63, 2, 0),
    (5 << 61, 0xcccc_cccc_cccc_cccd, 63),
    ((1 << 63) + 1, u64::MAX, 63),
];
#[test]
fn high_remainders_match_u128_rust_and_raw_ir_with_commuted_operands() {
    let mut checks = 0;
    for (d, m, s) in HIGH {
        for commute in [false, true] {
            for clips in [false, true] {
                let x = r(0);
                let e = rem(
                    x.clone(),
                    high(x, m, s, commute),
                    d,
                    clips.then_some(u64::MAX),
                    clips.then_some(u64::MAX),
                    commute,
                );
                let v = recognize(&e).unwrap();
                assert!(validate(&e, &v));
                assert_eq!(v.divisor, d);
                assert_eq!(v.maximum_remainder, d - 1);
                let before = e.clone();
                for x in inputs(d) {
                    let q = ((u128::from(x) * u128::from(m)) >> (64 + s)) as u64;
                    assert_eq!(q, x / d);
                    assert_eq!(eval(&e, &[x]), x % d);
                    assert_eq!(eval(v.value, &[x]) % v.divisor, x % d);
                    checks += 1;
                }
                assert_eq!(e, before);
            }
        }
    }
    println!("{checks} highu128/raw/rem checks");
}
#[test]
fn explicit_narrow_masks_and_clipping_keep_full_raw_dividend() {
    let mut checks = 0;
    for (mask, m, s, d) in [
        (0xffff_ffff, 0xcccc_cccd, 35, 10),
        (0xa5, 171, 9, 3),
        (0, 1, 1, 2),
        (u64::MAX, 1, 1, 2),
    ] {
        for commute in [false, true] {
            let x = and(r(0), mask, commute);
            let e = rem(
                x.clone(),
                low(x, m, s, commute),
                d,
                Some(if mask == 0xa5 { 0xff } else { mask }),
                Some(if d == 3 { 3 } else { u64::MAX }),
                commute,
            );
            let v = recognize(&e).unwrap();
            assert_eq!(v.maximum_remainder, mask.min(d - 1));
            assert_eq!(deps(&e), deps(v.value));
            assert!(matches!(v.value, Expr::Binary(B::And, _, _)));
            for raw in inputs(d) {
                let x = raw & mask;
                assert_eq!(eval(&e, &[raw]), x % d);
                assert_eq!(eval(v.value, &[raw]) % d, x % d);
                checks += 1;
            }
        }
    }
    println!("{checks} narrow/raw/rem checks");
}
#[test]
fn noncontiguous_numeric_bounds_require_the_full_low_bit_hull() {
    let x = and(r(0), 0xa5, false);
    let q = low(x.clone(), 171, 9, false);
    let bad_product = rem(x.clone(), q.clone(), 3, Some(0xa5), None, false);
    assert!(recognize(&bad_product).is_none());
    assert_ne!(eval(&bad_product, &[128]), 128 % 3);
    let bad_result = rem(x.clone(), q.clone(), 3, None, Some(2), false);
    assert!(recognize(&bad_result).is_none());
    assert_ne!(eval(&bad_result, &[1]), 1);
    let good = rem(x, q, 3, Some(0xff), Some(3), false);
    assert!(recognize(&good).is_some());
    for n in 0..256 {
        assert_eq!(eval(&good, &[n]), (n & 0xa5) % 3);
    }
}
#[test]
fn wrong_x_d_magic_or_materialized_quotient_never_uses_dataflow_guesses() {
    let x = r(0);
    let q = high(x.clone(), 0xcccc_cccc_cccc_cccd, 3, false);
    for e in [
        rem(r(1), q.clone(), 10, None, None, false),
        rem(x.clone(), q.clone(), 9, None, None, false),
        rem(x.clone(), q.clone(), 0, None, None, false),
        rem(x.clone(), r(1), 10, None, None, false),
        rem(
            x.clone(),
            b(
                B::Shr,
                b(B::UMulHigh, x.clone(), c(0xcccc_cccc_cccc_cccc)),
                c(3),
            ),
            10,
            None,
            None,
            false,
        ),
        rem(
            b(B::Add, r(0), c(1)),
            high(b(B::Add, c(1), r(0)), 0xcccc_cccc_cccc_cccd, 3, false),
            10,
            None,
            None,
            false,
        ),
    ] {
        assert!(recognize(&e).is_none(), "{e:?}");
    }
    let expr = rem(x, q, 10, None, None, false);
    let source = Program::new(
        0,
        2,
        vec![IrInstruction {
            address: 0,
            size: 1,
            assignments: vec![],
            control: Control::Return(expr.clone()),
        }],
    )
    .unwrap();
    let v = recognize(&expr).unwrap();
    for n in inputs(10).into_iter().step_by(17) {
        assert_eq!(
            source.execute(&[n, 777], 1).unwrap().value,
            eval(v.value, &[n, 777]) % 10
        );
    }
}
#[test]
fn raw_equality_is_bounded_structural_and_preserves_complex_select_dependencies() {
    let x = Expr::select(
        b(B::Ult, r(0), r(1)),
        b(B::Add, r(2), c(u64::MAX)),
        b(B::Xor, r(1), r(2)),
    );
    let e = rem(
        x.clone(),
        high(x, 0xcccc_cccc_cccc_cccd, 3, false),
        10,
        None,
        None,
        false,
    );
    let v = recognize(&e).unwrap();
    assert_eq!(deps(&e), deps(v.value));
    let Expr::Binary(_, lhs, _) = &e else {
        panic!()
    };
    assert!(std::ptr::eq(&**lhs, v.value));
    for n in inputs(10).into_iter().step_by(31) {
        let rs = [n, !n, n.rotate_left(17)];
        assert_eq!(eval(&e, &rs), eval(v.value, &rs) % 10);
    }
}
#[test]
fn every_load_including_dead_lazy_arm_and_masked_zero_declines() {
    for x in [
        Expr::load(r(0), Width::U64),
        Expr::select(c(1), r(0), Expr::load(c(u64::MAX), Width::U8)),
        b(B::Mul, c(0), Expr::load(r(0), Width::U16)),
    ] {
        let e = rem(
            x.clone(),
            high(x, 0xcccc_cccc_cccc_cccd, 3, false),
            10,
            None,
            None,
            false,
        );
        assert!(recognize(&e).is_none());
    }
    let good = rem(
        r(0),
        high(r(0), 0xcccc_cccc_cccc_cccd, 3, false),
        10,
        None,
        None,
        false,
    );
    let v = recognize(&good).unwrap();
    let bad = Expr::select(c(1), good.clone(), Expr::load(c(u64::MAX), Width::U8));
    assert!(!validate(&bad, &v));
}
#[test]
fn independently_checked_evidence_rejects_changed_fields_or_borrowed_clone() {
    let x = and(r(0), 0xffff_ffff, false);
    let e = rem(
        x.clone(),
        low(x, 0xcccc_cccd, 35, false),
        10,
        Some(0xffff_ffff),
        Some(0xffff_ffff),
        false,
    );
    let v = recognize(&e).unwrap();
    let copy = v.value.clone();
    let mut cases = vec![
        RemainderView { value: &copy, ..v },
        RemainderView { divisor: 0, ..v },
        RemainderView { divisor: 9, ..v },
        RemainderView {
            maximum_remainder: 0,
            ..v
        },
        RemainderView {
            maximum_remainder: u64::MAX,
            ..v
        },
        RemainderView {
            evidence: remainder_expr::RemainderEvidence {
                maximum: u64::MAX,
                ..v.evidence
            },
            ..v
        },
        RemainderView {
            evidence: remainder_expr::RemainderEvidence {
                product_mask: None,
                ..v.evidence
            },
            ..v
        },
        RemainderView {
            evidence: remainder_expr::RemainderEvidence {
                result_mask: Some(9),
                ..v.evidence
            },
            ..v
        },
    ];
    let QuotientEvidence::Narrow(n) = v.evidence.quotient else {
        panic!()
    };
    cases.push(RemainderView {
        evidence: remainder_expr::RemainderEvidence {
            quotient: QuotientEvidence::Narrow(narrow_division_expr::NarrowDivisionEvidence {
                shift: 64,
                ..n
            }),
            ..v.evidence
        },
        ..v
    });
    cases.push(RemainderView {
        evidence: remainder_expr::RemainderEvidence {
            quotient: QuotientEvidence::Narrow(narrow_division_expr::NarrowDivisionEvidence {
                excess: n.excess + 1,
                ..n
            }),
            ..v.evidence
        },
        ..v
    });
    for bad in cases {
        assert!(!validate(&e, &bad));
    }
}
#[test]
fn whole_tree_limits_precede_structural_equality_or_certificate_inspection() {
    let mut x = r(0);
    for _ in 0..=remainder_expr::MAX_DEPTH {
        x = b(B::Add, x, c(0));
    }
    let e = rem(
        x.clone(),
        high(x, 0xcccc_cccc_cccc_cccd, 3, false),
        10,
        None,
        None,
        false,
    );
    assert!(recognize(&e).is_none());
    fn balanced(n: usize) -> Expr {
        if n == 1 {
            r(0)
        } else {
            b(B::Xor, balanced(n / 2), balanced(n - n / 2))
        }
    }
    let x = balanced(remainder_expr::MAX_NODES);
    let e = rem(
        x.clone(),
        high(x, 0xcccc_cccc_cccc_cccd, 3, false),
        10,
        None,
        None,
        false,
    );
    assert!(recognize(&e).is_none());
    const {
        assert!(remainder_expr::MAX_WORK >= remainder_expr::MAX_NODES);
    }
}

#[test]
fn native_c11_percent_matches_magic_raw_and_rust_at_o0_o2_and_ubsan() {
    let out = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("target/remainder-expr/native");
    std::fs::create_dir_all(&out).unwrap();
    let mut source = String::from(
        r#"
#include <stdint.h>
#include <stdio.h>
#include <inttypes.h>
static uint64_t high(uint64_t a,uint64_t b){uint64_t a0=a&UINT64_C(0xffffffff),a1=a>>32,b0=b&UINT64_C(0xffffffff),b1=b>>32;uint64_t low=a0*b0,t=a1*b0+(low>>32),mid=(t&UINT64_C(0xffffffff))+a0*b1;return a1*b1+(t>>32)+(mid>>32);}
int main(void){uint64_t x;while(scanf("%" SCNu64,&x)==1){
"#,
    );
    for (d, m, s) in HIGH {
        writeln!(source,"printf(\"%\" PRIu64 \" %\" PRIu64 \" \",x-(high(x,UINT64_C({m}))>>{s})*UINT64_C({d}),x%UINT64_C({d}));").unwrap();
    }
    for (mask, m, s, d, pm, rm) in [
        (
            0xffff_ffff_u64,
            0xcccc_cccd_u64,
            35,
            10,
            0xffff_ffff_u64,
            0xffff_ffff_u64,
        ),
        (0xa5, 171, 9, 3, 0xff, 3),
        (0, 1, 1, 2, 0, 0),
    ] {
        writeln!(source,"{{uint64_t v=x&UINT64_C({mask}),q=(v*UINT64_C({m}))>>{s};printf(\"%\" PRIu64 \" %\" PRIu64 \" \",(v-((q*UINT64_C({d}))&UINT64_C({pm})))&UINT64_C({rm}),v%UINT64_C({d}));}}").unwrap();
    }
    source.push_str("putchar('\\n');}return 0;}\n");
    let p = out.join("remainder.c");
    std::fs::write(&p, source).unwrap();
    let values: Vec<_> = inputs(10).into_iter().step_by(5).collect();
    let input = values
        .iter()
        .map(u64::to_string)
        .collect::<Vec<_>>()
        .join("\n")
        + "\n";
    let expected: Vec<Vec<u64>> = values
        .iter()
        .map(|x| {
            let mut r: Vec<_> = HIGH.iter().flat_map(|(d, _, _)| [*x % d, *x % d]).collect();
            r.extend([
                (*x & 0xffff_ffff) % 10,
                (*x & 0xffff_ffff) % 10,
                (*x & 0xa5) % 3,
                (*x & 0xa5) % 3,
                0,
                0,
            ]);
            r
        })
        .collect();
    std::fs::write(out.join("inputs.txt"), &input).unwrap();
    for opt in ["-O0", "-O2"] {
        for sanitize in [false, true] {
            let binary = out.join(format!("remainder{opt}-{sanitize}"));
            let mut cmd = Command::new("cc");
            cmd.args([
                "-std=c11",
                "-Wall",
                "-Wextra",
                "-Werror",
                "-pedantic",
                "-fno-lto",
                opt,
            ]);
            if sanitize {
                cmd.args(["-fsanitize=undefined", "-fno-sanitize-recover=undefined"]);
            }
            let result = native::compile_output(cmd.arg(&p).arg("-o").arg(&binary));
            assert!(
                result.status.success(),
                "{}",
                String::from_utf8_lossy(&result.stderr)
            );
            assert_eq!(
                native::run_fields(&binary, &input, (HIGH.len() + 3) * 2),
                expected
            );
        }
    }
    println!(
        "native percent: {}inputs x{}pairs x4builds",
        values.len(),
        HIGH.len() + 3
    );
}

#[test]
fn extreme_high_divisors_and_shift63_preserve_unsigned_product_and_remainder_bounds() {
    for (d, m, s, clip) in [
        (1_u64 << 63, 2, 0, (1_u64 << 63) - 1),
        (5_u64 << 61, 0xcccc_cccc_cccc_cccd, 63, u64::MAX),
        ((1_u64 << 63) + 1, u64::MAX, 63, u64::MAX),
    ] {
        let e = rem(
            r(0),
            high(r(0), m, s, false),
            d,
            Some(u64::MAX),
            Some(clip),
            false,
        );
        let v = recognize(&e).unwrap();
        assert!(validate(&e, &v));
        assert_eq!(v.maximum_remainder, d - 1);
        for x in inputs(d) {
            assert_eq!(eval(&e, &[x]), x % d);
        }
    }
}

#[test]
fn actual_o2_fixture_exposes_one_u32_remainder_and_no_materialized_u64_remainder() {
    let out =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("target/remainder-expr/fixture");
    std::fs::create_dir_all(&out).unwrap();
    fn visit(e: &Expr, count: &mut usize) {
        if let Some(v) = recognize(e) {
            assert_eq!(v.divisor, 10);
            assert_eq!(v.maximum_remainder, 9);
            assert!(matches!(v.evidence.quotient, QuotientEvidence::Narrow(_)));
            assert_eq!(deps(e), deps(v.value));
            assert!(validate(e, &v));
            *count += 1;
            return;
        }
        match e {
            Expr::Unary(_, value) => visit(value, count),
            Expr::Binary(_, a, b) => {
                visit(a, count);
                visit(b, count)
            }
            Expr::Load { address, .. } => visit(address, count),
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => {
                visit(condition, count);
                visit(taken, count);
                visit(not_taken, count)
            }
            _ => {}
        }
    }
    let states: Vec<_> = inputs(10)
        .into_iter()
        .step_by(97)
        .enumerate()
        .map(|(i, x)| {
            [
                x,
                0xaaaa_aaaa_aaaa_aaaa,
                0xbbbb_bbbb_bbbb_bbbb,
                if i & 1 == 0 { u64::MAX } else { x },
            ]
        })
        .collect();
    let input = states
        .iter()
        .map(|s| s.iter().map(u64::to_string).collect::<Vec<_>>().join(" "))
        .collect::<Vec<_>>()
        .join("\n")
        + "\n";
    std::fs::write(out.join("inputs.txt"), &input).unwrap();
    let mut counts = String::new();
    for opt in ["-O0", "-O2"] {
        let object = out.join(format!("fixture{opt}.o"));
        let harness = out.join(format!("harness{opt}.o"));
        let binary = out.join(format!("fixture{opt}"));
        native::object(
            &native::fixture_root().join("recovery/unsigned-div-constant.c"),
            &object,
            opt,
            "fixture",
        );
        native::object(
            &native::fixture_root().join("harness.c"),
            &harness,
            opt,
            "fixture",
        );
        native::link(&[&object, &harness], &binary);
        let native = native::run(&binary, &input);
        let f = nirvana::frontend::lift_elf(&std::fs::read(&object).unwrap(), "fixture").unwrap();
        let original = f.program.instructions().to_vec();
        let reduced = nirvana::reduce::reduce(&f.program).unwrap();
        let web = nirvana::web::split(reduced.program()).unwrap();
        nirvana::web_verify::validate(reduced.program(), web.program()).unwrap();
        let masked =
            nirvana::load_mask::propose(web.program(), reduced.parameters()).and_then(|p| {
                nirvana::load_mask::validate(web.program(), &p, reduced.parameters())
                    .ok()
                    .map(|_| p)
            });
        let selected = masked.as_ref().unwrap_or_else(|| web.program());
        let widths = nirvana::value_width::ValueWidths::analyze(selected);
        let width = |reg| {
            if reduced.parameters().contains(&reg) {
                Width::U64
            } else {
                widths.width(reg)
            }
        };
        let mut count = 0;
        for instruction in selected.instructions() {
            for assignment in &instruction.assignments {
                visit(
                    &nirvana::presentation::normalize(&assignment.value, width),
                    &mut count,
                );
            }
            match &instruction.control {
                Control::Return(e) | Control::Branch { condition: e, .. } => {
                    visit(&nirvana::presentation::normalize(e, width), &mut count)
                }
                _ => {}
            }
        }
        assert_eq!(count, if opt == "-O2" { 1 } else { 0 });
        writeln!(
            counts,
            "{opt} normalized candidates{count}, native rows{}",
            states.len()
        )
        .unwrap();
        for (state, row) in states.iter().zip(native) {
            let mut registers = vec![0; f.program.register_count()];
            registers[nirvana::x86::RDI] = 4096;
            registers[nirvana::x86::RSP] = 65536;
            let mut memory: Vec<_> = (0usize..65536)
                .map(|i| i.wrapping_mul(29).wrapping_add(7) as u8)
                .collect();
            for (i, x) in state.iter().enumerate() {
                memory[4096 + i * 8..4096 + i * 8 + 8].copy_from_slice(&x.to_le_bytes());
            }
            let raw = f
                .program
                .execute_with_memory(&registers, 0, &memory, 1000)
                .unwrap();
            let reduced = reduced
                .execute_with_memory(&registers, 0, &memory, 1000)
                .unwrap();
            assert_eq!(raw.value, reduced.value);
            assert_eq!(raw.memory, reduced.memory);
            assert_eq!(raw.trace, reduced.trace);
            let q = state[0] / 10;
            let rem = state[0] % 10;
            let word = state[3] as u32;
            let narrow = u64::from(word / 10) + u64::from(word % 10);
            let expected = [q ^ (rem << 8) ^ narrow, state[0], q, rem, narrow];
            assert_eq!(row, expected);
            assert_eq!(raw.value, expected[0]);
            for (i, x) in expected[1..].iter().enumerate() {
                assert_eq!(
                    u64::from_le_bytes(
                        raw.memory[4096 + i * 8..4096 + i * 8 + 8]
                            .try_into()
                            .unwrap()
                    ),
                    *x
                );
            }
        }
        assert_eq!(f.program.instructions(), original);
    }
    std::fs::write(out.join("adoption.txt"), &counts).unwrap();
    print!("{counts}");
}

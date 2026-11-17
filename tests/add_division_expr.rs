use nirvana::{add_division_expr, ir};
#[path = "support/native.rs"]
#[allow(dead_code)]
mod native;
use add_division_expr::{AddDivisionEvidence, AddDivisionView, recognize, validate};
use ir::{BinaryOp as B, Control, Expr, IrInstruction, Program, Reg, Width};
use std::collections::BTreeSet;
use std::fmt::Write as _;
use std::process::Command;
fn c(x: u64) -> Expr {
    Expr::Const(x)
}
fn r(i: usize) -> Expr {
    Expr::Register(Reg(i))
}
fn b(op: B, a: Expr, z: Expr) -> Expr {
    Expr::binary(op, a, z)
}
fn high(x: Expr, m: u64, commute: bool) -> Expr {
    if commute {
        b(B::UMulHigh, c(m), x)
    } else {
        b(B::UMulHigh, x, c(m))
    }
}
fn pattern(x: Expr, m: u64, s: u32, order: u8) -> Expr {
    let outside = high(x.clone(), m, order & 2 != 0);
    let half = b(
        B::Shr,
        b(B::Sub, x.clone(), high(x, m, order & 4 != 0)),
        c(1),
    );
    let avg = if order & 1 != 0 {
        b(B::Add, half, outside)
    } else {
        b(B::Add, outside, half)
    };
    b(B::Shr, avg, c(u64::from(s)))
}
fn multiplier(d: u64, s: u32) -> u64 {
    let h = (1_u128 << (65 + s)).div_ceil(u128::from(d));
    u64::try_from(h - (1_u128 << 64)).unwrap()
}
fn kernel(x: u64, m: u64, s: u32) -> u64 {
    let t = ((u128::from(x) * u128::from(m)) >> 64) as u64;
    let difference = x.checked_sub(t).unwrap();
    t.checked_add(difference / 2).unwrap() >> s
}
// X*H can need129bits. Retain the carry above the wrapping low128bits.
fn extended_oracle(x: u64, m: u64, s: u32) -> u64 {
    let (a, carry) = ((u128::from(x)) << 64).overflowing_add(u128::from(x) * u128::from(m));
    let exponent = 65 + s;
    (a >> exponent) as u64 | if carry { 1_u64 << (128 - exponent) } else { 0 }
}
fn eval(e: &Expr, v: &[u64]) -> u64 {
    match e {
        Expr::Const(x) => *x,
        Expr::Register(r) => v[r.0],
        Expr::Select {
            condition,
            taken,
            not_taken,
        } => {
            if eval(condition, v) != 0 {
                eval(taken, v)
            } else {
                eval(not_taken, v)
            }
        }
        Expr::Binary(op, a, z) => {
            let a = eval(a, v);
            let z = eval(z, v);
            match op {
                B::Add => a.wrapping_add(z),
                B::Sub => a.wrapping_sub(z),
                B::Mul => a.wrapping_mul(z),
                B::UMulHigh => ((a as u128 * z as u128) >> 64) as u64,
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
        _ => panic!("pure"),
    }
}
fn inputs(d: u64) -> Vec<u64> {
    let mut values = BTreeSet::from([
        0,
        1,
        2,
        3,
        7,
        8,
        d - 1,
        d,
        d.saturating_add(1),
        u32::MAX as u64,
        1 << 63,
        u64::MAX,
    ]);
    for q in [1, 2, 3, 127, u64::MAX / d] {
        if let Some(x) = q.checked_mul(d) {
            for x in [x.checked_sub(1), Some(x), x.checked_add(1)]
                .into_iter()
                .flatten()
            {
                values.insert(x);
            }
        }
    }
    let mut seed = 0x2d4b381e84da9907_u64;
    for _ in 0..1024 {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        values.insert(seed);
    }
    values.into_iter().collect()
}
const CASES: [(u64, u32); 9] = [
    (2, 0),
    (3, 1),
    (4, 1),
    (5, 2),
    (7, 2),
    (9, 3),
    (10, 3),
    (14, 3),
    (1 << 63, 62),
];
#[test]
fn all_orderings_and_certificates_match_u64_division_and_129_bit_oracle() {
    let mut checks = 0;
    for (d, s) in CASES {
        let m = multiplier(d, s);
        for order in 0..8 {
            let e = pattern(r(0), m, s, order);
            let original = e.clone();
            let view = recognize(&e).unwrap();
            assert_eq!(view.divisor, d);
            assert!(validate(&e, &view));
            for x in inputs(d) {
                let a = kernel(x, m, s);
                assert_eq!(a, extended_oracle(x, m, s));
                assert_eq!(a, x / d);
                assert_eq!(eval(&e, &[x]), x / d);
                checks += 1;
            }
            assert_eq!(e, original);
        }
    }
    println!("{checks} orderedraw/kernel/129bit/division checks");
}
#[test]
fn kernel_floor_identity_and_safe_intermediates_hold_even_without_a_division_certificate() {
    let mut checks = 0;
    for m in [0, 1, 0x2492492492492493, 1 << 63, (1 << 63) - 1, u64::MAX] {
        for s in [0, 1, 2, 31, 61, 62] {
            for x in inputs(7) {
                assert_eq!(kernel(x, m, s), extended_oracle(x, m, s));
                checks += 1;
            }
        }
    }
    let x = u64::MAX;
    assert!(
        ((x as u128) << 64)
            .overflowing_add((x as u128) * (x as u128))
            .1
    );
    println!("{checks} kernel identities including129bitnumerators");
}
#[test]
fn generated_reciprocals_accept_only_the_recomputed_sufficient_bound() {
    let mut accepted = 0;
    for d in 2..=256_u64 {
        let s = 63 - d.leading_zeros() - u32::from(d.is_power_of_two());
        let m = multiplier(d, s);
        let e = pattern(r(0), m, s, 0);
        if let Some(v) = recognize(&e) {
            assert_eq!(v.divisor, d);
            assert!(validate(&e, &v));
            for x in inputs(d).into_iter().step_by(17) {
                assert_eq!(kernel(x, m, s), x / d);
            }
            accepted += 1;
        }
    }
    assert!(accepted > 50);
    println!("certified{accepted} generateddivisors");
}
#[test]
fn zero_multiplier_power_of_two_family_and_shift62_are_supported() {
    for s in [0, 1, 31, 61, 62] {
        let e = pattern(r(0), 0, s, 0);
        let v = recognize(&e).unwrap();
        assert_eq!(v.divisor, 1_u64 << (s + 1));
        for x in [0, 1, 1 << 63, u64::MAX] {
            assert_eq!(eval(&e, &[x]), x / v.divisor);
        }
    }
    let m = 0x2492492492492493;
    let e = pattern(r(0), m, 62, 0);
    let v = recognize(&e).unwrap();
    assert_eq!(v.divisor, 7_u64 << 60);
}
#[test]
fn wrong_constants_counts_and_unsafe_direct_average_have_counterexamples() {
    let m = 0x2492492492492493;
    let bad = pattern(r(0), m - 1, 2, 0);
    assert!(recognize(&bad).is_none());
    assert_ne!(eval(&bad, &[7]), 1);
    let unsafe_average = b(
        B::Shr,
        b(B::Shr, b(B::Add, r(0), high(r(0), m, false)), c(1)),
        c(2),
    );
    assert!(recognize(&unsafe_average).is_none());
    assert_ne!(eval(&unsafe_average, &[u64::MAX]), u64::MAX / 7);
    for s in [63, 64, 65, u64::MAX] {
        let Expr::Binary(_, a, _) = pattern(r(0), m, 2, 0) else {
            panic!()
        };
        assert!(recognize(&b(B::Shr, *a, c(s))).is_none());
    }
    let wrong_inner = b(
        B::Shr,
        b(
            B::Add,
            high(r(0), m, false),
            b(B::Shr, b(B::Sub, r(0), high(r(0), m, false)), c(0)),
        ),
        c(2),
    );
    assert!(recognize(&wrong_inner).is_none());
    assert_ne!(eval(&wrong_inner, &[4]), 4 / 7);
    for inner in [2, 63, 64, 65] {
        let e = b(
            B::Shr,
            b(
                B::Add,
                high(r(0), m, false),
                b(B::Shr, b(B::Sub, r(0), high(r(0), m, false)), c(inner)),
            ),
            c(2),
        );
        assert!(recognize(&e).is_none());
    }
}
#[test]
fn different_dividends_products_or_materialized_t_never_establish_equality() {
    let m = 0x2492492492492493;
    for e in [
        b(
            B::Shr,
            b(
                B::Add,
                high(r(0), m, false),
                b(B::Shr, b(B::Sub, r(1), high(r(0), m, false)), c(1)),
            ),
            c(2),
        ),
        b(
            B::Shr,
            b(
                B::Add,
                high(r(0), m + 1, false),
                b(B::Shr, b(B::Sub, r(0), high(r(0), m, false)), c(1)),
            ),
            c(2),
        ),
        b(
            B::Shr,
            b(B::Add, r(1), b(B::Shr, b(B::Sub, r(0), r(1)), c(1))),
            c(2),
        ),
        b(
            B::Shr,
            b(
                B::Add,
                high(r(0), m, false),
                b(B::Shr, b(B::Sub, high(r(0), m, false), r(0)), c(1)),
            ),
            c(2),
        ),
        b(
            B::Shr,
            b(
                B::Add,
                high(b(B::Add, r(0), c(1)), m, false),
                b(
                    B::Shr,
                    b(
                        B::Sub,
                        b(B::Add, c(1), r(0)),
                        high(b(B::Add, r(0), c(1)), m, false),
                    ),
                    c(1),
                ),
            ),
            c(2),
        ),
    ] {
        assert!(recognize(&e).is_none());
    }
}
#[test]
fn independent_validator_rejects_each_forged_field_and_borrowed_clone() {
    let e = pattern(r(0), 0x2492492492492493, 2, 0);
    let v = recognize(&e).unwrap();
    let copy = v.value.clone();
    for bad in [
        AddDivisionView { value: &copy, ..v },
        AddDivisionView { divisor: 0, ..v },
        AddDivisionView { divisor: 1, ..v },
        AddDivisionView { divisor: 8, ..v },
        AddDivisionView {
            divisor: u64::MAX,
            ..v
        },
        AddDivisionView {
            evidence: AddDivisionEvidence {
                multiplier: v.evidence.multiplier - 1,
                ..v.evidence
            },
            ..v
        },
        AddDivisionView {
            evidence: AddDivisionEvidence {
                multiplier: 0,
                ..v.evidence
            },
            ..v
        },
        AddDivisionView {
            evidence: AddDivisionEvidence {
                shift: 1,
                ..v.evidence
            },
            ..v
        },
        AddDivisionView {
            evidence: AddDivisionEvidence {
                shift: 63,
                ..v.evidence
            },
            ..v
        },
        AddDivisionView {
            evidence: AddDivisionEvidence {
                shift: u32::MAX,
                ..v.evidence
            },
            ..v
        },
        AddDivisionView {
            evidence: AddDivisionEvidence {
                excess: 4,
                ..v.evidence
            },
            ..v
        },
        AddDivisionView {
            evidence: AddDivisionEvidence {
                upper_bound: u128::MAX,
                ..v.evidence
            },
            ..v
        },
    ] {
        assert!(!validate(&e, &bad));
    }
}
#[test]
fn whole_tree_load_depth_and_size_limits_apply_before_matching_or_equality() {
    for x in [
        Expr::load(r(0), Width::U64),
        Expr::select(c(1), r(0), Expr::load(c(u64::MAX), Width::U8)),
        b(B::Mul, c(0), Expr::load(r(0), Width::U16)),
    ] {
        assert!(recognize(&pattern(x, 0x2492492492492493, 2, 0)).is_none());
    }
    let mut x = r(0);
    for _ in 0..=add_division_expr::MAX_DEPTH {
        x = b(B::Add, x, c(0));
    }
    assert!(recognize(&pattern(x, 0x2492492492492493, 2, 0)).is_none());
    fn big(n: usize) -> Expr {
        if n == 1 {
            r(0)
        } else {
            b(B::Xor, big(n / 2), big(n - n / 2))
        }
    }
    assert!(
        recognize(&pattern(
            big(add_division_expr::MAX_NODES),
            0x2492492492492493,
            2,
            0
        ))
        .is_none()
    );
    const {
        assert!(add_division_expr::MAX_WORK >= add_division_expr::MAX_NODES);
    }
}
#[test]
fn pure_select_value_borrows_complete_syntax_and_matches_original_ir() {
    let x = Expr::select(
        b(B::Ult, r(0), r(1)),
        b(B::Add, r(0), r(2)),
        b(B::And, r(2), c(0xffffffff)),
    );
    let e = pattern(x, 0x2492492492492493, 2, 7);
    let v = recognize(&e).unwrap();
    let p = Program::new(
        0,
        3,
        vec![IrInstruction {
            address: 0,
            size: 1,
            assignments: vec![],
            control: Control::Return(e.clone()),
        }],
    )
    .unwrap();
    for n in inputs(7).into_iter().step_by(31) {
        let rs = [n, n.rotate_left(7), !n];
        assert_eq!(p.execute(&rs, 1).unwrap().value, eval(v.value, &rs) / 7);
    }
}
#[test]
fn native_c11_raw_kernel_and_division_agree_at_o0_o2_with_ubsan() {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("target/add-division/native");
    std::fs::create_dir_all(&dir).unwrap();
    let mut source = String::from(
        r#"
#include <stdint.h>
#include <stdio.h>
#include <inttypes.h>
static uint64_t high(uint64_t a,uint64_t b){uint64_t a0=a&UINT64_C(0xffffffff),a1=a>>32,b0=b&UINT64_C(0xffffffff),b1=b>>32;uint64_t low=a0*b0,t=a1*b0+(low>>32),mid=(t&UINT64_C(0xffffffff))+a0*b1;return a1*b1+(t>>32)+(mid>>32);}
int main(void){uint64_t x;while(scanf("%" SCNu64,&x)==1){
"#,
    );
    for (d, s) in CASES {
        let m = multiplier(d, s);
        writeln!(source,"{{uint64_t t=high(x,UINT64_C({m}));printf(\"%\" PRIu64 \" %\" PRIu64 \" \",(t+((x-t)>>1))>>{s},x/UINT64_C({d}));}}").unwrap();
    }
    source.push_str("putchar('\\n');}return 0;}\n");
    let path = dir.join("add-division.c");
    std::fs::write(&path, source).unwrap();
    let xs: Vec<_> = inputs(7).into_iter().step_by(3).collect();
    let input = xs.iter().map(u64::to_string).collect::<Vec<_>>().join("\n") + "\n";
    let expected: Vec<Vec<u64>> = xs
        .iter()
        .map(|x| {
            CASES
                .into_iter()
                .flat_map(|(d, s)| {
                    let m = multiplier(d, s);
                    assert_eq!(extended_oracle(*x, m, s), *x / d);
                    [kernel(*x, m, s), *x / d]
                })
                .collect()
        })
        .collect();
    std::fs::write(dir.join("inputs.txt"), &input).unwrap();
    for opt in ["-O0", "-O2"] {
        for sanitize in [false, true] {
            let binary = dir.join(format!("add-division{opt}-{sanitize}"));
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
            let result = cmd.arg(&path).arg("-o").arg(&binary).output().unwrap();
            assert!(
                result.status.success(),
                "{}",
                String::from_utf8_lossy(&result.stderr)
            );
            assert_eq!(
                native::run_fields(&binary, &input, CASES.len() * 2),
                expected
            );
        }
    }
    println!("native {}inputs x9pairs x4builds", xs.len());
}

#[test]
fn actual_divide_seven_fixture_is_exposed_after_reduction_without_changing_ir() {
    let out = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("target/add-division/fixture");
    std::fs::create_dir_all(&out).unwrap();
    let source = out.join("seven.c");
    std::fs::write(&source,"#include <stdint.h>\nuint64_t fixture(uint64_t state[4]) {uint64_t x=state[0],q=x/UINT64_C(7),r=x%UINT64_C(7);state[1]=q;state[2]=r;return q^r;}\n").unwrap();
    let states: Vec<_> = inputs(7)
        .into_iter()
        .step_by(31)
        .map(|x| {
            [
                x,
                0xaaaa_aaaa_aaaa_aaaa,
                0xbbbb_bbbb_bbbb_bbbb,
                x.rotate_right(17),
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
    fn deps(e: &Expr) -> BTreeSet<usize> {
        let mut s = vec![e];
        let mut out = BTreeSet::new();
        while let Some(e) = s.pop() {
            match e {
                Expr::Register(r) => {
                    out.insert(r.0);
                }
                Expr::Binary(_, a, b) => s.extend([&**a, &**b]),
                Expr::Select {
                    condition,
                    taken,
                    not_taken,
                } => s.extend([&**condition, &**taken, &**not_taken]),
                Expr::Load { address, .. } => s.push(address),
                _ => {}
            }
        }
        out
    }
    fn visit(e: &Expr, count: &mut usize) {
        if let Some(v) = recognize(e) {
            assert_eq!(v.divisor, 7);
            assert_eq!(deps(e), deps(v.value));
            assert!(validate(e, &v));
            *count += 1;
            return;
        }
        match e {
            Expr::Binary(_, a, b) => {
                visit(a, count);
                visit(b, count)
            }
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => {
                visit(condition, count);
                visit(taken, count);
                visit(not_taken, count)
            }
            Expr::Load { address, .. } => visit(address, count),
            _ => {}
        }
    }
    let mut report = String::new();
    for opt in ["-O0", "-O2"] {
        let object = out.join(format!("seven{opt}.o"));
        let harness = out.join(format!("harness{opt}.o"));
        let binary = out.join(format!("seven{opt}"));
        native::object(&source, &object, opt, "fixture");
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
        let width = |r| {
            if reduced.parameters().contains(&r) {
                Width::U64
            } else {
                widths.width(r)
            }
        };
        let mut count = 0;
        for i in selected.instructions() {
            for a in &i.assignments {
                visit(
                    &nirvana::presentation::normalize(&a.value, width),
                    &mut count,
                );
            }
            match &i.control {
                Control::Return(e) | Control::Branch { condition: e, .. } => {
                    visit(&nirvana::presentation::normalize(e, width), &mut count)
                }
                _ => {}
            }
        }
        if opt == "-O2" {
            assert_eq!(count, 1);
        }
        writeln!(
            report,
            "{opt} normalizedcandidates{count}, nativecases{}",
            states.len()
        )
        .unwrap();
        for (state, observed) in states.iter().zip(native) {
            let mut registers: Vec<_> = (0..f.program.register_count())
                .map(|r| 0xfedc_ba98_7654_3210_u64 ^ (r as u64))
                .collect();
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
            let q = state[0] / 7;
            let r = state[0] % 7;
            assert_eq!(observed, vec![q ^ r, state[0], q, r, state[3]]);
            assert_eq!(raw.value, q ^ r);
            for (i, x) in [state[0], q, r, state[3]].iter().enumerate() {
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
    std::fs::write(out.join("adoption.txt"), &report).unwrap();
    print!("{report}");
}

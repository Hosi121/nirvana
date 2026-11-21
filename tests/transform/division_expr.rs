//! Arithmetic and native-C oracles for the borrowed division certificate.
use crate::support::native;
use nirvana::{division_expr, ir};

use division_expr::{DivisionEvidence, DivisionView, recognize, validate};
use ir::{BinaryOp as B, Control, Expr, IrInstruction, Program, Width};
use std::collections::BTreeSet;
use std::fmt::Write as _;
use std::process::Command;

use crate::support::ir::c;
use crate::support::ir::r;
fn b(op: B, left: Expr, right: Expr) -> Expr {
    Expr::binary(op, left, right)
}
fn magic(value: Expr, m: u64, s: u32, commute: bool, explicit: bool) -> Expr {
    let value = if commute {
        b(B::UMulHigh, c(m), value)
    } else {
        b(B::UMulHigh, value, c(m))
    };
    if explicit {
        b(B::Shr, value, c(u64::from(s)))
    } else {
        assert_eq!(s, 0);
        value
    }
}
const TABLE: [(u64, u64, u32); 10] = [
    (2, 0x8000_0000_0000_0000, 0),
    (3, 0xaaaa_aaaa_aaaa_aaab, 1),
    (4, 0x4000_0000_0000_0000, 0),
    (5, 0xcccc_cccc_cccc_cccd, 2),
    (6, 0xaaaa_aaaa_aaaa_aaab, 2),
    (8, 0x2000_0000_0000_0000, 0),
    (9, 0xe38e_38e3_8e38_e38f, 3),
    (10, 0xcccc_cccc_cccc_cccd, 3),
    (1 << 63, 2, 0),
    (5 << 61, 0xcccc_cccc_cccc_cccd, 63),
];
fn inputs(d: u64) -> Vec<u64> {
    let mut values = BTreeSet::from([
        0,
        1,
        2,
        3,
        d - 1,
        d,
        d.saturating_add(1),
        1 << 31,
        1 << 32,
        1 << 63,
        u64::MAX,
    ]);
    for q in [0, 1, 2, 3, 7, 255, u64::MAX / d - 1, u64::MAX / d] {
        if let Some(x) = q.checked_mul(d) {
            for x in [x.checked_sub(1), Some(x), x.checked_add(1)]
                .into_iter()
                .flatten()
            {
                values.insert(x);
            }
        }
    }
    let mut seed = 0x4d59_5df4_d0f3_3173_u64;
    for _ in 0..4096 {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        values.insert(seed);
    }
    values.into_iter().collect()
}
fn eval(expr: &Expr, registers: &[u64]) -> u64 {
    match expr {
        Expr::Unary(op, value) => crate::support::ir::unary_value(*op, eval(value, registers)),
        Expr::Const(x) => *x,
        Expr::Register(r) => registers[r.0],
        Expr::Binary(op, a, z) => {
            let a = eval(a, registers);
            let z = eval(z, registers);
            match op {
                B::Insert { start, width } => {
                    crate::support::ir::insert_value(*start, *width, a, z)
                }
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
        Expr::Select {
            condition,
            taken,
            not_taken,
        } => {
            if eval(condition, registers) != 0 {
                eval(taken, registers)
            } else {
                eval(not_taken, registers)
            }
        }
        Expr::Load { .. } => panic!("pure arithmetic test contains Load"),
    }
}
fn deps(expr: &Expr) -> BTreeSet<usize> {
    let mut pending = vec![expr];
    let mut result = BTreeSet::new();
    while let Some(e) = pending.pop() {
        match e {
            Expr::Register(r) => {
                result.insert(r.0);
            }
            Expr::Unary(_, value) => pending.push(value),
            Expr::Binary(_, a, z) => pending.extend([&**a, &**z]),
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => pending.extend([&**condition, &**taken, &**not_taken]),
            Expr::Load { address, .. } => pending.push(address),
            _ => {}
        }
    }
    result
}

#[test]
fn accepted_tables_match_independent_u128_and_division_at_boundaries_and_seeded_values() {
    let mut checks = 0;
    for (d, m, s) in TABLE {
        for commute in [false, true] {
            for explicit in if s == 0 {
                vec![false, true]
            } else {
                vec![true]
            } {
                let expr = magic(r(0), m, s, commute, explicit);
                let view = recognize(&expr).unwrap();
                assert_eq!(view.divisor, d);
                assert!(validate(&expr, &view));
                let before = expr.clone();
                for x in inputs(d) {
                    let high = ((u128::from(x) * u128::from(m)) >> (64 + s)) as u64;
                    assert_eq!(high, x / d, "d{d} m{m} s{s} x{x}");
                    assert_eq!(eval(&expr, &[x]), x / d);
                    checks += 1;
                }
                assert_eq!(expr, before);
            }
        }
    }
    println!("{checks} independent u128/raw-tree/division checks");
}

#[test]
fn generated_reciprocal_constants_are_checked_before_concrete_replay() {
    let mut accepted = 0;
    for d in 2..=256_u64 {
        let mut found = false;
        for s in 0..=63 {
            let power = 1_u128 << (64 + s);
            let m = power.div_ceil(u128::from(d));
            let Ok(m) = u64::try_from(m) else { continue };
            let expr = magic(r(0), m, s, false, true);
            if let Some(view) = recognize(&expr) {
                assert_eq!(view.divisor, d);
                assert!(validate(&expr, &view));
                for x in inputs(d).into_iter().step_by(17) {
                    assert_eq!(eval(&expr, &[x]), x / d);
                }
                accepted += 1;
                found = true;
                break;
            }
        }
        if [3, 5, 6, 9, 10].contains(&d) {
            assert!(found, "required divisor{d}");
        }
    }
    assert!(accepted > 100);
    println!("certified{accepted} divisors in2..256; other valid formulas may decline");
}

#[test]
fn value_is_borrowed_pure_complex_and_has_exact_original_dependencies() {
    let value = Expr::select(
        b(B::Ult, r(usize::MAX), c(7)),
        b(B::Add, r(4), c(u64::MAX)),
        b(B::And, r(9), c(0xffff)),
    );
    let expr = magic(value, 0xcccc_cccc_cccc_cccd, 3, true, true);
    let view = recognize(&expr).unwrap();
    assert_eq!(deps(&expr), deps(view.value));
    assert_eq!(deps(view.value), BTreeSet::from([4, 9, usize::MAX]));
    let Expr::Binary(_, product, _) = &expr else {
        panic!()
    };
    let Expr::Binary(_, _, value) = &**product else {
        panic!()
    };
    assert!(std::ptr::eq(view.value, &**value));
    let clone = view.value.clone();
    assert!(!validate(
        &expr,
        &DivisionView {
            value: &clone,
            ..view
        }
    ));
}

#[test]
fn independent_validator_rejects_every_forged_certificate_field_and_other_tree() {
    let expr = magic(r(0), 0xcccc_cccc_cccc_cccd, 3, false, true);
    let view = recognize(&expr).unwrap();
    for candidate in [
        DivisionView { divisor: 0, ..view },
        DivisionView { divisor: 1, ..view },
        DivisionView { divisor: 9, ..view },
        DivisionView {
            divisor: u64::MAX,
            ..view
        },
        DivisionView {
            evidence: DivisionEvidence {
                multiplier: 0,
                ..view.evidence
            },
            ..view
        },
        DivisionView {
            evidence: DivisionEvidence {
                multiplier: view.evidence.multiplier - 1,
                ..view.evidence
            },
            ..view
        },
        DivisionView {
            evidence: DivisionEvidence {
                shift: 2,
                ..view.evidence
            },
            ..view
        },
        DivisionView {
            evidence: DivisionEvidence {
                shift: 64,
                ..view.evidence
            },
            ..view
        },
        DivisionView {
            evidence: DivisionEvidence {
                shift: u32::MAX,
                ..view.evidence
            },
            ..view
        },
        DivisionView {
            evidence: DivisionEvidence {
                excess: 0,
                ..view.evidence
            },
            ..view
        },
        DivisionView {
            evidence: DivisionEvidence {
                upper_bound: u128::MAX,
                ..view.evidence
            },
            ..view
        },
    ] {
        assert!(!validate(&expr, &candidate), "{candidate:?}");
    }
    let wrong = magic(r(0), 0xcccc_cccc_cccc_cccd, 2, false, true);
    assert!(!validate(&wrong, &view));
    assert!(!validate(&Expr::load(r(0), Width::U64), &view));
}

#[test]
fn wrong_magic_or_shift_has_concrete_under_or_overestimation_counterexamples() {
    let m = 0xaaaa_aaaa_aaaa_aaab;
    let under = magic(r(0), m - 1, 1, false, true);
    assert!(recognize(&under).is_none());
    assert_ne!(eval(&under, &[3]), 3 / 3);
    let over = magic(r(0), m, 0, false, true);
    assert!(recognize(&over).is_none());
    assert_ne!(eval(&over, &[2]), 2 / 3);
    let other = magic(r(0), m, 2, false, true);
    let view = recognize(&other).unwrap();
    assert_eq!(view.divisor, 6);
    assert_ne!(eval(&other, &[3]), 3 / 3);
    // Round-up alone is insufficient: ceil(2^64/3) is wrong near MAX.
    let rounded = magic(r(0), 0x5555_5555_5555_5556, 0, false, false);
    assert!(recognize(&rounded).is_none());
    let x = u64::MAX - 1;
    assert_ne!(eval(&rounded, &[x]), x / 3);
}

#[test]
fn unrelated_shapes_counts_and_unsupported_low_product_decline() {
    let m = 0xcccc_cccc_cccc_cccd;
    for expr in [
        c(7),
        r(0),
        b(B::Mul, r(0), c(m)),
        b(B::Shr, b(B::Mul, r(0), c(m)), c(3)),
        magic(r(0), 0, 3, false, true),
        magic(r(0), 1, 0, false, false),
        b(B::Shr, b(B::UMulHigh, r(0), r(1)), c(3)),
        b(B::Shr, b(B::UMulHigh, r(0), c(m)), r(1)),
        b(B::Shr, b(B::UMulHigh, r(0), c(m)), c(64)),
        b(B::Shr, b(B::UMulHigh, r(0), c(m)), c(67)),
        b(B::Shr, b(B::UMulHigh, r(0), c(m)), c(u64::MAX)),
        b(B::Shl, b(B::UMulHigh, r(0), c(m)), c(3)),
    ] {
        assert!(recognize(&expr).is_none(), "{expr:?}");
    }
}

#[test]
fn every_syntactic_load_including_unchosen_select_arms_declines() {
    let bad = Expr::load(c(u64::MAX), Width::U8);
    for value in [
        bad.clone(),
        Expr::select(c(1), r(0), bad.clone()),
        Expr::select(bad.clone(), r(0), r(0)),
        b(B::Mul, c(0), bad),
    ] {
        assert!(recognize(&magic(value, 0xcccc_cccc_cccc_cccd, 3, false, true)).is_none());
    }
    let expr = b(
        B::Shr,
        b(B::UMulHigh, r(0), c(0xcccc_cccc_cccc_cccd)),
        Expr::select(c(1), c(3), Expr::load(r(1), Width::U64)),
    );
    assert!(recognize(&expr).is_none());
}

#[test]
fn whole_tree_bounds_precede_matching_and_validation() {
    let mut value = r(0);
    for _ in 0..division_expr::MAX_DEPTH {
        value = b(B::Add, c(0), value);
    }
    assert!(recognize(&magic(value, 0xcccc_cccc_cccc_cccd, 3, false, true)).is_none());
    fn balanced(n: usize) -> Expr {
        if n == 1 {
            c(0)
        } else {
            b(B::Add, balanced(n / 2), balanced(n - n / 2))
        }
    }
    let expr = magic(
        balanced(division_expr::MAX_NODES),
        0xcccc_cccc_cccc_cccd,
        3,
        false,
        true,
    );
    assert!(recognize(&expr).is_none());
    let valid = magic(r(0), 0xcccc_cccc_cccc_cccd, 3, false, true);
    let view = recognize(&valid).unwrap();
    assert!(!validate(&expr, &view));
    const {
        assert!(division_expr::MAX_WORK >= division_expr::MAX_NODES);
    }
}

#[test]
fn raw_program_execution_agrees_with_view_for_total_complex_values() {
    for (d, m, s) in TABLE {
        let expr = magic(
            Expr::select(
                b(B::And, r(1), c(1)),
                b(B::Add, r(0), r(2)),
                b(B::Xor, r(0), r(2)),
            ),
            m,
            s,
            false,
            true,
        );
        let view = recognize(&expr).unwrap();
        let program = Program::new(
            0,
            3,
            vec![IrInstruction {
                address: 0,
                size: 1,
                assignments: vec![],
                control: Control::Return(expr.clone()),
            }],
        )
        .unwrap();
        for x in inputs(d).into_iter().step_by(43) {
            for z in [0, 1, u64::MAX] {
                let registers = [x, z, !x];
                assert_eq!(
                    program.execute(&registers, 1).unwrap().value,
                    eval(view.value, &registers) / d
                );
            }
        }
    }
}

#[test]
fn native_c11_division_display_matches_magic_and_u128_at_o0_o2_and_ubsan() {
    let out = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("target/division-expr/native");
    std::fs::create_dir_all(&out).unwrap();
    let mut source = String::from(
        r#"
#include <stdint.h>
#include <stdio.h>
#include <inttypes.h>
static uint64_t high(uint64_t a,uint64_t b){
    uint64_t a0=a&UINT64_C(0xffffffff),a1=a>>32,b0=b&UINT64_C(0xffffffff),b1=b>>32;
    uint64_t low=a0*b0,t=a1*b0+(low>>32),middle=(t&UINT64_C(0xffffffff))+a0*b1;
    return a1*b1+(t>>32)+(middle>>32);
}
int main(void){uint64_t x;while(scanf("%" SCNu64,&x)==1){
"#,
    );
    for (d, m, s) in TABLE {
        writeln!(
            source,
            "printf(\"%\" PRIu64 \" %\" PRIu64 \" \",high(x,UINT64_C({m}))>>{s},x/UINT64_C({d}));"
        )
        .unwrap();
    }
    source.push_str("putchar('\\n');}return 0;}\n");
    let path = out.join("division.c");
    std::fs::write(&path, source).unwrap();
    let values: Vec<_> = inputs(10).into_iter().step_by(7).collect();
    let input = values
        .iter()
        .map(u64::to_string)
        .collect::<Vec<_>>()
        .join("\n")
        + "\n";
    let expected: Vec<Vec<u64>> = values
        .iter()
        .map(|x| {
            TABLE
                .into_iter()
                .flat_map(|(d, m, s)| {
                    let high = ((u128::from(*x) * u128::from(m)) >> (64 + s)) as u64;
                    assert_eq!(high, *x / d);
                    [high, *x / d]
                })
                .collect()
        })
        .collect();
    std::fs::write(out.join("inputs.txt"), &input).unwrap();
    for opt in ["-O0", "-O2"] {
        for sanitize in [false, true] {
            let binary = out.join(format!("division{opt}-{sanitize}"));
            let mut command = Command::new("cc");
            command.args([
                "-std=c11",
                "-Wall",
                "-Wextra",
                "-Werror",
                "-pedantic",
                "-fno-lto",
                opt,
            ]);
            if sanitize {
                command.args(["-fsanitize=undefined", "-fno-sanitize-recover=undefined"]);
            }
            let result = native::compile_output(command.arg(&path).arg("-o").arg(&binary));
            assert!(
                result.status.success(),
                "{}",
                String::from_utf8_lossy(&result.stderr)
            );
            assert_eq!(
                native::run_fields(&binary, &input, TABLE.len() * 2),
                expected,
                "{opt},UBSan{sanitize}"
            );
        }
    }
    println!("{} native C11 input rows x10 pairs x4 builds", values.len());
}

#[test]
fn actual_division_fixture_keeps_native_ir_results_and_adopts_only_pure_reduced_trees() {
    let out = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("target/division-expr/fixture");
    std::fs::create_dir_all(&out).unwrap();
    let values: Vec<_> = inputs(10).into_iter().step_by(97).collect();
    let states: Vec<_> = values
        .iter()
        .enumerate()
        .map(|(i, x)| {
            [
                *x,
                0xaaaa_aaaa_aaaa_aaaa,
                0xbbbb_bbbb_bbbb_bbbb,
                if i & 1 == 0 { u64::MAX } else { *x },
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
    fn visit(e: &Expr, views: &mut usize) {
        if let Some(view) = recognize(e) {
            assert_eq!(view.divisor, 10);
            assert!(validate(e, &view));
            assert_eq!(deps(e), deps(view.value));
            *views += 1;
            return;
        }
        match e {
            Expr::Unary(_, value) => visit(value, views),
            Expr::Binary(_, a, z) => {
                visit(a, views);
                visit(z, views)
            }
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => {
                visit(condition, views);
                visit(taken, views);
                visit(not_taken, views)
            }
            Expr::Load { address, .. } => visit(address, views),
            _ => {}
        }
    }
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
        let lifted =
            nirvana::frontend::lift_elf(&std::fs::read(&object).unwrap(), "fixture").unwrap();
        let before = lifted.program.instructions().to_vec();
        let reduced = nirvana::reduce::reduce(&lifted.program).unwrap();
        let split = nirvana::web::split(reduced.program()).unwrap();
        nirvana::web_verify::validate(reduced.program(), split.program()).unwrap();
        let widths = nirvana::value_width::ValueWidths::analyze(split.program());
        let width = |reg| {
            if reduced.parameters().contains(&reg) {
                Width::U64
            } else {
                widths.width(reg)
            }
        };
        let mut candidates = 0;
        for instruction in split.program().instructions() {
            for assignment in &instruction.assignments {
                visit(
                    &nirvana::presentation::normalize(&assignment.value, width),
                    &mut candidates,
                );
            }
            match &instruction.control {
                Control::Return(e) | Control::Branch { condition: e, .. } => {
                    visit(&nirvana::presentation::normalize(e, width), &mut candidates)
                }
                _ => {}
            }
        }
        assert!(
            candidates > 0,
            "actual{opt} compiler did not expose a supported pure high-multiply shape"
        );
        writeln!(
            counts,
            "{opt} normalized-reduced candidates{candidates}, native rows{}",
            states.len()
        )
        .unwrap();
        for (state, actual) in states.iter().zip(native) {
            let mut registers = vec![0; lifted.program.register_count()];
            registers[nirvana::x86::RDI] = 4096;
            registers[nirvana::x86::RSP] = 65536;
            let mut memory: Vec<_> = (0usize..65536)
                .map(|i| i.wrapping_mul(29).wrapping_add(7) as u8)
                .collect();
            for (i, value) in state.iter().enumerate() {
                memory[4096 + i * 8..4096 + i * 8 + 8].copy_from_slice(&value.to_le_bytes());
            }
            let ir = lifted
                .program
                .execute_with_memory(&registers, 0, &memory, 1000)
                .unwrap();
            let compact = reduced
                .execute_with_memory(&registers, 0, &memory, 1000)
                .unwrap();
            assert_eq!(compact.value, ir.value);
            assert_eq!(compact.memory, ir.memory);
            assert_eq!(compact.trace, ir.trace);
            let q = state[0] / 10;
            let rem = state[0] % 10;
            let word = state[3] as u32;
            let narrow = u64::from(word / 10) + u64::from(word % 10);
            let expected = [q ^ (rem << 8) ^ narrow, state[0], q, rem, narrow];
            assert_eq!(actual, expected);
            assert_eq!(ir.value, expected[0]);
            for (i, expected) in expected[1..].iter().enumerate() {
                assert_eq!(
                    u64::from_le_bytes(
                        ir.memory[4096 + i * 8..4096 + i * 8 + 8]
                            .try_into()
                            .unwrap()
                    ),
                    *expected
                );
            }
        }
        assert_eq!(lifted.program.instructions(), before);
    }
    std::fs::write(out.join("adoption.txt"), &counts).unwrap();
    print!("{counts}");
}

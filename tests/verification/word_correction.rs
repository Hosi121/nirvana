//! Integer obligations supplement the bit-vector projection checks and actual
//! matcher/IR execution. The negative domain keeps the signed minimum.
use crate::support::word_reciprocals::{WIDTHS, cases, corrected_kernel, magic};
use nirvana::{
    ir::{Control, IrInstruction, Program, Width},
    word_signed_division,
};

#[test]
#[ignore = "requires Z3; set NIRVANA_Z3"]
fn extended_word_results_fit_the_signed_word_for_every_admitted_divisor() {
    let solver = std::env::var("NIRVANA_Z3").unwrap_or_else(|_| "z3".into());
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("target/verification/word-extended-results");
    std::fs::create_dir_all(&root).unwrap();
    for width in WIDTHS {
        let half = 1u64 << (width.bits() - 1);
        let base = half * 2;
        // The magnitude equation characterizes Euclidean quotient/remainder.
        // Keep both signs arbitrary and include the signed minimum magnitude.
        let model = format!(
            r#"(set-logic QF_NIA)
(set-option :timeout 5000)
(declare-fun magnitude () Int)
(declare-fun divisor () Int)
(declare-fun quotient () Int)
(declare-fun remainder () Int)
(declare-fun quotient_negative () Bool)
(declare-fun remainder_negative () Bool)
(assert (and (<= 0 magnitude) (<= magnitude {half}) (<= 2 divisor) (< divisor {half})))
(assert (and (<= 0 quotient) (<= 0 remainder) (< remainder divisor)))
(assert (= magnitude (+ (* quotient divisor) remainder)))
(define-fun q () Int (ite quotient_negative (- quotient) quotient))
(define-fun r () Int (ite remainder_negative (- remainder) remainder))
(assert (or (distinct q (- (mod (+ q {half}) {base}) {half}))
            (distinct r (- (mod (+ r {half}) {base}) {half}))))
(check-sat)
"#
        );
        let file = root.join(format!("bits-{}.smt2", width.bits()));
        std::fs::write(&file, model).unwrap();
        let result = std::process::Command::new(&solver)
            .args(["-T:6", "-smt2"])
            .arg(&file)
            .output()
            .unwrap();
        std::fs::write(file.with_extension("out"), &result.stdout).unwrap();
        assert!(result.status.success());
        assert_eq!(String::from_utf8(result.stdout).unwrap().trim(), "unsat");
    }
    std::fs::write(root.join("result.json"),"{\"model\":\"word-extended-result-v1\",\"unsat\":3,\"divisors\":\"all magnitudes 2 <= d < signed half\"}\n").unwrap();
}

#[test]
#[ignore = "requires Z3; set NIRVANA_Z3"]
fn estimate_corrections_have_universal_integer_obligations_and_a_minimum_counterexample() {
    let solver = std::env::var("NIRVANA_Z3").unwrap_or_else(|_| "z3".into());
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("target/verification/word-correction");
    std::fs::create_dir_all(&root).unwrap();
    let mut profiles = 0;
    for width in WIDTHS {
        let bits = width.bits();
        let base = 1u64 << bits;
        let half = base / 2;
        let mut seen = std::collections::BTreeSet::new();
        for (d, shift) in cases(width) {
            for negative in [false, true] {
                let shift = if negative && d == 3 { 1 } else { shift };
                let signed_d = if negative { -d } else { d };
                if !seen.insert((signed_d, shift)) {
                    continue;
                }
                let expression = corrected_kernel(width, signed_d, shift, true, true);
                let view = word_signed_division::recognize(&expression).unwrap();
                assert_eq!(view.divisor, signed_d);
                let magnitude = magic(width, d, shift);
                let raw = if negative {
                    base - magnitude
                } else {
                    magnitude
                };
                let encoded = if raw >= half {
                    raw as i64 - base as i64
                } else {
                    raw as i64
                };
                let correction = if negative && encoded > 0 {
                    -1
                } else if !negative && encoded < 0 {
                    1
                } else {
                    0
                };
                let integer = |n: i64| {
                    if n < 0 {
                        format!("(- {})", n.unsigned_abs())
                    } else {
                        n.to_string()
                    }
                };
                let mut model =
                    include_str!("../models/word_estimate_correction.smt2.in").to_owned();
                for (key, value) in [
                    ("BASE", base.to_string()),
                    ("HALF", half.to_string()),
                    ("ENCODED", integer(encoded)),
                    ("CORRECTION", integer(correction)),
                    ("POSTPOWER", (1u64 << shift).to_string()),
                    ("DIVISOR", d.to_string()),
                    ("SIGNED_D", integer(signed_d)),
                    ("NEGATIVE", negative.to_string()),
                    ("PRODUCT_HALF", (1u128 << (2 * bits - 1)).to_string()),
                ] {
                    model = model.replace(&format!("@{key}@"), &value);
                }
                let file = root.join(format!("bits-{bits}-divisor-{signed_d}-shift-{shift}.smt2"));
                std::fs::write(&file, model).unwrap();
                let output = std::process::Command::new(&solver)
                    .args(["-T:25", "-smt2"])
                    .arg(&file)
                    .output()
                    .unwrap();
                let text = String::from_utf8(output.stdout).unwrap();
                std::fs::write(file.with_extension("out"), &text).unwrap();
                assert!(output.status.success(), "{text}");
                assert_eq!(
                    text.lines().collect::<Vec<_>>(),
                    ["unsat"; 5],
                    "{bits}/{signed_d}/{shift}: {text}"
                );
                profiles += 1;
            }
        }
    }
    assert_eq!(profiles, 66);
    let bad = "(set-logic QF_LIA)\n(declare-fun n () Int)\n(assert (= n (- 128)))\n(define-fun estimate () Int (div (* n (- 86)) 256))\n(define-fun actual () Int (+ estimate (ite (< estimate 0) 1 0)))\n(assert (distinct actual 42))\n(check-sat)\n(get-value (n actual))\n";
    let file = root.join("invalid-reversed-minimum.smt2");
    std::fs::write(&file, bad).unwrap();
    let output = std::process::Command::new(&solver)
        .arg(&file)
        .output()
        .unwrap();
    assert!(output.status.success());
    let text = String::from_utf8(output.stdout).unwrap();
    assert!(text.starts_with("sat\n"));
    std::fs::write(file.with_extension("out"), text).unwrap();
    let expression = corrected_kernel(Width::U8, -3, 0, true, false);
    assert!(word_signed_division::recognize(&expression).is_none());
    let program = Program::new(
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
    assert_eq!(program.execute(&[128 - 13], 1).unwrap().value, 43);
    let result = format!(
        "{{\"model\":\"word-estimate-correction-v2\",\"profiles\":{profiles},\"unsat\":{},\"sat_replayed\":1}}\n",
        profiles * 5
    );
    std::fs::write(root.join("result.json"), &result).unwrap();
    print!("{result}");
}

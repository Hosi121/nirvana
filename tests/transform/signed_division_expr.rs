use crate::support::ir::{c, r};
use crate::support::native;
use nirvana::ir::{BinaryOp as B, Control, Expr, IrInstruction, Program, Width};
use nirvana::signed_division_expr::{self as signed, SignedDivisionEvidence, SignedDivisionView};
use std::fmt::Write as _;

use crate::support::signed_reciprocals::KERNELS as TABLE;
fn b(op: B, a: Expr, z: Expr) -> Expr {
    Expr::binary(op, a, z)
}
fn kernel(value: Expr, m: u64, s: u32, negative: bool, commute: bool) -> Expr {
    let high = if commute {
        b(B::SMulHigh, c(m), value.clone())
    } else {
        b(B::SMulHigh, value.clone(), c(m))
    };
    let high = if m >> 63 != 0 {
        if commute {
            b(B::Add, value.clone(), high)
        } else {
            b(B::Add, high, value.clone())
        }
    } else {
        high
    };
    let estimate = if s == 0 {
        high
    } else {
        b(B::AShr, high, c(u64::from(s)))
    };
    let sign = b(B::AShr, value, c(63));
    if negative {
        b(B::Sub, sign, estimate)
    } else {
        b(B::Sub, estimate, sign)
    }
}
fn program(expression: Expr) -> Program {
    Program::new(
        0,
        2,
        vec![IrInstruction {
            address: 0,
            size: 1,
            assignments: vec![],
            control: Control::Return(expression),
        }],
    )
    .unwrap()
}
fn values(d: i64) -> Vec<u64> {
    let mut result = vec![
        0,
        1,
        2,
        63,
        64,
        65,
        i64::MAX as u64,
        i64::MIN as u64,
        u64::MAX,
        u64::MAX - 1,
    ];
    for q in [1, 2, 3, 99, i64::MAX / d] {
        let x = q * d;
        for offset in [-1, 0, 1] {
            if let Some(v) = x.checked_add(offset) {
                result.extend([v as u64, v.wrapping_neg() as u64]);
            }
        }
    }
    let mut seed = 0x811c_9dc5_94d0_49bbu64;
    for _ in 0..256 {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        result.push(seed);
    }
    result
}

#[test]
fn positive_negative_and_added_high_products_match_signed_quotients_and_remainders() {
    let mut compared = 0;
    for (d, m, s) in TABLE {
        for negative in [false, true] {
            let divisor = if negative { -d } else { d };
            for commute in [false, true] {
                let q = kernel(r(0), m, s, negative, commute);
                let view = signed::recognize(&q).unwrap();
                assert_eq!(view.divisor, divisor);
                assert!(signed::validate(&q, &view));
                let remainder = b(
                    B::Sub,
                    r(0),
                    if commute {
                        b(B::Mul, c(divisor as u64), q.clone())
                    } else {
                        b(B::Mul, q.clone(), c(divisor as u64))
                    },
                );
                let rv = signed::recognize_remainder(&remainder).unwrap();
                assert_eq!(rv.divisor, divisor);
                assert!(signed::validate_remainder(&remainder, &rv));
                let qp = program(q);
                let rp = program(remainder);
                for x in values(d) {
                    assert_eq!(
                        qp.execute(&[x, 0], 1).unwrap().value,
                        ((x as i64) / divisor) as u64
                    );
                    assert_eq!(
                        rp.execute(&[x, 0], 1).unwrap().value,
                        ((x as i64) % divisor) as u64
                    );
                    compared += 2;
                }
            }
        }
    }
    let q = kernel(r(0), TABLE[0].1, 0, false, false);
    let v = signed::recognize(&q).unwrap();
    assert_eq!(v.evidence.negative_bound, 1u128 << 64);
    assert!(v.evidence.positive_bound < (1u128 << 64));
    println!(
        "{compared} signed quotient/remainder comparisons across 20 divisors and commuted kernels"
    );
}

#[test]
fn evidence_borrows_the_actual_numerator_and_rejects_changed_fields() {
    let q = kernel(b(B::Add, r(0), c(17)), TABLE[3].1, 2, false, false);
    let v = signed::recognize(&q).unwrap();
    let copied = v.value.clone();
    let e = v.evidence;
    let wrong = [
        SignedDivisionView {
            value: &copied,
            ..v
        },
        SignedDivisionView { divisor: -10, ..v },
        SignedDivisionView { divisor: 0, ..v },
        SignedDivisionView {
            divisor: i64::MIN,
            ..v
        },
        SignedDivisionView {
            evidence: SignedDivisionEvidence {
                multiplier: e.multiplier - 1,
                ..e
            },
            ..v
        },
        SignedDivisionView {
            evidence: SignedDivisionEvidence {
                shift: e.shift + 1,
                ..e
            },
            ..v
        },
        SignedDivisionView {
            evidence: SignedDivisionEvidence {
                excess: e.excess + 1,
                ..e
            },
            ..v
        },
        SignedDivisionView {
            evidence: SignedDivisionEvidence {
                positive_bound: e.positive_bound + 1,
                ..e
            },
            ..v
        },
        SignedDivisionView {
            evidence: SignedDivisionEvidence {
                negative_bound: e.negative_bound - 1,
                ..e
            },
            ..v
        },
    ];
    for wrong in wrong {
        assert!(!signed::validate(&q, &wrong));
    }
    let rem = b(
        B::Sub,
        r(0),
        b(B::Mul, kernel(r(0), TABLE[3].1, 2, false, false), c(10)),
    );
    let rv = signed::recognize_remainder(&rem).unwrap();
    let value = rv.value.clone();
    assert!(!signed::validate_remainder(
        &rem,
        &signed::SignedRemainderView {
            value: &value,
            ..rv
        }
    ));
    assert!(!signed::validate_remainder(
        &rem,
        &signed::SignedRemainderView { divisor: -10, ..rv }
    ));
}

#[test]
fn missing_corrections_stale_values_loads_and_unmasked_counts_decline() {
    let m = TABLE[6].1;
    let wrong_add = b(
        B::Sub,
        b(B::AShr, b(B::SMulHigh, r(0), c(m)), c(3)),
        b(B::AShr, r(0), c(63)),
    );
    let wrong_value = b(
        B::Sub,
        b(B::AShr, b(B::SMulHigh, r(0), c(TABLE[3].1)), c(2)),
        b(B::AShr, r(1), c(63)),
    );
    let wrong_count = b(
        B::Sub,
        b(B::AShr, b(B::SMulHigh, r(0), c(TABLE[3].1)), c(64)),
        b(B::AShr, r(0), c(63)),
    );
    for e in [
        wrong_add,
        wrong_value,
        wrong_count,
        kernel(r(0), TABLE[3].1 - 1, 2, false, false),
        kernel(r(0), 0, 2, false, false),
    ] {
        assert!(signed::recognize(&e).is_none());
    }
    let value = Expr::select(c(0), Expr::load(r(0), Width::U8), r(0));
    assert!(signed::recognize(&kernel(value, TABLE[3].1, 2, false, false)).is_none());
    let bad_rem = b(
        B::Sub,
        r(1),
        b(B::Mul, kernel(r(0), TABLE[3].1, 2, false, false), c(10)),
    );
    assert!(signed::recognize_remainder(&bad_rem).is_none());
    let mut deep = r(0);
    for _ in 0..signed::MAX_DEPTH {
        deep = b(B::Add, deep, c(1));
    }
    assert!(signed::recognize(&kernel(deep, TABLE[3].1, 2, false, false)).is_none());
}

#[test]
fn selected_signed_operators_are_portable_c11_for_all_boundary_signs() {
    let scratch = native::Scratch::new();
    let mut source =
        String::from("#include <stdint.h>\n#include <inttypes.h>\n#include <stdio.h>\n");
    let mut names = Vec::new();
    let mut divisors = Vec::new();
    for (d, m, s) in TABLE {
        for negative in [false, true] {
            let d = if negative { -d } else { d };
            for rem in [false, true] {
                let q = kernel(r(0), m, s, negative, true);
                let expression = if rem {
                    b(B::Sub, r(0), b(B::Mul, q, c(d as u64)))
                } else {
                    q
                };
                let output = nirvana::readable::emit_readable_c(&program(expression)).unwrap();
                assert_eq!(output.parameters, vec![nirvana::ir::Reg(0)]);
                let helper = if rem {
                    "nirvana_srem64("
                } else {
                    "nirvana_sdiv64("
                };
                assert!(output.code.contains(helper), "{}", output.code);
                let prefix = format!("probe_{}_", names.len());
                source.push_str(&output.code.replace("nirvana_", &prefix));
                names.push(format!("{prefix}readable"));
                divisors.push((d, rem));
            }
        }
    }
    writeln!(
        source,
        "static uint64_t (*const probes[])(uint64_t)={{{}}};",
        names.join(",")
    )
    .unwrap();
    source.push_str("int main(void) { uint64_t x;while(scanf(\"%\" SCNu64,&x)==1) { for(unsigned i=0;i<sizeof(probes)/sizeof(probes[0]);++i) printf(\"%\" PRIu64 \" \",probes[i](x));putchar('\\n'); }return 0;}\n");
    let inputs = values(3);
    let mut text = String::new();
    let mut expected = Vec::new();
    for x in inputs {
        writeln!(text, "{x}").unwrap();
        expected.push(
            divisors
                .iter()
                .map(|&(d, rem)| {
                    if rem {
                        ((x as i64) % d) as u64
                    } else {
                        ((x as i64) / d) as u64
                    }
                })
                .collect::<Vec<_>>(),
        );
    }
    let file = scratch.0.join("signed.c");
    std::fs::write(&file, source).unwrap();
    for opt in ["-O0", "-O2"] {
        let binary = scratch.0.join(format!("signed{opt}"));
        native::compile_c(
            &file,
            &binary,
            &[
                opt,
                "-fsanitize=undefined",
                "-fno-sanitize-recover=undefined",
            ],
        );
        assert_eq!(native::run_fields(&binary, &text, names.len()), expected);
    }
}

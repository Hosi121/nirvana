use crate::support::ir::{c, r};
use crate::support::native;
use crate::support::word_reciprocals::{
    CASES, WIDTHS, b, cases as word_cases, kernel, magic, sext, word,
};
use nirvana::ir::{BinaryOp as B, Control, Expr, IrInstruction, Program, Width};
use nirvana::word_signed_division::{self as signed, Operation, View};
use std::fmt::Write as _;

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
fn signed_value(x: u64, width: Width) -> i64 {
    match width {
        Width::U8 => x as i8 as i64,
        Width::U16 => x as i16 as i64,
        Width::U32 => x as i32 as i64,
        Width::U64 => unreachable!(),
    }
}
fn values(width: Width) -> Vec<u64> {
    let top = 1u64 << (width.bits() - 1);
    let mut result = vec![
        0,
        1,
        2,
        top - 1,
        top,
        top + 1,
        width.mask(),
        u64::MAX,
        1 << 63,
    ];
    for (d, _) in CASES {
        for q in [1, 2, 3, (top - 1) / d as u64] {
            for n in [q * d as u64 - 1, q * d as u64, q * d as u64 + 1] {
                result.extend([n, 0u64.wrapping_sub(n)]);
            }
        }
    }
    let mut seed = 0xa342_7381_cafe_9317u64;
    for _ in 0..512 {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        result.push(seed);
    }
    if width == Width::U8 {
        result.extend(0..=255);
    }
    result
}
fn remainder(q: Expr, d: i64, width: Width, strength: bool) -> Expr {
    let product = if strength {
        let power = d.unsigned_abs().next_power_of_two();
        let aligned = b(
            B::And,
            b(B::Shl, q.clone(), c(u64::from(power.ilog2()))),
            c(width.mask() & !(power - 1)),
        );
        let positive = b(B::Sub, aligned, b(B::Mul, q, c(power - d.unsigned_abs())));
        if d < 0 {
            b(B::Sub, c(0), positive)
        } else {
            positive
        }
    } else {
        b(B::Mul, q, c(d as u64))
    };
    word(b(B::Sub, r(0), product), width)
}

#[test]
fn explicit_words_recover_all_signed_boundaries_and_strength_reduced_remainders() {
    let mut compared = 0;
    for width in WIDTHS {
        for (d, s) in word_cases(width) {
            for negative in [false, true] {
                let d = if negative { -d } else { d };
                for split in [false, true] {
                    for commute in [false, true] {
                        let q = kernel(width, d, s, split, commute);
                        let view = signed::recognize(&q).unwrap_or_else(|| {
                            panic!("{width:?}/{d}/{s}/{split}/{commute}: {q:?}")
                        });
                        assert_eq!(
                            (view.width, view.divisor, view.operation),
                            (width, d, Operation::Quotient)
                        );
                        assert!(signed::validate(&q, &view));
                        for strength in [false, true] {
                            let rem = remainder(q.clone(), d, width, strength);
                            let v = signed::recognize(&rem).unwrap();
                            assert_eq!(
                                (v.width, v.divisor, v.operation),
                                (width, d, Operation::Remainder)
                            );
                            assert!(signed::validate(&rem, &v));
                            let qp = program(q.clone());
                            let rp = program(rem);
                            for x in values(width) {
                                let n = signed_value(x, width);
                                assert_eq!(
                                    qp.execute(&[x, 0], 1).unwrap().value,
                                    (n / d) as u64 & width.mask(),
                                    "{width:?}/{d}/{x}"
                                );
                                assert_eq!(
                                    rp.execute(&[x, 0], 1).unwrap().value,
                                    (n % d) as u64 & width.mask()
                                );
                                compared += 2;
                            }
                        }
                    }
                }
            }
        }
    }
    println!("{compared} independent word quotient/remainder observations");
}

#[test]
fn views_bind_every_field_to_the_original_word_and_complete_source() {
    let e = kernel(Width::U32, 7, 2, true, false);
    let v = signed::recognize(&e).unwrap();
    let copied = v.value.clone();
    let copied_product = v.product.clone();
    let evidence = v.evidence;
    let wrong = [
        View {
            product: &copied_product,
            ..v
        },
        View {
            value: &copied,
            ..v
        },
        View {
            width: Width::U16,
            ..v
        },
        View { divisor: -7, ..v },
        View {
            operation: Operation::Remainder,
            ..v
        },
        View {
            evidence: signed::Evidence {
                multiplier: evidence.multiplier - 1,
                ..evidence
            },
            ..v
        },
        View {
            evidence: signed::Evidence {
                shift: evidence.shift + 1,
                ..evidence
            },
            ..v
        },
        View {
            evidence: signed::Evidence {
                excess: evidence.excess + 1,
                ..evidence
            },
            ..v
        },
        View {
            evidence: signed::Evidence {
                positive_bound: evidence.positive_bound + 1,
                ..evidence
            },
            ..v
        },
        View {
            evidence: signed::Evidence {
                negative_bound: evidence.negative_bound - 1,
                ..evidence
            },
            ..v
        },
    ];
    for wrong in wrong {
        assert!(!signed::validate(&e, &wrong));
    }
    let Expr::Binary(B::And, low, _) = e.clone() else {
        panic!()
    };
    assert!(signed::recognize(&low).is_none());
    for width in WIDTHS {
        let bits = u64::from(width.bits());
        let m = magic(width, 5, 1);
        let bad = word(
            b(
                B::Sub,
                b(B::Shr, b(B::Mul, sext(r(0), width), c(m)), c(bits + 1)),
                b(B::AShr, sext(r(0), width), c(bits - 1)),
            ),
            width,
        );
        assert_eq!(
            signed::recognize(&bad).is_some(),
            width != Width::U32,
            "logical shift is valid only while the sign fill stays above the low word"
        );
        let mut changed = kernel(width, 7, 2, true, false);
        fn mutate(e: &mut Expr) {
            match e {
                Expr::Const(m) if *m > u32::MAX as u64 => *m &= u32::MAX as u64,
                Expr::Unary(_, v) => mutate(v),
                Expr::Binary(_, a, b) => {
                    mutate(a);
                    mutate(b)
                }
                _ => {}
            }
        }
        if width == Width::U32 {
            mutate(&mut changed);
            assert!(signed::recognize(&changed).is_none());
        }
        fn replace(e: &mut Expr, value: &Expr) {
            match e {
                Expr::Register(_) => *e = value.clone(),
                Expr::Unary(_, v) => replace(v, value),
                Expr::Binary(_, a, b) => {
                    replace(a, value);
                    replace(b, value);
                }
                _ => {}
            }
        }
        for value in [
            Expr::load(r(0), Width::U8),
            Expr::select(c(0), Expr::load(r(0), Width::U8), r(0)),
        ] {
            let mut impure = kernel(width, 3, 0, false, false);
            replace(&mut impure, &value);
            assert!(signed::recognize(&impure).is_none());
        }
    }
    let mut deep = e;
    for _ in 0..signed::MAX_DEPTH {
        deep = word(deep, Width::U32);
    }
    assert!(signed::recognize(&deep).is_none());
}

#[test]
fn selected_word_helpers_match_signed_c_oracles_under_ubsan() {
    let scratch = native::Scratch::new();
    let mut source =
        String::from("#include <stdint.h>\n#include <inttypes.h>\n#include <stdio.h>\n");
    let mut names = Vec::new();
    let mut cases = Vec::new();
    for width in WIDTHS {
        for (d, s) in word_cases(width) {
            for negative in [false, true] {
                let d = if negative { -d } else { d };
                for rem in [false, true] {
                    let q = kernel(width, d, s, true, true);
                    let e = if rem { remainder(q, d, width, true) } else { q };
                    let out = nirvana::readable::emit_readable_c(&program(e)).unwrap();
                    let helper = if rem {
                        "nirvana_srem_word("
                    } else {
                        "nirvana_sdiv_word("
                    };
                    assert!(out.code.contains(helper), "{}", out.code);
                    let prefix = format!("probe_{}_", names.len());
                    source.push_str(&out.code.replace("nirvana_", &prefix));
                    names.push(format!("{prefix}readable"));
                    cases.push((width, d, rem));
                }
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
    let mut input = String::new();
    let mut expected = Vec::new();
    let mut inputs = values(Width::U32);
    inputs.extend(values(Width::U16));
    inputs.extend(values(Width::U8));
    for x in inputs {
        writeln!(input, "{x}").unwrap();
        expected.push(
            cases
                .iter()
                .map(|&(w, d, rem)| {
                    let x = signed_value(x, w);
                    (if rem { x % d } else { x / d }) as u64 & w.mask()
                })
                .collect::<Vec<_>>(),
        );
    }
    let file = scratch.0.join("word.c");
    std::fs::write(&file, source).unwrap();
    for opt in ["-O0", "-O2"] {
        let bin = scratch.0.join(format!("word{opt}"));
        native::compile_c(
            &file,
            &bin,
            &[
                opt,
                "-fsanitize=undefined",
                "-fno-sanitize-recover=undefined",
            ],
        );
        assert_eq!(native::run_fields(&bin, &input, names.len()), expected);
    }
    println!(
        "{} sanitized C word helper observations",
        2 * expected.len() * names.len()
    );
}

use crate::support::ir::{c, r};
use crate::support::word_reciprocals::{WIDTHS, b, cases, kernel, magic, sext, word};
use nirvana::ir::{BinaryOp as B, Width};
use nirvana::verify::{self, Solver, Verdict};

#[test]
#[ignore = "requires Z3; set NIRVANA_Z3"]
fn word_projection_and_shift_cuts_have_universal_bit_vector_checks() {
    let solver = Solver::new(std::env::var("NIRVANA_Z3").unwrap_or_else(|_| "z3".into()));
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("target/verification/word-projection");
    std::fs::create_dir_all(&root).unwrap();
    let mut proved = 0;
    let mut broken = 0;
    let mut check = |name: String, a: nirvana::ir::Expr, z: nirvana::ir::Expr, equal: bool| {
        let query = verify::pure_query(&a, &z).unwrap();
        std::fs::write(
            root.join(format!("{name}.smt2")),
            format!("{}(check-sat)\n", query.smt2()),
        )
        .unwrap();
        let verdict = solver.check_query(&query);
        std::fs::write(root.join(format!("{name}.out")), format!("{verdict:?}\n")).unwrap();
        if equal {
            assert_eq!(verdict, Verdict::EquivalentUnderModel, "{name}");
            proved += 1;
        } else {
            let Verdict::Counterexample(w) = verdict else {
                panic!("{name}: {verdict:?}")
            };
            assert_ne!(w.before, w.after);
            broken += 1;
        }
    };
    for width in WIDTHS {
        let bits = width.bits();
        let double = match width {
            Width::U8 => Width::U16,
            Width::U16 => Width::U32,
            Width::U32 => Width::U64,
            Width::U64 => unreachable!(),
        };
        for inner in WIDTHS
            .into_iter()
            .chain([Width::U64])
            .filter(|w| w.bits() >= bits)
        {
            check(
                format!("extension-{}-{}", bits, inner.bits()),
                word(sext(r(0), inner), width),
                word(r(0), width),
                true,
            );
        }
        for op in [B::Add, B::Sub, B::Mul, B::And, B::Or, B::Xor] {
            check(
                format!("ring-{bits}-{op:?}"),
                word(b(op, r(0), r(1)), width),
                word(b(op, word(r(0), width), word(r(1), width)), width),
                true,
            );
        }
        let product = sext(r(0), double);
        for count in [1, 2, bits - 1] {
            let shifted = b(B::Shl, r(0), c(u64::from(count)));
            let aligned = width.mask() & !((1u64 << count) - 1);
            check(
                format!("aligned-mask-{bits}-{count}"),
                word(shifted.clone(), width),
                word(b(B::And, shifted, c(aligned)), width),
                true,
            );
        }
        for shift in [0, 1, bits - 1] {
            check(
                format!("signed-cut-{bits}-{shift}"),
                word(
                    b(B::AShr, product.clone(), c(u64::from(bits + shift))),
                    width,
                ),
                word(
                    b(
                        B::AShr,
                        sext(
                            word(b(B::Shr, product.clone(), c(u64::from(bits))), width),
                            width,
                        ),
                        c(u64::from(shift)),
                    ),
                    width,
                ),
                true,
            );
        }
        check(
            format!("sign-{bits}"),
            word(b(B::AShr, sext(r(0), width), c(u64::from(bits - 1))), width),
            word(b(B::AShr, sext(r(0), width), c(63)), width),
            true,
        );
        if bits < 32 {
            check(
                format!("logical-fused-safe-{bits}"),
                word(b(B::AShr, product.clone(), c(u64::from(bits + 1))), width),
                word(b(B::Shr, product.clone(), c(u64::from(bits + 1))), width),
                true,
            );
        }
        check(
            format!("wrong-logical-fused-{bits}"),
            word(b(B::AShr, product.clone(), c(u64::from(65 - bits))), width),
            word(b(B::Shr, product, c(u64::from(65 - bits))), width),
            false,
        );
        check(
            format!("wrong-mask-before-right-{bits}"),
            word(b(B::AShr, sext(r(0), width), c(1)), width),
            word(b(B::AShr, word(r(0), width), c(1)), width),
            false,
        );
    }
    assert_eq!((proved, broken), (50, 6));
    println!(
        "{proved} universal projection/shift equivalences and {broken} IR-replayed SAT controls"
    );
}

#[test]
#[ignore = "requires Z3; set NIRVANA_Z3"]
fn signed_word_reciprocals_have_universal_integer_quotient_and_remainder_checks() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("target/verification/word-reciprocal");
    std::fs::create_dir_all(&root).unwrap();
    let solver = std::env::var("NIRVANA_Z3").unwrap_or_else(|_| "z3".into());
    let mut count = 0;
    for width in WIDTHS {
        for (d, s) in cases(width) {
            for negative in [false, true] {
                let signed_d = if negative { -d } else { d };
                let q = kernel(width, signed_d, s, false, false);
                let v = nirvana::word_signed_division::recognize(&q).unwrap();
                assert_eq!(v.divisor, signed_d);
                let bits = width.bits();
                let m = magic(width, d, s);
                let base = 1u64 << bits;
                let half = base / 2;
                let encoded = if m >= half {
                    format!("(- {})", base - m)
                } else {
                    m.to_string()
                };
                let model = include_str!("../models/signed_reciprocal.smt2.in")
                    .replace("@BASE@", &base.to_string())
                    .replace("@HALF@", &half.to_string())
                    .replace("@M@", &m.to_string())
                    .replace("@ENCODED@", &encoded)
                    .replace("@ADD@", if m >= half { "true" } else { "false" })
                    .replace("@NEGATE@", if negative { "true" } else { "false" })
                    .replace("@D@", &d.to_string())
                    .replace(
                        "@SIGNED_D@",
                        &if negative {
                            format!("(- {d})")
                        } else {
                            d.to_string()
                        },
                    )
                    .replace("@WRONG_M@", &(m - 1).to_string())
                    .replace("@POSTPOWER@", &(1u64 << s).to_string())
                    .replace("@POWER@", &(1u64 << (bits + s)).to_string());
                let file = root.join(format!("bits-{bits}-divisor-{signed_d}-shift-{s}.smt2"));
                std::fs::write(&file, model).unwrap();
                let output = std::process::Command::new(&solver)
                    .args(["-T:30", "-smt2"])
                    .arg(&file)
                    .output()
                    .unwrap();
                assert!(output.status.success());
                let text = String::from_utf8(output.stdout).unwrap();
                std::fs::write(file.with_extension("out"), &text).unwrap();
                let statuses: Vec<_> = text
                    .lines()
                    .filter(|s| matches!(*s, "sat" | "unsat" | "unknown"))
                    .collect();
                assert_eq!(
                    statuses,
                    ["unsat", "unsat", "unsat", "unsat", "sat", "sat"],
                    "{width:?}/{d}/{negative}: {text}"
                );
                count += 1;
            }
        }
    }
    assert_eq!(count, 68);
    println!(
        "{} universal integer obligations, {count} broken-multiplier SAT controls and {count} admitted minimum inputs",
        count * 4
    );
}

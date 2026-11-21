#[test]
#[ignore = "requires Z3; set NIRVANA_Z3"]
fn signed_integer_lemmas_and_broken_controls() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let solver = std::env::var("NIRVANA_Z3").unwrap_or_else(|_| "z3".into());
    let output = std::process::Command::new(solver)
        .args(["-T:30", "-smt2"])
        .arg(root.join("tests/models/signed_integer.smt2"))
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let text = String::from_utf8(output.stdout).unwrap();
    let directory = root.join("target/verification/signed-integer");
    std::fs::create_dir_all(&directory).unwrap();
    std::fs::write(directory.join("result.txt"), &text).unwrap();
    let statuses: Vec<_> = text
        .lines()
        .filter(|s| matches!(*s, "sat" | "unsat" | "unknown"))
        .collect();
    assert_eq!(
        statuses,
        ["unsat", "sat", "unsat", "unsat", "unsat", "sat"],
        "{text}"
    );
}

#[test]
#[ignore = "requires Z3; set NIRVANA_Z3"]
fn signed_reciprocal_quotients_and_remainders_have_universal_integer_checks() {
    use crate::support::signed_reciprocals::KERNELS;
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let directory = root.join("target/verification/signed-reciprocal");
    std::fs::create_dir_all(&directory).unwrap();
    let solver = std::env::var("NIRVANA_Z3").unwrap_or_else(|_| "z3".into());
    for (d, m, s) in KERNELS {
        for negative in [false, true] {
            let encoded = m as i64;
            let encoded = if encoded < 0 {
                format!("(- {})", encoded.unsigned_abs())
            } else {
                encoded.to_string()
            };
            let model = include_str!("../models/signed_reciprocal.smt2.in")
                .replace("@M@", &m.to_string())
                .replace("@ENCODED@", &encoded)
                .replace("@ADD@", if m >> 63 != 0 { "true" } else { "false" })
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
                .replace("@POSTPOWER@", &(1u128 << s).to_string())
                .replace("@POWER@", &(1u128 << (64 + s)).to_string());
            let file = directory.join(format!("divisor-{d}-negative-{negative}.smt2"));
            std::fs::write(&file, model).unwrap();
            let output = std::process::Command::new(&solver)
                .args(["-T:30", "-smt2"])
                .arg(&file)
                .output()
                .unwrap();
            assert!(
                output.status.success(),
                "{}\n{}",
                String::from_utf8_lossy(&output.stderr),
                String::from_utf8_lossy(&output.stdout)
            );
            let text = String::from_utf8(output.stdout).unwrap();
            std::fs::write(file.with_extension("out"), &text).unwrap();
            let statuses: Vec<_> = text
                .lines()
                .filter(|s| matches!(*s, "sat" | "unsat" | "unknown"))
                .collect();
            assert_eq!(
                statuses,
                ["unsat", "unsat", "unsat", "unsat", "sat", "sat"],
                "{d}/{negative}: {text}"
            );
        }
    }
}

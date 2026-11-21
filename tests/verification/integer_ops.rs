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

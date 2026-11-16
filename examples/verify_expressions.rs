//! Save independently encoded obligations and require real solver results.
use nirvana::ir::{BinaryOp, Expr, Reg, Width};
use nirvana::simplify::simplify;
use nirvana::verify::{MODEL_ID, Solver, Verdict, pure_query};
use std::fmt::Write;
use std::path::PathBuf;

#[path = "../tests/support/rewrite_cases.rs"]
mod rewrite_cases;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut args = std::env::args().skip(1);
    let mut executable = std::env::var_os("NIRVANA_Z3")
        .map(PathBuf::from)
        .unwrap_or_else(|| "z3".into());
    let mut directory = PathBuf::from("target/verification");
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--z3" => executable = args.next().ok_or("--z3 needs a path")?.into(),
            "--out" => directory = args.next().ok_or("--out needs a directory")?.into(),
            _ => return Err(format!("unknown argument {arg}").into()),
        }
    }
    std::fs::create_dir_all(&directory)?;
    let solver = Solver::new(&executable);
    let mut report = format!(
        "# model={MODEL_ID}; solver={}; all inputs unconstrained u64\ncase\tresult\tevidence\n",
        executable.display()
    );
    let mut proved = 0;
    let mut rejected = 0;
    let mut failed = false;
    for (name, before) in rewrite_cases::cases() {
        let after = simplify(&before);
        let query = pure_query(&before, &after).expect("pure case");
        std::fs::write(
            directory.join(format!("{name}.smt2")),
            format!("{}(check-sat)\n", query.smt2()),
        )?;
        let checked = solver.checked_rewrite(&before, &after);
        match checked.verdict {
            Verdict::EquivalentUnderModel => {
                proved += 1;
                writeln!(report, "{name}\tequivalent-under-model\tall u64 inputs")?;
            }
            other => {
                failed = true;
                writeln!(report, "{name}\tunexpected\t{other:?}")?;
            }
        }
        let mutant = Expr::binary(BinaryOp::Add, after, Expr::Const(1));
        let query = pure_query(&before, &mutant).expect("pure mutant");
        std::fs::write(
            directory.join(format!("{name}-mutant.smt2")),
            format!("{}(check-sat)\n", query.smt2()),
        )?;
        let checked = solver.checked_rewrite(&before, &mutant);
        match checked.verdict {
            Verdict::Counterexample(witness) if checked.expression == before => {
                rejected += 1;
                writeln!(report, "{name}-mutant\tcounterexample\t{witness:?}")?;
            }
            other => {
                failed = true;
                writeln!(report, "{name}-mutant\tunexpected\t{other:?}")?;
            }
        }
    }
    for (name, before, after) in rewrite_cases::semantic_mutants() {
        let query = pure_query(&before, &after).expect("pure mutant");
        std::fs::write(
            directory.join(format!("{name}.smt2")),
            format!("{}(check-sat)\n", query.smt2()),
        )?;
        let checked = solver.checked_rewrite(&before, &after);
        match checked.verdict {
            Verdict::Counterexample(witness) if checked.expression == before => {
                rejected += 1;
                writeln!(report, "{name}\tcounterexample\t{witness:?}")?;
            }
            other => {
                failed = true;
                writeln!(report, "{name}\tunexpected\t{other:?}")?;
            }
        }
    }
    let load = Expr::load(Expr::Register(Reg(0)), Width::U64);
    let checked = solver.checked_rewrite(&load, &Expr::Const(0));
    if checked.expression != load || !matches!(checked.verdict, Verdict::Unknown(_)) {
        failed = true;
    }
    writeln!(
        report,
        "memory-expression\tunknown\t{:?}; original retained",
        checked.verdict
    )?;
    std::fs::write(directory.join("report.tsv"), report)?;
    println!(
        "model={MODEL_ID}: {proved} rewrites equivalent for all u64 inputs; {rejected} mutants rejected with replayed witnesses; memory expressions remain unknown"
    );
    println!("obligations and report: {}", directory.display());
    if failed {
        return Err("verification incomplete or failed; inspect report.tsv".into());
    }
    Ok(())
}

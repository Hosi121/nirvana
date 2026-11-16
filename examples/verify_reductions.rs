//! Validate reductions of the existing machine-code fixture objects.
use nirvana::{
    block_verify::{self, BlockVerdict, block_query},
    frontend, reduce,
    verify::Solver,
};
use std::fmt::Write;
use std::path::PathBuf;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut args = std::env::args().skip(1);
    let mut executable = std::env::var_os("NIRVANA_Z3")
        .map(PathBuf::from)
        .unwrap_or_else(|| "z3".into());
    let mut root = PathBuf::from("target/c-fixtures/cc-0");
    let mut out = PathBuf::from("target/block-verification");
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--z3" => executable = args.next().ok_or("--z3 needs a path")?.into(),
            "--fixtures" => root = args.next().ok_or("--fixtures needs a directory")?.into(),
            "--out" => out = args.next().ok_or("--out needs a directory")?.into(),
            _ => return Err(format!("unknown argument {arg}").into()),
        }
    }
    std::fs::create_dir_all(&out)?;
    let solver = Solver::new(executable);
    let mut report = format!(
        "# {}\ncase\toptimization\tresult\tblocks\tevidence\n",
        block_verify::MODEL_ID
    );
    let mut checked = 0;
    let mut accepted = 0;
    let mut blocks = 0;
    for opt in ["O0", "O2"] {
        for line in include_str!("../tests/fixtures/cases.tsv")
            .lines()
            .filter(|line| !line.is_empty() && !line.starts_with('#'))
        {
            let name = line.split('\t').next().unwrap();
            let bytes = std::fs::read(root.join(opt).join(format!("{name}.o")))?;
            let function = match frontend::lift_elf(&bytes, "fixture") {
                Ok(function) => function,
                Err(error) => {
                    writeln!(report, "{name}\t{opt}\tunsupported\t0\t{error}")?;
                    continue;
                }
            };
            let candidate = reduce::reduce(&function.program)?;
            let validation =
                block_verify::validate_program(&function.program, candidate.program(), &solver);
            checked += 1;
            accepted += usize::from(validation.accepted());
            let mut reason = format!("{:?}", validation.incomplete);
            for evidence in &validation.blocks {
                let query = block_query(
                    &function.program,
                    candidate.program(),
                    evidence.address,
                    &evidence.shared_inputs,
                    &evidence.required_outputs,
                )
                .expect("validated shape");
                std::fs::write(
                    out.join(format!("{name}-{opt}-{:x}.smt2", evidence.address)),
                    format!("{}(check-sat)\n", query.smt2()),
                )?;
                match &evidence.verdict {
                    BlockVerdict::EquivalentUnderModel => blocks += 1,
                    BlockVerdict::Counterexample(witness) => {
                        reason = format!(
                            "counterexample at {:#x}; before={:?}; after={:?}; memory_size={}",
                            evidence.address,
                            witness.before.exit,
                            witness.after.exit,
                            witness.memory.len()
                        )
                    }
                    BlockVerdict::Unknown(reason_at_block) => {
                        reason = format!("unknown at {:#x}: {reason_at_block:?}", evidence.address)
                    }
                }
            }
            let status = if validation.accepted() {
                "equivalent-under-model"
            } else {
                "retained-original"
            };
            writeln!(
                report,
                "{name}\t{opt}\t{status}\t{}\t{reason}",
                validation.blocks.len()
            )?;
            println!(
                "{name} {opt}: {status}, {} block checks, {reason}",
                validation.blocks.len()
            );
            std::fs::write(out.join("report.tsv"), &report)?;
        }
    }
    println!(
        "{accepted}/{checked} reductions accepted under {}; {blocks} block obligations UNSAT; report {}",
        block_verify::MODEL_ID,
        out.join("report.tsv").display()
    );
    Ok(())
}

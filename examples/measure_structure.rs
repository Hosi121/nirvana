//! Reproducible comparison on the existing 4,000 small CFGs and C objects.
use nirvana::ir::{Assignment, BinaryOp, Control, Expr, IrInstruction, Program, Reg};
use nirvana::structure::StructuredFunction;
use std::fmt::Write;
use std::path::PathBuf;
use std::time::Instant;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let directory = PathBuf::from(
        std::env::args()
            .nth(1)
            .ok_or("usage: measure_structure OUTPUT_DIR")?,
    );
    std::fs::create_dir_all(&directory)?;
    let mut tiny =
        String::from("case\tstatus\tunique_blocks\tblock_copies\toriginal_steps\tstep_copies\n");
    let mut accepted = 0;
    let mut copies = 0;
    let start = Instant::now();
    for first in 0..10 {
        for second in 0..10 {
            for third in 0..10 {
                for entry in 0..4 {
                    let mut instructions = Vec::new();
                    for (address, choice) in [first, second, third, 1].into_iter().enumerate() {
                        let control = match choice {
                            0 => Control::Next,
                            1 => Control::Return(Expr::Register(Reg(1))),
                            2..=5 => Control::Jump(choice - 2),
                            _ => Control::Branch {
                                condition: Expr::binary(
                                    BinaryOp::And,
                                    Expr::Register(Reg(0)),
                                    Expr::Const(1),
                                ),
                                target: choice - 6,
                            },
                        };
                        let assignments = vec![
                            Assignment {
                                destination: Reg(0).into(),
                                value: Expr::binary(
                                    BinaryOp::Add,
                                    Expr::Register(Reg(0)),
                                    Expr::Const(address as u64 + 1),
                                ),
                            },
                            Assignment {
                                destination: Reg(1).into(),
                                value: Expr::binary(
                                    BinaryOp::Xor,
                                    Expr::Register(Reg(1)),
                                    Expr::Register(Reg(0)),
                                ),
                            },
                        ];
                        instructions.push(IrInstruction {
                            address: address as u64,
                            size: 1,
                            assignments,
                            control,
                        });
                    }
                    let program = Program::new(entry, 2, instructions)?;
                    let name = format!("{first}-{second}-{third}-{entry}");
                    match StructuredFunction::recover(&program) {
                        Ok(function) => {
                            accepted += 1;
                            let stats = function.stats();
                            let evidence = function.evidence();
                            copies += stats.extra_block_copies;
                            writeln!(
                                tiny,
                                "{name}\tstructured\t{}\t{}\t{}\t{}",
                                stats.unique_blocks,
                                stats.emitted_block_copies,
                                evidence.original_steps,
                                evidence.compared_copies
                            )?;
                        }
                        Err(reason) => writeln!(tiny, "{name}\t{reason:?}\t0\t0\t0\t0")?,
                    }
                }
            }
        }
    }
    std::fs::write(directory.join("tiny.tsv"), tiny)?;
    println!(
        "tiny: {accepted}/4000 structured, {copies} extra block copies, {:?} including program validation",
        start.elapsed()
    );
    let root = PathBuf::from("target/c-fixtures/cc-0");
    let mut fixtures = String::from(
        "case\toptimization\tstatus\tunique_blocks\tblock_copies\toriginal_steps\tstep_copies\n",
    );
    let mut structured = 0;
    let mut lifted = 0;
    let mut step_copies = 0;
    for opt in ["O0", "O2"] {
        for line in include_str!("../tests/fixtures/cases.tsv")
            .lines()
            .filter(|line| !line.is_empty() && !line.starts_with('#'))
        {
            let name = line.split('\t').next().unwrap();
            let object = std::fs::read(root.join(opt).join(format!("{name}.o")))?;
            match nirvana::frontend::lift_elf(&object, "fixture") {
                Ok(function) => {
                    lifted += 1;
                    match StructuredFunction::recover(&function.program) {
                        Ok(function) => {
                            structured += 1;
                            let s = function.stats();
                            let e = function.evidence();
                            step_copies += e.compared_copies;
                            writeln!(
                                fixtures,
                                "{name}\t{opt}\tstructured\t{}\t{}\t{}\t{}",
                                s.unique_blocks,
                                s.emitted_block_copies,
                                e.original_steps,
                                e.compared_copies
                            )?;
                        }
                        Err(reason) => writeln!(fixtures, "{name}\t{opt}\t{reason:?}\t0\t0\t0\t0")?,
                    }
                }
                Err(_) => writeln!(fixtures, "{name}\t{opt}\tunsupported\t0\t0\t0\t0")?,
            }
        }
    }
    std::fs::write(directory.join("fixtures.tsv"), fixtures)?;
    println!(
        "machine: {structured}/{lifted} lifted configurations structured, {step_copies} step copies"
    );
    Ok(())
}

//! Compare representable memory accesses on the same compiled fixture objects.
use nirvana::ir::Reg;
use nirvana::readable::{ReadableOptions, emit_readable_c, emit_readable_c_with_options};
use std::fmt::Write;
use std::path::PathBuf;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let directory = PathBuf::from(
        std::env::args()
            .nth(1)
            .ok_or("usage: measure_stack_views OUTPUT_DIR [FIXTURE_OBJECT_DIR]")?,
    );
    let objects = PathBuf::from(
        std::env::args()
            .nth(2)
            .unwrap_or_else(|| "target/c-fixtures/cc-0".into()),
    );
    std::fs::create_dir_all(&directory)?;
    let mut report = String::from(
        "case\toptimization\tstatus\tviews\tread_sites\twrite_sites\traw_loads_before\traw_loads_after\tnamed_loads\traw_stores_before\traw_stores_after\tnamed_stores\n",
    );
    let (mut lifted, mut views, mut reads, mut writes) = (0, 0, 0, 0);
    for opt in ["O0", "O2"] {
        for line in include_str!("../tests/fixtures/cases.tsv")
            .lines()
            .filter(|l| !l.is_empty() && !l.starts_with('#'))
        {
            let name = line.split('\t').next().unwrap();
            let bytes = std::fs::read(objects.join(opt).join(format!("{name}.o")))?;
            let function = match nirvana::frontend::lift_elf(&bytes, "fixture") {
                Ok(function) => function,
                Err(error) => {
                    writeln!(
                        report,
                        "{name}\t{opt}\tunsupported: {error}\t0\t0\t0\t0\t0\t0\t0\t0\t0"
                    )?;
                    continue;
                }
            };
            let baseline = emit_readable_c(&function.program)?;
            let output = emit_readable_c_with_options(
                &function.program,
                ReadableOptions {
                    stack_register: Some(Reg(nirvana::x86::RSP)),
                    recover_objects: false,
                },
            )?;
            let r: usize = output.stack_views.iter().map(|v| v.read_sites).sum();
            let w: usize = output.stack_views.iter().map(|v| v.write_sites).sum();
            lifted += 1;
            views += output.stack_views.len();
            reads += r;
            writes += w;
            let count = |code: &str, pattern: &str| code.matches(pattern).count();
            writeln!(
                report,
                "{name}\t{opt}\tlifted\t{}\t{r}\t{w}\t{}\t{}\t{}\t{}\t{}\t{}",
                output.stack_views.len(),
                count(&baseline.code, "nirvana_load(&m,"),
                count(&output.code, "nirvana_load(&m,"),
                count(&output.code, "nirvana_view_load(&m,"),
                count(&baseline.code, "nirvana_store(&m,"),
                count(&output.code, "nirvana_store(&m,"),
                count(&output.code, "nirvana_view_store(&m,")
            )?;
            std::fs::write(
                directory.join(format!("{name}-{opt}-before.c")),
                baseline.code,
            )?;
            std::fs::write(directory.join(format!("{name}-{opt}-after.c")), output.code)?;
        }
    }
    std::fs::write(directory.join("report.tsv"), report)?;
    println!(
        "{lifted}/40 lifted configurations: {views} stack views, {reads} read sites, {writes} write sites; these are address-representation counts, not source-recovery accuracy"
    );
    Ok(())
}

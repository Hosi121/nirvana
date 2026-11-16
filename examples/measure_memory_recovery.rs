//! Compare address representation and local storage on identical machine code.
use nirvana::ir::{Reg, Width};
use nirvana::readable::{ReadableOptions, emit_readable_c_with_options};
use std::fmt::Write;
use std::path::{Path, PathBuf};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let out = PathBuf::from(
        std::env::args()
            .nth(1)
            .unwrap_or_else(|| "target/memory-recovery".into()),
    );
    std::fs::create_dir_all(&out)?;
    let mut cases = Vec::new();
    for opt in ["O0", "O2"] {
        for line in include_str!("../tests/fixtures/cases.tsv")
            .lines()
            .filter(|l| !l.is_empty() && !l.starts_with('#'))
        {
            let name = line.split('\t').next().unwrap();
            cases.push((
                "base".to_string(),
                name.to_string(),
                opt.to_string(),
                PathBuf::from(format!("target/c-fixtures/cc-0/{opt}/{name}.o")),
            ));
        }
        for name in ["byte-fields", "strided-input", "selected-alias"] {
            let target = out.join(format!("recovery-{name}-{opt}.o"));
            compile(
                &PathBuf::from(format!("tests/fixtures/recovery/{name}.c")),
                &target,
                opt,
            )?;
            cases.push(("recovery".into(), name.into(), opt.into(), target));
        }
    }
    let mut generated: Vec<_> = std::fs::read_dir("target/memory-recovery/generated")?
        .map(|p| p.map(|e| e.path()))
        .collect::<Result<_, _>>()?;
    generated.sort();
    for object in generated {
        if object.extension().is_none_or(|e| e != "o") {
            continue;
        }
        let stem = object.file_stem().unwrap().to_str().unwrap();
        let (name, opt) = stem
            .rsplit_once('-')
            .ok_or("invalid generated object name")?;
        cases.push(("generated".into(), name.into(), opt.into(), object));
    }
    let version = std::process::Command::new("cc").arg("--version").output()?;
    std::fs::write(out.join("compiler.txt"), version.stdout)?;
    let mut report = String::from(
        "corpus\tcase\topt\tstatus\tstack_views\tobjects\tfields\tfield_reads\tfield_writes\tindex_shapes\tindex_reads\tindex_writes\tstack_only_locals\tseparate_locals\treused_locals\tnarrow_separate\tnarrow_reused\twhile_loops\tindex_addresses\n",
    );
    let (mut lifted, mut separate, mut reused, mut fields, mut indexes) = (0, 0, 0, 0, 0);
    for (corpus, name, opt, object) in cases {
        let program = match nirvana::frontend::lift_elf(&std::fs::read(&object)?, "fixture") {
            Ok(f) => f.program,
            Err(error) => {
                writeln!(
                    report,
                    "{corpus}\t{name}\t{opt}\tunsupported: {error}\t0\t0\t0\t0\t0\t0\t0\t0\t0\t0\t0\t0\t0\t0\t0"
                )?;
                continue;
            }
        };
        let options = ReadableOptions {
            stack_register: Some(Reg(nirvana::x86::RSP)),
            recover_objects: true,
            coalesce_locals: false,
            compact_memory: false,
        };
        let stack_only = emit_readable_c_with_options(
            &program,
            ReadableOptions {
                recover_objects: false,
                ..options
            },
        )?;
        let before = emit_readable_c_with_options(&program, options)?;
        let after = emit_readable_c_with_options(
            &program,
            ReadableOptions {
                coalesce_locals: true,
                ..options
            },
        )?;
        let count_fields: usize = after.object_views.iter().map(|o| o.fields.len()).sum();
        let field_reads: usize = after
            .object_views
            .iter()
            .flat_map(|o| &o.fields)
            .map(|f| f.read_sites)
            .sum();
        let field_writes: usize = after
            .object_views
            .iter()
            .flat_map(|o| &o.fields)
            .map(|f| f.write_sites)
            .sum();
        let count_indexes: usize = after.object_views.iter().map(|o| o.indexed.len()).sum();
        let index_addresses: usize = after
            .object_views
            .iter()
            .flat_map(|o| &o.indexed)
            .map(|i| i.address_sites)
            .sum();
        let index_reads: usize = after
            .object_views
            .iter()
            .flat_map(|o| &o.indexed)
            .map(|f| f.read_sites)
            .sum();
        let index_writes: usize = after
            .object_views
            .iter()
            .flat_map(|o| &o.indexed)
            .map(|f| f.write_sites)
            .sum();
        let narrow_before = before
            .locals
            .iter()
            .filter(|l| l.width != Width::U64)
            .count();
        let narrow_after = after
            .locals
            .iter()
            .filter(|l| l.width != Width::U64)
            .count();
        writeln!(
            report,
            "{corpus}\t{name}\t{opt}\tlifted\t{}\t{}\t{count_fields}\t{field_reads}\t{field_writes}\t{count_indexes}\t{index_reads}\t{index_writes}\t{}\t{}\t{}\t{narrow_before}\t{narrow_after}\t{}\t{index_addresses}",
            after.stack_views.len(),
            after.object_views.len(),
            stack_only.locals.len(),
            before.locals.len(),
            after.locals.len(),
            after.code.matches("while (").count()
        )?;
        lifted += 1;
        separate += before.locals.len();
        reused += after.locals.len();
        fields += count_fields;
        indexes += count_indexes;
        std::fs::write(
            out.join(format!("{corpus}-{name}-{opt}-stack-only.c")),
            stack_only.code,
        )?;
        std::fs::write(
            out.join(format!("{corpus}-{name}-{opt}-separate.c")),
            before.code,
        )?;
        std::fs::write(
            out.join(format!("{corpus}-{name}-{opt}-full.c")),
            after.code,
        )?;
    }
    std::fs::write(out.join("report.tsv"), report)?;
    println!(
        "{lifted} lifted configurations: {fields} fields, {indexes} indexed shapes; C local declarations {separate} -> {reused}; no source-similarity score or speed claim"
    );
    Ok(())
}

fn compile(source: &Path, object: &Path, opt: &str) -> Result<(), Box<dyn std::error::Error>> {
    let result = std::process::Command::new("cc")
        .args([
            "-std=c11",
            "-Wall",
            "-Wextra",
            "-Werror",
            "-pedantic",
            "-fno-lto",
            "-DFIXTURE_ENTRY=fixture",
        ])
        .arg(format!("-{opt}"))
        .arg("-c")
        .arg(source)
        .arg("-o")
        .arg(object)
        .output()?;
    if !result.status.success() {
        return Err(String::from_utf8_lossy(&result.stderr).into_owned().into());
    }
    Ok(())
}

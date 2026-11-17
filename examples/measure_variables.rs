//! Candidate variable lineages for source-oracle evaluation. Debug information
//! is never passed to the decompiler; this only reports its own output metadata.
use nirvana::{frontend, ir::Reg, readable, x86};

fn cell(value: &str) -> String {
    value
        .replace('\\', "\\\\")
        .replace('\t', "\\t")
        .replace('\n', "\\n")
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let objects: Vec<_> = std::env::args_os().skip(1).collect();
    if objects.is_empty() {
        return Err("usage: cargo run --example measure_variables -- FILE.o ...".into());
    }
    println!("object\tlocal\tregister\tweb\toffset\twidth\trole\tbasis");
    for object in objects {
        let path = std::path::Path::new(&object);
        let input = frontend::lift_elf(&std::fs::read(path)?, "fixture")?;
        let output = readable::emit_readable_c_with_options(
            &input.program,
            readable::ReadableOptions {
                stack_register: Some(Reg(x86::RSP)),
                recover_objects: true,
                coalesce_locals: true,
                compact_memory: true,
            },
        )?;
        for local in &output.locals {
            for &register in &local.registers {
                let web = output
                    .stack_roles
                    .as_ref()
                    .and_then(|roles| roles.register_web(register));
                let stored = web.and_then(|web| output.stack_roles.as_ref()?.web_location(web));
                let loaded = output
                    .stack_cells
                    .as_ref()
                    .and_then(|cells| cells.location(register));
                let location = stored.or(loaded);
                let basis = if stored.is_some() {
                    "store-web"
                } else if loaded.is_some() {
                    "load-cell"
                } else {
                    "-"
                };
                println!(
                    "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
                    cell(&path.display().to_string()),
                    cell(&local.name),
                    register.0,
                    web.map_or_else(|| "-".into(), |web| web.to_string()),
                    location.map_or_else(|| "-".into(), |location| location.offset.to_string()),
                    location
                        .map_or_else(|| "-".into(), |location| location.width.bytes().to_string()),
                    local.role.map_or("-", |role| role.stem()),
                    basis,
                );
            }
        }
    }
    Ok(())
}

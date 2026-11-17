//! Inspect definition-web candidates on the same object inputs used by C tests.
use nirvana::{frontend, readable, reduce, web, web_verify};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let objects: Vec<_> = std::env::args_os().skip(1).collect();
    if objects.is_empty() {
        return Err("usage: cargo run --example verify_definition_webs -- FILE.o ...".into());
    }
    println!(
        "object\tstatus\tdefinitions\twebs\tsplit_registers\tfresh_registers\tread_obligations\tdisplay"
    );
    for path in objects {
        let bytes = std::fs::read(&path)?;
        let name = std::path::Path::new(&path).display().to_string();
        let lifted = match frontend::lift_elf(&bytes, "fixture") {
            Ok(lifted) => lifted,
            Err(error) => {
                eprintln!("{name}: {error}");
                println!("{name}\tunsupported\t0\t0\t0\t0\t0\tnot-emitted");
                continue;
            }
        };
        let reduced = reduce::reduce(&lifted.program)?;
        let Some(candidate) = web::split(reduced.program()) else {
            println!("{name}\tunavailable\t0\t0\t0\t0\t0\tunchanged");
            continue;
        };
        let evidence = match web_verify::validate(reduced.program(), candidate.program()) {
            Ok(evidence) => evidence,
            Err(error) if error.is_resource_limit() => {
                println!("{name}\tverification-unavailable\t0\t0\t0\t0\t0\tunchanged");
                continue;
            }
            Err(error) => return Err(format!("{name}: invalid candidate: {error}").into()),
        };
        let output = readable::emit_readable_c_with_options(
            &lifted.program,
            readable::ReadableOptions {
                stack_register: Some(nirvana::ir::Reg(nirvana::x86::RSP)),
                recover_objects: true,
                coalesce_locals: true,
                compact_memory: true,
            },
        )?;
        let status = match output.web_recovery {
            readable::WebRecovery::Applied { .. } => "applied",
            readable::WebRecovery::Unchanged => "unchanged",
            readable::WebRecovery::Unavailable => "unavailable",
            readable::WebRecovery::StructureFallback(_) => "structure-fallback",
            readable::WebRecovery::RenderingFallback(_) => "render-fallback",
            readable::WebRecovery::Rejected(error) => return Err(error.into()),
        };
        let stats = candidate.stats();
        println!(
            "{name}\tvalidated\t{}\t{}\t{}\t{}\t{}\t{status}",
            stats.definitions,
            stats.webs,
            stats.split_registers,
            stats.fresh_registers,
            evidence.register_reads,
        );
    }
    Ok(())
}

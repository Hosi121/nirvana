//! Read-only probes for the pinned CTF corpus. See tools/audit_ctf.py.
use nirvana::{linked_elf::LinkedOptions, module_ir, x86};
use std::io::{self, BufRead};

fn number(value: &str) -> Result<u64, Box<dyn std::error::Error>> {
    Ok(if let Some(hex) = value.strip_prefix("0x") {
        u64::from_str_radix(hex, 16)?
    } else {
        value.parse()?
    })
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<_> = std::env::args().skip(1).collect();
    match args.first().map(String::as_str) {
        Some("decode") if args.len() == 1 => {
            for line in io::stdin().lock().lines() {
                let line = line?;
                let fields: Vec<_> = line.split('\t').collect();
                if fields.len() != 3 || !fields[2].is_ascii() || fields[2].len() % 2 != 0 {
                    return Err("expected index, address, instruction hex".into());
                }
                let address = number(fields[1])?;
                let bytes = (0..fields[2].len())
                    .step_by(2)
                    .map(|i| u8::from_str_radix(&fields[2][i..i + 2], 16))
                    .collect::<Result<Vec<_>, _>>()?;
                let (kind, detail) = match x86::decode_reference_at(&bytes, address) {
                    Ok(i) if usize::from(i.size) == bytes.len() => {
                        ("scalar", format!("{:?}", i.operation))
                    }
                    _ if x86::decode_fs_guard_at(&bytes, address, x86::FS_GUARD_OFFSET)
                        .is_ok_and(|i| usize::from(i.size) == bytes.len()) =>
                    {
                        ("fs-guard", "explicit guest TLS guard profile".into())
                    }
                    scalar => match x86::decode_vector_at(&bytes, address) {
                        Ok(i) if i.size as usize == bytes.len() => ("vector", "vector".into()),
                        vector => (
                            "unsupported",
                            format!("scalar={scalar:?}; vector={vector:?}"),
                        ),
                    },
                };
                println!(
                    "{}\t{kind}\t{}",
                    fields[0],
                    detail.replace(['\t', '\n', '\r'], " ")
                );
            }
        }
        Some(mode) if (mode == "run" && args.len() == 4) || (mode == "image" && args.len() == 3) => {
            let bytes = std::fs::read(&args[1])?;
            let options = LinkedOptions {
                load_bias: if bytes.get(16..18) == Some(&[2, 0]) {
                    0
                } else {
                    0x10000
                },
                ..Default::default()
            };
            let module = module_ir::lift_elf_at(&bytes, number(&args[2])?, options)?;
            if mode == "image" {
                let layout = module.image.memory_layout.as_ref();
                let end = layout.map_or(module.image.memory_base + module.image.memory.len() as u64,
                    |l| { let r=l.regions().last().unwrap(); r.address+r.size });
                println!("{{\"model\":\"{}\",\"memory_base\":{},\"backing_bytes\":{},\"virtual_span\":{},\"regions\":{}}}",
                    module.program.model_id(), module.image.memory_base, module.image.memory.len(),
                    end-module.image.memory_base, layout.map_or(0,|l|l.regions().len()));
                return Ok(());
            }
            let mut registers = module.initial_registers();
            let inputs = args[3]
                .split(',')
                .map(number)
                .collect::<Result<Vec<_>, _>>()?;
            if inputs.len() > 6 {
                return Err("at most six SysV integer arguments".into());
            }
            for (register, value) in [7, 6, 2, 1, 8, 9].into_iter().zip(inputs) {
                registers[register] = value;
            }
            let report = module.program.run(
                &registers,
                module.image.memory_base,
                &module.image.memory,
                module_ir::Limits {
                    instructions: 100_000,
                    imports: 0,
                },
                &mut module_ir::RejectImports,
            )?;
            println!(
                "status={:?}\npc={:#x}\nrax={}\nsteps={}",
                report.status,
                report.pc,
                report.state.registers[0],
                report.state.trace.len()
            );
        }
        _ => return Err("usage: inspect_ctf decode | image ELF LINK_TIME_ENTRY | run ELF LINK_TIME_ENTRY ARG[,ARG...]".into()),
    }
    Ok(())
}

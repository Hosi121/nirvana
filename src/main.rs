use nirvana::{
    block_verify::{self, BlockVerdict},
    emit, frontend, readable,
    structure::StructuredFunction,
    structure_verify::{self, FlowGraph},
    verify::Solver,
    x86,
};
use std::error::Error;

const HELP: &str = "usage: nirvana FILE.o [--symbol fixture] [--emit c|readable-c|ir|cfg|structured-cfg|decoded]\n       nirvana FILE.o --emit readable-c --verify-reduction PATH_TO_Z3\n       nirvana FILE.o --run A,B,C,D [--steps N]\n       nirvana FILE.bin --raw [--base 0x1000] [--entry 0x1000] [--emit ...]\n\nObject input: ELF64 little-endian x86-64 ET_REL, with a sized function symbol.\n--run initializes the four-word fixture ABI (RDI points to guest state).\n--emit readable-c observes the return and guest memory, with value arguments and named memory views.\n--no-coalesce-locals keeps separate local value variables in readable-c.\n--emit structured-cfg reconstructs a graph from the checked structured AST.\n--verify-reduction checks IR reduction only; an unaccepted candidate keeps original IR.\n--emit c preserves the full machine-register interface.\nUnsupported instructions and unresolved relocations are errors.\n";

fn number(text: &str) -> Result<u64, Box<dyn Error>> {
    Ok(if let Some(hex) = text.strip_prefix("0x") {
        u64::from_str_radix(hex, 16)?
    } else {
        text.parse()?
    })
}

fn main() {
    if let Err(error) = run() {
        eprintln!("{error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), Box<dyn Error>> {
    let mut args = std::env::args().skip(1);
    let path = args.next().ok_or(HELP)?;
    if path == "--help" || path == "-h" {
        print!("{HELP}");
        return Ok(());
    }
    let mut symbol = String::from("fixture");
    let mut format = String::from("c");
    let mut raw = false;
    let mut base = None;
    let mut entry = None;
    let mut input = None;
    let mut limit = 100_000;
    let mut solver = None;
    let mut coalesce_locals = true;
    while let Some(argument) = args.next() {
        match argument.as_str() {
            "--symbol" => symbol = args.next().ok_or("--symbol requires a name")?,
            "--emit" => format = args.next().ok_or("--emit requires a format")?,
            "--raw" => raw = true,
            "--no-coalesce-locals" => coalesce_locals = false,
            "--verify-reduction" => {
                solver = Some(Solver::new(
                    args.next().ok_or("--verify-reduction requires a Z3 path")?,
                ))
            }
            "--base" => base = Some(number(&args.next().ok_or("--base requires an address")?)?),
            "--entry" => entry = Some(number(&args.next().ok_or("--entry requires an address")?)?),
            "--steps" => limit = args.next().ok_or("--steps requires a limit")?.parse()?,
            "--run" => {
                let text = args
                    .next()
                    .ok_or("--run requires four comma-separated unsigned values")?;
                let values: Vec<_> = text.split(',').map(number).collect::<Result<_, _>>()?;
                let values: [u64; 4] = values
                    .try_into()
                    .map_err(|_| "--run requires exactly four values")?;
                input = Some(values);
            }
            _ => return Err(format!("unknown argument {argument}\n{HELP}").into()),
        }
    }
    if solver.is_some() && (format != "readable-c" || input.is_some()) {
        return Err(
            "--verify-reduction requires --emit readable-c and cannot be used with --run".into(),
        );
    }
    if !coalesce_locals && (format != "readable-c" || input.is_some()) {
        return Err(
            "--no-coalesce-locals requires --emit readable-c and cannot be used with --run".into(),
        );
    }
    let bytes = std::fs::read(path)?;
    let (program, code, code_base) = if raw {
        let base = base.unwrap_or(0);
        (x86::lift(&bytes, base, entry.unwrap_or(base))?, bytes, base)
    } else {
        if base.is_some() || entry.is_some() {
            return Err("--base and --entry require --raw".into());
        }
        let lifted = frontend::lift_elf(&bytes, &symbol)?;
        (lifted.program, lifted.image.bytes, lifted.image.address)
    };
    if let Some(input) = input {
        let memory_base = 0x1000u64;
        let state_address = 0x2000u64;
        let mut memory = vec![0; 0x10000];
        for (i, value) in input.iter().enumerate() {
            let offset = (state_address - memory_base) as usize + i * 8;
            memory[offset..offset + 8].copy_from_slice(&value.to_le_bytes());
        }
        let mut registers = vec![0; x86::REGISTER_COUNT];
        registers[x86::RDI] = state_address;
        registers[x86::RSP] = 0x10000;
        let execution = program.execute_with_memory(&registers, memory_base, &memory, limit)?;
        let state: Vec<_> = (0..4)
            .map(|i| {
                let offset = (state_address - memory_base) as usize + i * 8;
                u64::from_le_bytes(execution.memory[offset..offset + 8].try_into().unwrap())
            })
            .collect();
        println!(
            "{} {} {} {} {}",
            execution.value, state[0], state[1], state[2], state[3]
        );
        return Ok(());
    }
    match format.as_str() {
        "readable-c" => {
            let options = readable::ReadableOptions {
                stack_register: Some(nirvana::ir::Reg(x86::RSP)),
                recover_objects: true,
                coalesce_locals,
            };
            let output = if let Some(solver) = solver {
                let (output, validation) =
                    readable::emit_readable_c_with_checked_reduction_and_options(
                        &program, &solver, options,
                    )?;
                if validation.accepted() {
                    eprintln!(
                        "IR reduction accepted under {}: {} block obligations; C emission is separately tested",
                        block_verify::MODEL_ID,
                        validation.blocks.len()
                    );
                } else {
                    let reason = validation
                        .incomplete
                        .map(|reason| format!("{reason:?}"))
                        .or_else(|| {
                            validation.blocks.last().map(|block| match &block.verdict {
                                BlockVerdict::Unknown(reason) => {
                                    format!("unknown at {:#x}: {reason:?}", block.address)
                                }
                                BlockVerdict::Counterexample(_) => {
                                    format!("local boundary counterexample at {:#x}", block.address)
                                }
                                BlockVerdict::EquivalentUnderModel => {
                                    "incomplete validation".into()
                                }
                            })
                        })
                        .unwrap_or_else(|| "incomplete validation".into());
                    eprintln!("retaining original IR: {reason}");
                }
                output
            } else {
                readable::emit_readable_c_with_options(&program, options)?
            };
            if let Some(reason) = output.fallback_reason {
                eprintln!("retaining goto control flow: {reason}");
            }
            print!("{}", output.code);
        }
        "c" => {
            let output = emit::emit_c(&program);
            if let Some(reason) = output.fallback_reason {
                eprintln!("retaining goto control flow: {reason}");
            }
            println!(
                "/* x86-64 machine state: {} uint64_t registers; r[0]=RAX, r[4]=RSP, r[7]=RDI. */",
                program.register_count()
            );
            print!("{}", output.code);
        }
        "ir" => {
            for instruction in program.instructions() {
                println!("{instruction:#?}");
            }
        }
        "cfg" => print!("{}", program.cfg().to_dot()),
        "structured-cfg" => {
            let function = StructuredFunction::recover(&program)?;
            let evidence = function.evidence();
            eprintln!(
                "structured AST accepted under {}: {} original steps, {} compared copies; C rendering is separately tested",
                structure_verify::MODEL_ID,
                evidence.original_steps,
                evidence.compared_copies
            );
            print!("{}", FlowGraph::from_nodes(function.body())?.to_dot());
        }
        "decoded" => {
            let entry = program.cfg().block(program.cfg().entry()).start;
            for instruction in x86::decode_reachable(&code, code_base, entry)? {
                println!(
                    "{:#x} (+{}): {:?}",
                    instruction.address, instruction.size, instruction.operation
                );
            }
        }
        _ => return Err(format!("unknown emission format {format}").into()),
    }
    Ok(())
}

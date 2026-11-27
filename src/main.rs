use nirvana::{
    block_verify::{self, BlockVerdict},
    emit, frontend, readable,
    structure::StructuredFunction,
    structure_verify::{self, FlowGraph},
    verify::Solver,
    x86,
};
use std::error::Error;

const HELP: &str = "usage: nirvana ELF [--symbol fixture] [--emit c|ssa-c|readable-c|middle-ir|middle-c|effects-c|effects-readable-c|effects-ir|module-c|module-readable-c|module-locals-c|module-ir|module-values|module-jumps|types|record-types|references|ir|cfg|structured-cfg|decoded]\n       nirvana FILE.o --emit readable-c --verify-reduction PATH_TO_Z3\n       nirvana FILE.o --run A,B,C,D [--steps N]\n       nirvana FILE.o --run-effects RESULT[,RESULT...] [--steps N]\n       nirvana FILE.bin --raw [--base 0x1000] [--entry 0x1000] [--emit ...]\n\nELF input: ELF64 little-endian x86-64 ET_REL/ET_EXEC/PIE, with a sized function symbol. Module modes also accept --entry LINK_TIME_ADDRESS with mapped unwind bounds.\n--version reports the package and build source identity.\n--run initializes the four-word fixture ABI (RDI points to guest state).\n--emit readable-c observes the return and guest memory, with value arguments and named memory views.\n--no-coalesce-locals keeps separate local value variables in readable-c/middle-c.\n--emit middle-ir reports scoped values, checked-load constants, saved snapshots, SSA storage versions and CFG.\n--emit middle-c compares checked Middle IR constants and saved values with the readable C baseline.\n--emit types reports SSA value constraints, candidate layouts and record shape compatibility as JSON.\n--emit record-types emits tentative x86-64 record declarations inferred from field and pointer flow.\n--emit references reports ELF symbolic addresses, file literals and opaque call sites as JSON.\n--emit effects-c/effects-readable-c/effects-ir uses the explicit puts output/outcome model.\n--emit effects-readable-c structures control while preserving checked calls and budgets.\n--emit module-c/module-ir lifts bounded linked functions with internal/indirect calls; default symbol main.\n--entry ADDRESS selects an exact link-time region entry in module modes; PIE bias is added automatically.\nmodule-c emits a standalone Linux x86-64 C program with checked POSIX imports.\nmodule-readable-c recovers named calls and structured function bodies with checked PC resumption.\nmodule-locals-c adds checked named locals, phi transfers and canonical state reconstruction.\n--emit module-values reports per-function SSA values, uses, live sets and opaque call boundaries as JSON.\n--run-effects supplies signed int return inputs, prints modeled output, and reports status on stderr.\n--emit structured-cfg reconstructs a graph from the checked structured AST.\n--recover-loops PATH_TO_Z3 tries source-bound loop recovery in readable-c/middle-c, retaining the baseline on incomplete proofs.\n--verify-reduction checks IR reduction only; an unaccepted candidate keeps original IR.\n--emit c preserves the full machine-register interface.\n--emit ssa-c adds checked SSA local groups and phi edge copies with canonical register mirrors.\nExecutable modes require supported instructions and fully resolved code references.\n";

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
    if path == "--version" || path == "-V" {
        if args.next().is_some() {
            return Err("--version accepts no additional arguments".into());
        }
        println!("{}", nirvana::BUILD_VERSION);
        return Ok(());
    }
    if path == "--help" || path == "-h" {
        print!("{HELP}");
        return Ok(());
    }
    let mut symbol = String::from("fixture");
    let mut symbol_given = false;
    let mut format = String::from("c");
    let mut raw = false;
    let mut base = None;
    let mut entry = None;
    let mut input = None;
    let mut effect_results = None;
    let mut limit = 100_000;
    let mut solver = None;
    let mut loop_solver = None;
    let mut coalesce_locals = true;
    while let Some(argument) = args.next() {
        match argument.as_str() {
            "--symbol" => {
                symbol = args.next().ok_or("--symbol requires a name")?;
                symbol_given = true;
            }
            "--emit" => format = args.next().ok_or("--emit requires a format")?,
            "--raw" => raw = true,
            "--run-effects" => {
                let text = args
                    .next()
                    .ok_or("--run-effects requires comma-separated signed int return inputs")?;
                let results = text
                    .split(',')
                    .map(str::parse::<i32>)
                    .collect::<Result<Vec<_>, _>>()?;
                effect_results = Some(results);
            }
            "--no-coalesce-locals" => coalesce_locals = false,
            "--verify-reduction" => {
                solver = Some(Solver::new(
                    args.next().ok_or("--verify-reduction requires a Z3 path")?,
                ))
            }
            "--recover-loops" => {
                loop_solver = Some(
                    Solver::new(args.next().ok_or("--recover-loops requires a Z3 path")?)
                        .with_timeout(std::time::Duration::from_secs(15)),
                );
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
    if loop_solver.is_some()
        && (!matches!(format.as_str(), "readable-c" | "middle-c")
            || input.is_some()
            || effect_results.is_some()
            || solver.is_some())
    {
        return Err(
            "--recover-loops requires readable-c or middle-c emission with a separate loop proof"
                .into(),
        );
    }
    if !coalesce_locals
        && (!matches!(format.as_str(), "readable-c" | "middle-c") || input.is_some())
    {
        return Err(
            "--no-coalesce-locals requires --emit readable-c or middle-c and cannot be used with --run".into(),
        );
    }
    let bytes = std::fs::read(path)?;
    if matches!(
        format.as_str(),
        "module-c"
            | "module-readable-c"
            | "module-locals-c"
            | "module-ir"
            | "module-values"
            | "module-jumps"
    ) {
        if raw
            || input.is_some()
            || effect_results.is_some()
            || base.is_some()
            || solver.is_some()
            || !coalesce_locals
        {
            return Err("module modes require a linked ELF and separate emission options".into());
        }
        if symbol_given && entry.is_some() {
            return Err(
                "module modes select either --symbol NAME or --entry LINK_TIME_ADDRESS".into(),
            );
        }
        if !symbol_given {
            symbol = "main".into();
        }
        let options = nirvana::linked_elf::LinkedOptions {
            load_bias: if bytes.get(16..18) == Some(&[2, 0]) {
                0
            } else {
                0x10000
            },
            ..Default::default()
        };
        let module = if let Some(entry) = entry {
            nirvana::module_ir::lift_elf_at(&bytes, entry, options)?
        } else {
            nirvana::module_ir::lift_elf(&bytes, &symbol, options)?
        };
        if format == "module-jumps" {
            print!(
                "{}",
                nirvana::jump_tables::to_json_with_context_limits(
                    &module.jump_tables,
                    &module.jump_table_diagnostics,
                    &module.jump_table_context_limits,
                )?
            );
        } else if format == "module-values" {
            let analysis = nirvana::module_values::analyze(&module.program)?;
            let analyzed = analysis
                .functions
                .iter()
                .filter(|f| f.result.is_ok())
                .count();
            let closed = analysis
                .call_summaries()
                .functions
                .iter()
                .filter(|f| f.closed)
                .count();
            eprintln!(
                "module values: {analyzed}/{} functions analyzed; {closed} closed call summaries",
                analysis.functions.len()
            );
            print!("{}", analysis.to_json()?);
        } else if matches!(format.as_str(), "module-readable-c" | "module-locals-c") {
            let output = if format == "module-locals-c" {
                nirvana::module_readable::emit_c_with_locals(&module)?
            } else {
                nirvana::module_readable::emit_c(&module)?
            };
            if format == "module-locals-c" {
                eprintln!(
                    "module locals: {} functions, {} fallback; {} variables, {} resume bindings, {} call reloads",
                    output.report.local_functions,
                    output.report.local_fallback_functions,
                    output.report.local_variables,
                    output.report.resume_bindings,
                    output.report.call_reloads
                );
            }
            eprintln!(
                "module structure: {} structured, {} goto; {} direct calls, {} dynamic calls, {} import calls; {} guarded tails, {} key switches",
                output.report.structured_functions,
                output.report.goto_functions,
                output.report.direct_calls,
                output.report.indirect_calls,
                output.report.import_calls,
                output.report.guarded_tail_transfers,
                output.report.selector_switches
            );
            print!("{}", output.code);
        } else if format == "module-c" {
            print!("{}", nirvana::module_emit::emit_c(&module)?);
        } else {
            for function in module.program.functions() {
                println!(
                    "function {} at {:#x}, {} bytes",
                    function.name, function.address, function.size
                );
            }
            for import in module.program.imports() {
                println!("import {:?} at {:#x}", import.name, import.address);
            }
            for instruction in module.program.instructions() {
                println!("{instruction:#?}");
            }
        }
        return Ok(());
    }
    let effect_mode = matches!(
        format.as_str(),
        "effects-c" | "effects-readable-c" | "effects-ir"
    ) || effect_results.is_some();
    if effect_mode {
        if raw
            || input.is_some()
            || base.is_some()
            || entry.is_some()
            || solver.is_some()
            || !coalesce_locals
            || effect_results.is_some() && format != "c"
        {
            return Err(
                "effect modes require an ELF image and separate execution or emission options"
                    .into(),
            );
        }
        let function = frontend::lift_elf_effects_auto(&bytes, &symbol)?;
        if let Some(results) = effect_results {
            let outcomes: Vec<_> = results
                .into_iter()
                .map(|r| nirvana::effects::PutsOutcome::success(u64::from(r as u32)))
                .collect();
            let mut registers = vec![0; function.program.register_count()];
            registers[x86::RSP] = function.image.stack_pointer;
            let report = function.program.run(
                &registers,
                function.image.memory_base,
                &function.image.memory,
                &outcomes,
                nirvana::effects::Limits {
                    instructions: limit,
                    ..Default::default()
                },
            )?;
            use std::io::Write as _;
            std::io::stdout().write_all(&report.output)?;
            return match report.status {
                nirvana::effects::Status::Returned(value) => {
                    eprintln!(
                        "{}: returned {value}; {} outcomes consumed",
                        nirvana::effects::MODEL_ID,
                        report.consumed
                    );
                    Ok(())
                }
                status => Err(format!(
                    "{}: {status:?}; {} outcomes consumed",
                    nirvana::effects::MODEL_ID,
                    report.consumed
                )
                .into()),
            };
        }
        if format == "effects-readable-c" {
            let output = nirvana::effects_readable::emit_image(&function.program, &function.image)?;
            if let Some(reason) = output.fallback_reason {
                eprintln!("effect structure fallback: {reason}");
            }
            print!("{}", output.code);
        } else if format == "effects-ir" {
            for instruction in function.program.instructions() {
                println!("{instruction:#?}");
            }
        } else {
            print!(
                "{}",
                nirvana::effects_emit::emit_image(&function.program, &function.image)?
            );
        }
        return Ok(());
    }
    if format == "references" {
        if raw || input.is_some() || base.is_some() || entry.is_some() {
            return Err("--emit references requires an ELF object and static inspection".into());
        }
        let analysis = nirvana::object_refs::ObjectReferences::analyze(&bytes, &symbol)?;
        print!(
            "{}",
            analysis
                .to_json()
                .ok_or("object-reference report exceeds output bound")?
        );
        return Ok(());
    }
    let (program, code, code_base) = if raw {
        let base = base.unwrap_or(0);
        (x86::lift(&bytes, base, entry.unwrap_or(base))?, bytes, base)
    } else {
        if base.is_some() || entry.is_some() {
            return Err("--base and --entry require --raw".into());
        }
        let lifted = frontend::lift_elf_auto(&bytes, &symbol)?;
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
        "ssa-c" => {
            let graph = nirvana::ssa::SsaFunction::build(&program)
                .ok_or("SSA unavailable under resource/control bounds")?;
            let lowered =
                nirvana::ssa_destroy::lower(&program, &graph, &std::collections::BTreeSet::new())?;
            let stats = lowered.stats();
            eprintln!(
                "SSA locals: {} values -> {} locals; {} edge copies, {} temporary edges",
                stats.ssa_values, stats.locals, stats.edge_copies, stats.temporary_edges
            );
            print!("{}", lowered.emit_c()?.code);
        }
        "middle-ir" => {
            let middle = nirvana::middle_ir::Function::from_low(&program)?;
            let middle = match middle.recover_memory_constants() {
                Ok((refined, _)) => refined,
                Err(
                    error @ (nirvana::middle_ir::Error::Limit(_)
                    | nirvana::middle_ir::Error::Ssa(nirvana::ssa::SsaError::Unavailable(_))
                    | nirvana::middle_ir::Error::Memory(_)),
                ) => {
                    eprintln!("middle IR memory facts unavailable: {error}");
                    middle
                }
                Err(error) => return Err(error.into()),
            };
            let middle = match middle.recover_saved_values() {
                Ok(Some((refined, _))) => refined,
                Ok(None) => middle,
                Err(
                    error @ (nirvana::middle_ir::Error::Limit(_)
                    | nirvana::middle_ir::Error::Ssa(nirvana::ssa::SsaError::Unavailable(_))
                    | nirvana::middle_ir::Error::Memory(_)),
                ) => {
                    eprintln!("middle IR saved value facts unavailable: {error}");
                    middle
                }
                Err(error) => return Err(error.into()),
            };
            print!("{}", middle.to_text()?);
        }
        "readable-c" | "middle-c" => {
            let options = readable::ReadableOptions {
                stack_register: Some(nirvana::ir::Reg(x86::RSP)),
                recover_objects: true,
                coalesce_locals,
                compact_memory: true,
            };
            let output = if let Some(solver) = loop_solver {
                let emission = if format == "middle-c" {
                    readable::loop_recovery::emit_middle_c(
                        &nirvana::middle_ir::Function::from_low(&program)?,
                        options,
                        &solver,
                    )?
                } else {
                    readable::loop_recovery::emit_readable_c(&program, options, &solver)?
                };
                eprintln!(
                    "loop recovery: {}; {:.3}s; C emission is separately tested",
                    emission
                        .retention()
                        .map_or("selected", readable::loop_recovery::Retention::kind),
                    emission.elapsed().as_secs_f64()
                );
                emission.into_selected()
            } else if let Some(solver) = solver {
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
            } else if format == "middle-c" {
                readable::emit_middle_c_with_options(
                    &nirvana::middle_ir::Function::from_low(&program)?,
                    options,
                )?
            } else {
                readable::emit_readable_c_with_options(&program, options)?
            };
            if let Some(reason) = output.fallback_reason {
                eprintln!("retaining goto control flow: {reason}");
            }
            print!("{}", output.code);
        }
        "c" => {
            let output = emit::emit_c(&program)?;
            if let Some(reason) = output.fallback_reason {
                eprintln!("retaining goto control flow: {reason}");
            }
            println!(
                "/* x86-64 machine state: {} uint64_t registers; r[0]=RAX, r[4]=RSP, r[7]=RDI. */",
                program.register_count()
            );
            print!("{}", output.code);
        }
        "types" | "record-types" => {
            let reduced = nirvana::reduce::reduce(&program)?;
            let records = nirvana::record_shapes::analyze(
                reduced.program(),
                Some(nirvana::ir::Reg(nirvana::x86::RSP)),
            );
            if format == "record-types" {
                print!("{}", records?.to_c()?);
            } else {
                let analysis = nirvana::type_infer::TypeAnalysis::analyze(reduced.program())
                    .ok_or("type-constraint analysis unavailable under resource/control bounds")?;
                let report = analysis
                    .to_json_with_records(&records)
                    .ok_or("type-constraint report exceeds output bound")?;
                print!("{report}");
            }
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

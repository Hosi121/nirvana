//! A separate linked-leaf profile: full module state, budgets and resumption.
//! Single-function scalar probe profiles retain their own ABI and contracts.
#[path = "../../tests/support/module_fixture.rs"]
#[allow(dead_code)]
mod fixtures;
#[path = "../evaluation/json.rs"]
mod json;
#[path = "../../tests/support/native.rs"]
#[allow(dead_code)]
mod native;

use nirvana::{
    linked_elf::LinkedOptions,
    module_ir::{self, Limits, Module, RejectImports, Status},
};
use std::{
    error::Error,
    fmt::Write,
    path::{Path, PathBuf},
};

fn rows(path: &Path) -> Result<Vec<[u64; 4]>, Box<dyn Error>> {
    let text = std::fs::read_to_string(path)?;
    let rows: Vec<_> = text
        .lines()
        .map(|line| {
            line.split_whitespace()
                .map(str::parse::<u64>)
                .collect::<Result<Vec<_>, _>>()?
                .try_into()
                .map_err(|_| "expected four state words".into())
        })
        .collect::<Result<_, Box<dyn Error>>>()?;
    if rows.is_empty() || rows.len() > 256 {
        return Err("require 1..256 state vectors".into());
    }
    Ok(rows)
}

fn text_rows(rows: &[Vec<u64>]) -> String {
    rows.iter()
        .map(|row| row.iter().map(u64::to_string).collect::<Vec<_>>().join(" ") + "\n")
        .collect()
}

fn check(
    module: &Module,
    inputs: &[[u64; 4]],
    native_rows: Option<&[Vec<u64>]>,
    out: &Path,
) -> String {
    let root = module
        .program
        .functions()
        .iter()
        .find(|f| f.name == "fixture")
        .unwrap();
    let root_steps = module
        .program
        .instructions()
        .iter()
        .filter(|i| root.address <= i.address() && i.address() < root.address + root.size)
        .count();
    let wanted = inputs.len() + root_steps * 7;
    if root_steps > 256
        || wanted > 4096
        || module
            .image
            .memory
            .len()
            .checked_mul(wanted)
            .is_none_or(|n| n > 128 * 1024 * 1024)
    {
        return "\"status\":\"budget_exhausted\",\"reason\":\"linked-leaf case/RAM budget\"".into();
    }
    let mut cases: Vec<_> = inputs
        .iter()
        .map(|&input| fixtures::Case {
            input,
            pc: module.program.entry(),
            budget: 1024,
            patch: None,
        })
        .collect();
    for (ordinal, instruction) in module
        .program
        .instructions()
        .iter()
        .filter(|i| root.address <= i.address() && i.address() < root.address + root.size)
        .enumerate()
    {
        for budget in [0, 1, 2, 4, 8, 16, 32] {
            cases.push(fixtures::Case {
                input: inputs[ordinal % inputs.len()],
                pc: instruction.address(),
                budget,
                patch: None,
            });
        }
    }
    let mut initial = module.initial_registers();
    for (i, register) in initial.iter_mut().enumerate() {
        if i != 4 {
            *register = 0x9e3779b97f4a7c15_u64.wrapping_mul(i as u64 + 1);
        }
    }
    for i in [16, 17, 18, 19, 20, 29] {
        initial[i] &= 1;
    }
    initial[29] = 0;
    std::fs::write(
        out.join("initial-registers.bin"),
        initial
            .iter()
            .flat_map(|v| v.to_le_bytes())
            .collect::<Vec<_>>(),
    )
    .unwrap();
    let mut expected = Vec::new();
    let mut memories = Vec::new();
    let mut native_compared = 0;
    let mut descriptors = String::new();
    for (ordinal, case) in cases.iter().enumerate() {
        let (registers, memory) = fixtures::prepare_with_state(module, case, Some(&initial));
        let result = module
            .program
            .run_from(
                case.pc,
                &registers,
                module.image.memory_base,
                &memory,
                Limits {
                    instructions: case.budget,
                    imports: 0,
                },
                &mut RejectImports,
            )
            .unwrap();
        let (row, status) = fixtures::expected_with_state(module, case, Some(&initial));
        if ordinal < inputs.len()
            && matches!(status, Status::Returned(_))
            && let Some(native_rows) = native_rows
        {
            assert_eq!(&row[..5], native_rows[ordinal], "native input {ordinal}");
            native_compared += 1;
        }
        writeln!(
            descriptors,
            "{} {} {} {} {} {}",
            case.input[0], case.input[1], case.input[2], case.input[3], case.pc, case.budget
        )
        .unwrap();
        std::fs::write(
            out.join(format!("memory-{ordinal:04}.bin")),
            &result.state.memory,
        )
        .unwrap();
        expected.push(row);
        memories.push(result.state.memory);
    }
    std::fs::write(out.join("cases.tsv"), descriptors).unwrap();
    std::fs::write(out.join("expected.tsv"), text_rows(&expected)).unwrap();
    let selected = nirvana::module_readable::emit_c_with_locals(module).unwrap();
    std::fs::write(out.join("selected.c"), selected.code).unwrap();
    let generated =
        fixtures::check_generated_with_memory(module, &cases, &expected, &memories, out, &initial);
    format!(
        "\"status\":\"passed\",\"model\":{},\"entry\":{},\"memory_base\":{},\"memory_size\":{},\"state_pointer\":{},\"input_vectors\":{},\"cases\":{},\"native_compared\":{},\"native_inconclusive\":{},\"generated_compared\":{},\"checked_ram_bytes\":{},\"resumption_cases\":{}",
        json::quote(module.program.model_id()),
        module.program.entry(),
        module.image.memory_base,
        module.image.memory.len(),
        fixtures::state_address(module),
        inputs.len(),
        cases.len(),
        native_compared,
        if native_rows.is_some() {
            inputs.len() - native_compared
        } else {
            0
        },
        generated,
        memories.iter().map(Vec::len).sum::<usize>() * (generated / cases.len()),
        cases.len() - inputs.len()
    )
}

pub(super) fn run(mut args: impl Iterator<Item = String>) -> Result<(), Box<dyn Error>> {
    let started = std::time::Instant::now();
    let elf = PathBuf::from(
        args.next()
            .ok_or("--module requires ELF INPUTS NEW_OUT [NATIVE_ORACLE]")?,
    );
    let input_file = PathBuf::from(args.next().ok_or("state input file required")?);
    let out = PathBuf::from(args.next().ok_or("output directory required")?);
    let oracle = args.next();
    if args.next().is_some() {
        return Err("unexpected module profile argument".into());
    }
    let inputs = rows(&input_file)?;
    std::fs::create_dir_all(&out)?;
    if std::fs::read_dir(&out)?.next().is_some() {
        return Err("preserve earlier evidence; output must be empty".into());
    }
    let bytes = std::fs::read(&elf)?;
    std::fs::write(out.join("input.elf"), &bytes)?;
    std::fs::copy(input_file, out.join("inputs.txt"))?;
    let kind = bytes.get(16..18).ok_or("truncated ELF header")?;
    let bias = match u16::from_le_bytes(kind.try_into().unwrap()) {
        2 => 0,
        3 => 0x10000,
        _ => return Err("module profile requires a linked ELF".into()),
    };
    let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let native_rows = oracle.as_ref().map(|path| {
            let input = inputs
                .iter()
                .map(|row| row.iter().map(u64::to_string).collect::<Vec<_>>().join(" ") + "\n")
                .collect::<String>();
            let rows = native::run_fields(Path::new(path), &input, 5);
            assert_eq!(rows.len(), inputs.len());
            std::fs::write(out.join("native-observed.tsv"), text_rows(&rows)).unwrap();
            rows
        });
        match module_ir::lift_elf(
            &bytes,
            "fixture",
            LinkedOptions {
                load_bias: bias,
                ..Default::default()
            },
        ) {
            Err(error) => format!(
                "\"status\":\"unsupported\",\"reason\":{}",
                json::quote(&error.to_string())
            ),
            Ok(module) => check(&module, &inputs, native_rows.as_deref(), &out),
        }
    }));
    let status = match outcome {
        Ok(status) => status,
        Err(error) => {
            let reason = error
                .downcast_ref::<String>()
                .map(String::as_str)
                .or_else(|| error.downcast_ref::<&str>().copied())
                .unwrap_or("module observer failure");
            format!(
                "\"status\":\"evaluator_error\",\"reason\":{}",
                json::quote(reason)
            )
        }
    };
    let report = format!(
        "{{\"schema\":\"nirvana-module-evaluation-v1\",\"profile\":\"linked-leaf-state4-full-state-v1\",\"build\":{},\"requested_vectors\":{},\"native_requested\":{},\"stack_size\":65536,\"load_bias\":{},\"native_oracle\":{},\"wall_milliseconds\":{},\"limits\":{{\"root_instructions\":256,\"cases\":4096,\"expected_ram_bytes\":134217728}},{status}}}\n",
        json::quote(nirvana::BUILD_VERSION),
        inputs.len(),
        if oracle.is_some() { inputs.len() } else { 0 },
        bias,
        oracle.as_deref().map_or("null".into(), json::quote),
        started.elapsed().as_millis(),
    );
    std::fs::write(out.join("report.json"), &report)?;
    print!("{report}");
    Ok(())
}

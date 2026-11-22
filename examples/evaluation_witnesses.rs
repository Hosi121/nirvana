//! Find or classify unobserved CFG transfers for the M0 fixed valid-pointer ABI.
//! usage: evaluation_witnesses FILE.o INPUTS.txt NEW_OUT [QUERY_LIMIT] [TIMEOUT_MS] [STEP_LIMIT]
#[path = "evaluation/fixture.rs"]
mod fixture;
use fixture::{BASE, POINTER, SIZE, STACK};
use nirvana::{
    block_verify::paths::{self, InputProfile, Reachability, SymbolicWord},
    cfg::Target,
    elf, frontend,
    ir::{Program, RunReport, RunStatus, Width},
    verify::Solver,
};
use std::{collections::BTreeSet, fmt::Write, path::PathBuf, time::Duration};

fn quote(value: &str) -> String {
    let mut out = String::from("\"");
    for ch in value.chars() {
        match ch {
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            c if c < ' ' => write!(out, "\\u{:04x}", c as u32).unwrap(),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}
fn run(program: &Program, words: [u64; 4], limit: usize) -> RunReport {
    program
        .run_with_memory(
            &fixture::registers(program.register_count(), POINTER),
            BASE,
            &fixture::memory(words, POINTER),
            limit,
        )
        .expect("validated fixed profile")
}
fn inputs_text(inputs: &[[u64; 4]]) -> String {
    inputs
        .iter()
        .map(|v| format!("{} {} {} {}\n", v[0], v[1], v[2], v[3]))
        .collect()
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut args = std::env::args_os().skip(1);
    let object = PathBuf::from(args.next().ok_or("object required")?);
    let input_file = PathBuf::from(args.next().ok_or("input file required")?);
    let out = PathBuf::from(args.next().ok_or("new output directory required")?);
    let query_limit: usize = args
        .next()
        .map(|s| s.to_str().unwrap_or("").parse())
        .transpose()?
        .unwrap_or(64);
    let timeout_ms: u64 = args
        .next()
        .map(|s| s.to_str().unwrap_or("").parse())
        .transpose()?
        .unwrap_or(2000);
    let solver = Solver::new(std::env::var_os("NIRVANA_Z3").unwrap_or_else(|| "z3".into()))
        .with_timeout(Duration::from_millis(timeout_ms));
    let step_limit: usize = args
        .next()
        .map(|s| s.to_str().unwrap_or("").parse())
        .transpose()?
        .unwrap_or(4096);
    if args.next().is_some()
        || !(1..=256).contains(&query_limit)
        || !(1..=16384).contains(&step_limit)
        || !(1..=5000).contains(&timeout_ms)
    {
        return Err("invalid query/step limits".into());
    }
    let bytes = std::fs::read(&object)?;
    let seed_text = std::fs::read_to_string(&input_file)?;
    if bytes.len() > 32 * 1024 * 1024 || seed_text.len() > 65536 {
        return Err("excessive input size".into());
    }
    let context = elf::read_function_context(&bytes, "fixture")?;
    if context
        .sections
        .iter()
        .filter_map(|s| s.name)
        .any(|n| n.starts_with(".debug") || n.starts_with(".zdebug") || n == ".gnu_debugdata")
    {
        return Err("path generation requires the original nondebug object".into());
    }
    let program = frontend::lift_elf_auto(&bytes, "fixture")?.program;
    let mut inputs = Vec::new();
    for line in seed_text.lines() {
        let v = line
            .split_whitespace()
            .map(str::parse)
            .collect::<Result<Vec<u64>, _>>()?;
        inputs.push(<[u64; 4]>::try_from(v).map_err(|_| "expected four unsigned words")?);
    }
    if !(1..=256).contains(&inputs.len()) {
        return Err("expected 1..256 input vectors".into());
    }
    if out.exists() && out.read_dir()?.next().is_some() {
        return Err("output directory must be new or empty".into());
    }
    std::fs::create_dir_all(&out)?;
    std::fs::write(out.join("input.o"), &bytes)?;
    std::fs::write(out.join("seed-inputs.txt"), &seed_text)?;
    let seed_count = inputs.len();
    let mut traces: Vec<_> = inputs
        .iter()
        .map(|&v| run(&program, v, step_limit).state.trace)
        .collect();
    let cfg = program.cfg();
    let edges: BTreeSet<_> = cfg
        .reachable_blocks()
        .iter()
        .flat_map(|id| {
            let block = cfg.block(*id);
            let from = program.instructions()[block.instructions.end - 1].address;
            block.successors.iter().filter_map(move |e| match e.target {
                Target::Block(to) => Some((from, cfg.block(to).start)),
                _ => None,
            })
        })
        .collect();
    let mut observed: BTreeSet<_> = traces
        .iter()
        .flat_map(|t| {
            t.windows(2)
                .map(|w| (w[0], w[1]))
                .filter(|p| edges.contains(p))
        })
        .collect();
    let baseline = observed.len();
    let unobserved: Vec<_> = edges.difference(&observed).copied().collect();
    let profile = InputProfile {
        registers: fixture::registers(program.register_count(), POINTER),
        memory_base: BASE,
        memory: fixture::memory([0; 4], POINTER),
        words: (0..4)
            .map(|n| SymbolicWord {
                offset: 128 + n * 8,
                width: Width::U64,
            })
            .collect(),
    };
    let mut queries = Vec::new();
    let mut rows = Vec::new();
    for (from, to) in unobserved {
        if observed.contains(&(from, to)) {
            rows.push(format!(
                "{{\"from\":{from},\"to\":{to},\"status\":\"covered_by_new_input\"}}"
            ));
            continue;
        }
        let (prefixes, exhaustive, enumeration) = match paths::dag_prefixes_to(&program, from, 256)
        {
            Ok(prefixes) => (prefixes, true, "\"complete_dag\"".into()),
            Err(reason) => {
                let prefixes: BTreeSet<_> = traces
                    .iter()
                    .flat_map(|trace| {
                        trace
                            .iter()
                            .enumerate()
                            .filter(|&(i, pc)| *pc == from && i < 1024)
                            .map(|(i, _)| trace[..=i].to_vec())
                    })
                    .take(256)
                    .collect();
                (
                    prefixes.into_iter().collect(),
                    false,
                    quote(&format!("observed_only: {reason:?}")),
                )
            }
        };
        let mut unsat = 0;
        let mut attempted = 0;
        let mut witness = false;
        let mut returned_witness = false;
        for prefix in &prefixes {
            if queries.len() >= query_limit {
                break;
            }
            let id = queries.len();
            let stem = format!("query-{id:03}");
            let result = if prefix.len() >= step_limit {
                Reachability::Unknown(nirvana::verify::UnknownReason::ResourceLimit)
            } else {
                match paths::path_query(&program, &profile, prefix, to) {
                    Ok(query) => {
                        std::fs::write(
                            out.join(format!("{stem}.smt2")),
                            format!("{}(check-sat)\n", query.smt2()),
                        )?;
                        query.check(&solver)
                    }
                    Err(reason) => Reachability::Unknown(reason),
                }
            };
            std::fs::write(out.join(format!("{stem}.out")), format!("{result:?}\n"))?;
            attempted += 1;
            let (status, detail) = match result {
                Reachability::InfeasiblePrefix => {
                    unsat += 1;
                    ("infeasible_prefix", "null".into())
                }
                Reachability::Unknown(reason) => ("unknown", quote(&format!("{reason:?}"))),
                Reachability::Witness(w) => {
                    let words = <[u64; 4]>::try_from(w.words).expect("fixed profile");
                    witness = true;
                    let replay = run(&program, words, step_limit);
                    returned_witness = matches!(replay.status, RunStatus::Returned(_));
                    std::fs::write(
                        out.join(format!("{stem}.replay.txt")),
                        format!("{replay:?}\n"),
                    )?;
                    if returned_witness && !inputs.contains(&words) && inputs.len() < 256 {
                        let trace = replay.state.trace;
                        observed.extend(
                            trace
                                .windows(2)
                                .map(|p| (p[0], p[1]))
                                .filter(|p| edges.contains(p)),
                        );
                        traces.push(trace);
                        inputs.push(words);
                    }
                    (
                        if returned_witness {
                            "replayed_witness"
                        } else {
                            "prefix_witness_without_return"
                        },
                        format!("{words:?}"),
                    )
                }
            };
            queries.push(format!("{{\"id\":{id},\"from\":{from},\"to\":{to},\"prefix\":{prefix:?},\"status\":\"{status}\",\"detail\":{detail}}}"));
            if witness {
                break;
            }
        }
        let status = if witness {
            if returned_witness {
                "witness"
            } else {
                "witness_without_return"
            }
        } else if exhaustive && unsat == prefixes.len() {
            "infeasible_dag"
        } else {
            "not_proved"
        };
        rows.push(format!("{{\"from\":{from},\"to\":{to},\"status\":\"{status}\",\"enumeration\":{enumeration},\"prefixes\":{},\"attempted\":{attempted},\"unsat\":{unsat}}}", prefixes.len()));
    }
    std::fs::write(out.join("inputs.txt"), inputs_text(&inputs))?;
    let remaining: Vec<_> = edges
        .difference(&observed)
        .map(|&(a, b)| format!("[{a},{b}]"))
        .collect();
    let report = format!(
        "{{\"schema\":\"nirvana-evaluation-paths-v1\",\"model\":\"{}\",\"profile\":{{\"base\":{BASE},\"size\":{SIZE},\"pointer\":{POINTER},\"stack\":{STACK},\"valid_pointer_only\":true}},\"seed_vectors\":{seed_count},\"output_vectors\":{},\"query_limit\":{query_limit},\"timeout_ms\":{timeout_ms},\"step_limit\":{step_limit},\"syntactic_transfers\":{},\"observed_before\":{baseline},\"observed_after\":{},\"remaining\":[{}],\"edges\":[{}],\"queries\":[{}]}}\n",
        paths::MODEL_ID,
        inputs.len(),
        edges.len(),
        observed.len(),
        remaining.join(","),
        rows.join(","),
        queries.join(",")
    );
    std::fs::write(out.join("report.json"), report)?;
    println!(
        "{} -> {} / {} transfers, {} -> {} inputs, {} queries",
        baseline,
        observed.len(),
        edges.len(),
        seed_count,
        inputs.len(),
        queries.len()
    );
    Ok(())
}

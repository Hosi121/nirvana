//! Find fixture-state4 inputs by flipping a retained concrete Low IR branch.
//! Solver models are accepted only after replay through the original program
//! with the fixed 512-byte ABI memory. UNSAT concerns the chosen prefix only.
use nirvana::{
    block_verify::{self, BlockVerdict},
    frontend,
    ir::{
        Assignment, BinaryOp as B, BlockExit, Control, Expr, IrInstruction, Place, Program, Reg,
        RunReport, RunStatus, Width,
    },
    verify::Solver,
    x86,
};
use std::{collections::BTreeSet, fmt::Write, time::Duration};
const BASE: u64 = 4096;
const POINTER: u64 = 4224;
const STACK: u64 = 4600;
fn r(n: usize) -> Expr {
    Expr::Register(Reg(n))
}
fn c(n: u64) -> Expr {
    Expr::Const(n)
}
fn assign(n: usize, value: Expr) -> Assignment {
    Assignment {
        destination: Reg(n).into(),
        value,
    }
}
fn store(address: u64, value: Expr) -> Assignment {
    Assignment {
        destination: Place::Memory {
            address: c(address),
            width: Width::U64,
        },
        value,
    }
}
fn execute(source: &Program, words: [u64; 4]) -> RunReport {
    let mut memory: Vec<_> = (0..512).map(|n| (n * 29 + 7) as u8).collect();
    for (n, value) in words.into_iter().enumerate() {
        memory[128 + n * 8..136 + n * 8].copy_from_slice(&value.to_le_bytes());
    }
    let mut registers = vec![0; source.register_count()];
    registers[x86::RDI] = POINTER;
    registers[x86::RSP] = STACK;
    source
        .run_with_memory(&registers, BASE, &memory, 4096)
        .unwrap()
}
fn prefix(source: &Program, trace: &[u64], wanted: u64) -> (Program, Program) {
    assert!(!trace.is_empty() && trace.len() <= 128);
    let count = source.register_count();
    let guard = count + 4;
    let mut init: Vec<_> = (0..count).map(|n| assign(n, c(0))).collect();
    init.extend([
        assign(x86::RDI, c(POINTER)),
        assign(x86::RSP, c(STACK)),
        assign(guard, c(1)),
    ]);
    for n in 0..64 {
        let bytes = std::array::from_fn(|i| ((n * 8 + i) * 29 + 7) as u8);
        init.push(store(BASE + n as u64 * 8, c(u64::from_le_bytes(bytes))));
    }
    for n in 0..4 {
        init.push(store(POINTER + n as u64 * 8, r(count + n)));
    }
    let mut rows = vec![IrInstruction {
        address: 0,
        size: 1,
        assignments: init,
        control: Control::Next,
    }];
    for (n, pc) in trace.iter().enumerate() {
        let original = source
            .instructions()
            .iter()
            .find(|i| i.address == *pc)
            .unwrap();
        let mut assignments = original.assignments.clone();
        if let Control::Branch { condition, target } = &original.control {
            let next = trace.get(n + 1).copied().unwrap_or(wanted);
            let op = if next == *target {
                B::Ne
            } else {
                assert_eq!(next, *pc + u64::from(original.size));
                B::Eq
            };
            assignments.push(assign(
                guard,
                Expr::binary(B::And, r(guard), Expr::binary(op, condition.clone(), c(0))),
            ));
        }
        rows.push(IrInstruction {
            address: n as u64 + 1,
            size: 1,
            assignments,
            control: Control::Next,
        });
    }
    rows.last_mut().unwrap().control = Control::Return(r(guard));
    let before = Program::new(0, count + 5, rows.clone()).unwrap();
    rows.last_mut().unwrap().control = Control::Return(c(0));
    (before, Program::new(0, count + 5, rows).unwrap())
}
fn witnessed(source: &Program, words: [u64; 4], trace: &[u64], wanted: u64) -> bool {
    let report = execute(source, words);
    matches!(report.status, RunStatus::Returned(_))
        && report.state.trace.starts_with(trace)
        && report.state.trace.get(trace.len()) == Some(&wanted)
}
fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut args = std::env::args().skip(1);
    let object = args.next().ok_or("object")?;
    let inputs = args.next().ok_or("native input rows")?;
    let out = std::path::PathBuf::from(args.next().ok_or("output directory")?);
    let max_queries: usize = args.next().ok_or("max queries")?.parse()?;
    let timeout: u64 = args.next().ok_or("per-query milliseconds")?.parse()?;
    if args.next().is_some() || !(1..=64).contains(&max_queries) || !(1..=5000).contains(&timeout) {
        return Err("invalid bounded witness campaign".into());
    }
    std::fs::create_dir_all(&out)?;
    if std::fs::read_dir(&out)?.next().is_some() {
        return Err("preserve previous witness campaign".into());
    }
    let source = frontend::lift_elf_auto(&std::fs::read(object)?, "fixture")?.program;
    let mut vectors = Vec::new();
    for line in std::fs::read_to_string(inputs)?.lines() {
        let words = line
            .split_whitespace()
            .map(str::parse)
            .collect::<Result<Vec<u64>, _>>()?;
        let words: [u64; 4] = words.try_into().map_err(|_| "four input words")?;
        if !vectors.contains(&words) {
            vectors.push(words);
        }
    }
    if !(1..=256).contains(&vectors.len()) {
        return Err("input-vector budget".into());
    }
    let initial = vectors.len();
    let solver = Solver::new(std::env::var("NIRVANA_Z3").unwrap_or_else(|_| "z3".into()))
        .with_timeout(Duration::from_millis(timeout));
    let mut observed = BTreeSet::new();
    let mut traces = Vec::new();
    for words in &vectors {
        let report = execute(&source, *words);
        observed.extend(report.state.trace.windows(2).map(|p| (p[0], p[1])));
        traces.push(report.state.trace);
    }
    let mut attempts = BTreeSet::new();
    let mut records = Vec::new();
    let mut cursor = 0;
    while cursor < traces.len() && records.len() < max_queries && vectors.len() < 256 {
        let trace = traces[cursor].clone();
        cursor += 1;
        for index in 0..trace.len().saturating_sub(1).min(128) {
            if records.len() >= max_queries || vectors.len() >= 256 {
                break;
            }
            let pc = trace[index];
            let instruction = source
                .instructions()
                .iter()
                .find(|i| i.address == pc)
                .unwrap();
            let Control::Branch { target, .. } = instruction.control else {
                continue;
            };
            let wanted = if trace[index + 1] == target {
                pc + u64::from(instruction.size)
            } else {
                target
            };
            let path = &trace[..=index];
            if observed.contains(&(pc, wanted)) || !attempts.insert((path.to_vec(), wanted)) {
                continue;
            }
            let id = records.len();
            let (a, b) = prefix(&source, path, wanted);
            let shared: Vec<_> = (source.register_count()..source.register_count() + 4)
                .map(Reg)
                .collect();
            let query = block_verify::block_query(&a, &b, 0, &shared, &[])
                .map_err(|e| format!("prefix query: {e:?}"))?;
            std::fs::write(
                out.join(format!("{id}.smt2")),
                format!(
                    "; concolic-fixture-prefix-v1: initialized RAM; source prefix {path:?}; target {wanted}\n{}(check-sat)\n",
                    query.smt2()
                ),
            )?;
            let verdict = query.check(&solver);
            std::fs::write(out.join(format!("{id}.out")), format!("{verdict:?}\n"))?;
            let mut words_json = "null".to_string();
            let status = match verdict {
                BlockVerdict::EquivalentUnderModel => "prefix_unsat",
                BlockVerdict::Unknown(_) => "unknown",
                BlockVerdict::Counterexample(w) => {
                    let words =
                        std::array::from_fn(|n| w.before_registers[source.register_count() + n]);
                    std::fs::write(
                        out.join(format!("{id}.replay.txt")),
                        format!(
                            "input={words:?}\nprefix={path:?}, target={wanted}\nactual={:?}\n",
                            execute(&source, words)
                        ),
                    )?;
                    words_json = format!("{words:?}");
                    if w.before.exit != BlockExit::Returned(1)
                        || !witnessed(&source, words, path, wanted)
                    {
                        "replay_rejected"
                    } else if vectors.contains(&words) {
                        "already_present"
                    } else {
                        let report = execute(&source, words);
                        observed.extend(report.state.trace.windows(2).map(|p| (p[0], p[1])));
                        traces.push(report.state.trace);
                        vectors.push(words);
                        "new_input"
                    }
                }
            };
            records.push(format!("{{\"id\":{id},\"from\":{pc},\"target\":{wanted},\"status\":\"{status}\",\"words\":{words_json}}}"));
        }
    }
    let mut text = String::new();
    for words in &vectors {
        writeln!(text, "{} {} {} {}", words[0], words[1], words[2], words[3])?;
    }
    std::fs::write(out.join("inputs.txt"), text)?;
    let report = format!(
        "{{\"schema\":\"nirvana-fixture-prefix-witnesses-v1\",\"model\":\"{}\",\"initial_vectors\":{initial},\"vectors\":{},\"max_queries\":{max_queries},\"timeout_ms\":{timeout},\"attempts\":[{}]}}",
        block_verify::MODEL_ID,
        vectors.len(),
        records.join(",")
    );
    std::fs::write(out.join("report.json"), &report)?;
    println!("{report}");
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    fn source() -> Program {
        Program::new(
            0,
            32,
            vec![
                IrInstruction {
                    address: 0,
                    size: 1,
                    assignments: vec![assign(0, Expr::load(r(x86::RDI), Width::U64))],
                    control: Control::Next,
                },
                IrInstruction {
                    address: 1,
                    size: 1,
                    assignments: vec![],
                    control: Control::Branch {
                        condition: Expr::binary(B::Eq, r(0), c(2)),
                        target: 3,
                    },
                },
                IrInstruction {
                    address: 2,
                    size: 1,
                    assignments: vec![],
                    control: Control::Return(c(0)),
                },
                IrInstruction {
                    address: 3,
                    size: 1,
                    assignments: vec![],
                    control: Control::Return(c(1)),
                },
            ],
        )
        .unwrap()
    }
    #[test]
    fn replay_requires_the_exact_prefix_transfer_and_a_returned_fixture() {
        let p = source();
        assert!(witnessed(&p, [2, 0, 0, 0], &[0, 1], 3));
        assert!(!witnessed(&p, [1, 0, 0, 0], &[0, 1], 3));
        assert!(!witnessed(&p, [2, 0, 0, 0], &[1], 3));
    }
    #[test]
    #[ignore = "requires Z3; set NIRVANA_Z3"]
    fn threshold_model_produces_a_replayed_new_fixture_input() {
        let p = source();
        let (a, b) = prefix(&p, &[0, 1], 3);
        let shared = (32..36).map(Reg).collect::<Vec<_>>();
        let q = block_verify::block_query(&a, &b, 0, &shared, &[]).unwrap();
        let solver = Solver::new(std::env::var("NIRVANA_Z3").unwrap_or_else(|_| "z3".into()));
        let BlockVerdict::Counterexample(w) = q.check(&solver) else {
            panic!("threshold witness")
        };
        let words = std::array::from_fn(|n| w.before_registers[32 + n]);
        assert_eq!(words[0], 2);
        assert!(witnessed(&p, words, &[0, 1], 3));
    }
}

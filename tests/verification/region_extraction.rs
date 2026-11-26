//! Opt-in actual compiler-region extraction trial; inputs and compiler stay external.
use nirvana::block_verify::region::extraction::{Exit, Region, extract};
use nirvana::block_verify::region::{Verdict, query};
use nirvana::control_flow::{
    analysis::ControlFlowAnalysis,
    cfg::Target,
    postdom::{PostDomNode, PostDominators},
};
use nirvana::dataflow::value_width::ValueWidths;
use nirvana::ir::{BlockExit, MemoryFault, Program, Reg, RunStatus};
use nirvana::verify::Solver;
use std::collections::BTreeSet;
#[derive(Debug, Eq, PartialEq)]
enum Outcome {
    Boundary(u64),
    Returned(u64),
    Fault(MemoryFault),
}
fn original(
    source: &Program,
    slice: &Region,
    input: &[u64],
    base: u64,
    memory: &[u8],
) -> (Outcome, Vec<u64>, Vec<u8>) {
    let mut pc = slice.source_entry();
    let mut registers = input.to_vec();
    let mut memory = memory.to_vec();
    for _ in 0..256 {
        let report = source
            .run_block_with_memory(pc, &registers, base, &memory)
            .unwrap();
        registers = report.state.registers;
        memory = report.state.memory;
        match report.exit {
            BlockExit::Returned(value) => return (Outcome::Returned(value), registers, memory),
            BlockExit::Fault(fault) => return (Outcome::Fault(fault), registers, memory),
            BlockExit::Next(next) if slice.continuations().contains(&next) => {
                return (Outcome::Boundary(next), registers, memory);
            }
            BlockExit::Next(next) => pc = next,
        }
    }
    panic!("source slice did not reach a boundary");
}
fn compare(source: &Program, slice: &Region, input: &[u64], base: u64, memory: &[u8]) {
    for (&value, &bits) in input.iter().zip(slice.input_bit_caps()) {
        assert!(
            bits == 64 || value < 1u64 << bits,
            "input violates certified entry cap"
        );
    }
    let (expected, registers, expected_memory) = original(source, slice, input, base, memory);
    let mut extended = input.to_vec();
    extended.push(0);
    let actual = slice
        .program()
        .run_with_memory(&extended, base, memory, 256)
        .unwrap();
    let outcome = match actual.status {
        RunStatus::Returned(tag) => match slice.exit(tag).unwrap() {
            Exit::ContinueAt(pc) => Outcome::Boundary(pc),
            Exit::FunctionReturn => {
                Outcome::Returned(actual.state.registers[slice.return_register().0])
            }
        },
        RunStatus::Fault(fault) => Outcome::Fault(fault),
        RunStatus::Suspended => panic!("extracted DAG suspended"),
    };
    assert_eq!(outcome, expected);
    assert_eq!(actual.state.memory, expected_memory);
    assert_eq!(
        &actual.state.registers[..source.register_count()],
        registers
    );
}

#[test]
#[ignore]
fn actual_compiler_region_extraction_probe() {
    let directory = std::path::PathBuf::from(std::env::var("NIRVANA_REGION_OUTPUT").unwrap());
    std::fs::create_dir_all(&directory).unwrap();
    let bytes = std::fs::read(std::env::var("NIRVANA_REGION_OBJECT").unwrap()).unwrap();
    let source = nirvana::binary::frontend::lift_elf_auto(&bytes, "fixture")
        .unwrap()
        .program;
    let analysis = ControlFlowAnalysis::compute(source.cfg()).unwrap();
    let natural = analysis
        .natural_loops()
        .iter()
        .max_by_key(|l| l.body.len())
        .unwrap();
    let exits: BTreeSet<_> = natural
        .body
        .iter()
        .flat_map(|&id| source.cfg().block(id).successors.iter())
        .filter_map(|e| {
            if let Target::Block(to) = e.target {
                (!natural.body.contains(&to)).then_some(to)
            } else {
                None
            }
        })
        .collect();
    let postdom = PostDominators::compute(source.cfg()).unwrap();
    let PostDomNode::Block(follow) = postdom
        .nearest_common_post_dominator(&exits.iter().copied().collect::<Vec<_>>())
        .unwrap()
    else {
        panic!("no follow");
    };
    let widths = ValueWidths::analyze(&source);
    let entry = source.cfg().block(natural.header).start;
    let follow = source.cfg().block(follow).start;
    let slice = extract(&source, entry, &[entry, follow], Some(&widths)).unwrap();
    println!(
        "ACTUAL source_steps={} source_regs={} header={} follow={} region_steps={} region_regs={} caps={:?}",
        source.instructions().len(),
        source.register_count(),
        slice.source_entry(),
        follow,
        slice.program().instructions().len(),
        slice.program().register_count(),
        slice.input_bit_caps()
    );
    std::fs::write(
        directory.join("region.ir"),
        format!("{:#?}", slice.program().instructions()),
    )
    .unwrap();
    let text = std::fs::read_to_string("tools/corpora/structure-nested-v1.inputs.txt").unwrap();
    let mut comparisons = 0;
    let mut inputs = 0;
    for line in text.lines().filter(|l| !l.trim().is_empty()) {
        inputs += 1;
        let words: Vec<u64> = line
            .split_whitespace()
            .map(|s| s.parse().unwrap())
            .collect();
        assert_eq!(words.len(), 4);
        let mut memory: Vec<_> = (0..512usize).map(|i| (i * 29 + 7) as u8).collect();
        for (n, value) in words.iter().enumerate() {
            memory[128 + n * 8..136 + n * 8].copy_from_slice(&value.to_le_bytes());
        }
        let mut input = vec![0; source.register_count()];
        input[nirvana::binary::x86::RDI] = 4224;
        input[nirvana::binary::x86::RSP] = 4600;
        let full = source.run_with_memory(&input, 4096, &memory, 4096).unwrap();
        assert!(matches!(full.status, RunStatus::Returned(_)));
        for (budget, &pc) in full.state.trace.iter().enumerate() {
            if pc != slice.source_entry() {
                continue;
            }
            let snapshot = source
                .run_with_memory(&input, 4096, &memory, budget)
                .unwrap();
            for pointer in [4224, 4095, 4608, u64::MAX] {
                let mut entry = snapshot.state.registers.clone();
                entry[nirvana::binary::x86::RDI] = pointer;
                compare(&source, &slice, &entry, 4096, &snapshot.state.memory);
                comparisons += 1;
            }
            compare(&source, &slice, &snapshot.state.registers, 4096, &[]);
            comparisons += 1;
        }
    }
    assert_eq!(inputs, 65);
    assert!(comparisons > 0);
    println!("ACTUAL concrete_region_comparisons={comparisons}");
    let shared: Vec<_> = (0..source.register_count()).map(Reg).collect();
    let outputs: Vec<_> = (0..slice.program().register_count()).map(Reg).collect();
    let q = query(slice.program(), slice.program(), &shared, &outputs).unwrap();
    std::fs::write(directory.join("identity.smt2"), q.smt2()).unwrap();
    let solver = Solver::new(std::env::var("NIRVANA_Z3").unwrap())
        .with_timeout(std::time::Duration::from_secs(5));
    let now = std::time::Instant::now();
    let verdict = q.check(&solver);
    assert_eq!(verdict, Verdict::EquivalentUnderModel);
    println!(
        "ACTUAL self_verdict={verdict:?} bytes={} ms={}",
        q.smt2().len(),
        now.elapsed().as_millis()
    );
}

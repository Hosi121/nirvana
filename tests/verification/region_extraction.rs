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

fn iteration(source: &Program) -> Region {
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
    let widths = ValueWidths::analyze(source);
    let entry = source.cfg().block(natural.header).start;
    let follow = source.cfg().block(follow).start;
    extract(source, entry, &[entry, follow], Some(&widths)).unwrap()
}

fn fixture_states(registers: usize) -> Vec<(Vec<u64>, Vec<u8>)> {
    let text = std::fs::read_to_string("tools/corpora/structure-nested-v1.inputs.txt").unwrap();
    let states: Vec<_> = text
        .lines()
        .filter(|line| !line.trim().is_empty())
        .map(|line| {
            let words: Vec<u64> = line
                .split_whitespace()
                .map(|s| s.parse().unwrap())
                .collect();
            assert_eq!(words.len(), 4);
            let mut memory: Vec<_> = (0..512usize).map(|i| (i * 29 + 7) as u8).collect();
            for (n, value) in words.iter().enumerate() {
                memory[128 + n * 8..136 + n * 8].copy_from_slice(&value.to_le_bytes());
            }
            let mut input = vec![0; registers];
            input[nirvana::binary::x86::RDI] = 4224;
            input[nirvana::binary::x86::RSP] = 4600;
            (input, memory)
        })
        .collect();
    assert_eq!(states.len(), 65);
    states
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
    let slice = iteration(&source);
    println!(
        "ACTUAL source_steps={} source_regs={} header={} follow={} region_steps={} region_regs={} caps={:?}",
        source.instructions().len(),
        source.register_count(),
        slice.source_entry(),
        slice
            .continuations()
            .iter()
            .copied()
            .find(|&pc| pc != slice.source_entry())
            .unwrap(),
        slice.program().instructions().len(),
        slice.program().register_count(),
        slice.input_bit_caps()
    );
    std::fs::write(
        directory.join("region.ir"),
        format!("{:#?}", slice.program().instructions()),
    )
    .unwrap();
    let mut comparisons = 0;
    for (input, memory) in fixture_states(source.register_count()) {
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

#[test]
#[ignore = "requires the development fixture object and Z3; compares selected sparse display IR at every prefix"]
fn actual_selected_display_register_projection_and_region_queries() {
    use nirvana::block_verify::region::registers::compact;
    use nirvana::readable::{self, ReadableOptions, StorageProvenance};
    let directory = std::path::PathBuf::from(std::env::var("NIRVANA_REGION_OUTPUT").unwrap());
    std::fs::create_dir_all(&directory).unwrap();
    let bytes = std::fs::read(std::env::var("NIRVANA_REGION_OBJECT").unwrap()).unwrap();
    let raw = nirvana::frontend::lift_elf_auto(&bytes, "fixture")
        .unwrap()
        .program;
    let output = readable::emit_middle_c_with_storage_provenance(
        &nirvana::middle_ir::Function::from_low(&raw).unwrap(),
        ReadableOptions {
            stack_register: Some(Reg(nirvana::x86::RSP)),
            recover_objects: true,
            coalesce_locals: true,
            compact_memory: true,
        },
    )
    .unwrap();
    let StorageProvenance::Captured(snapshot) = output.storage_provenance else {
        panic!("missing selected storage input");
    };
    let source = &snapshot.source;
    let compact = compact(source).unwrap();
    assert!(compact.program().register_count() < source.register_count());
    let slice = iteration(compact.program());
    for (name, program) in [
        ("selected-source.ir", source.as_ref()),
        ("dense.ir", compact.program()),
    ] {
        std::fs::write(
            directory.join(name),
            format!(
                "entry={} registers={}\n{:#?}\n",
                program.cfg().block(program.cfg().entry()).start,
                program.register_count(),
                program.instructions()
            ),
        )
        .unwrap();
    }
    let mut prefixes = 0;
    let mut regions = 0;
    for (input, memory) in fixture_states(source.register_count()) {
        let dense = compact.project_input(&input).unwrap();
        let full = source.run_with_memory(&input, 4096, &memory, 4096).unwrap();
        assert!(matches!(full.status, RunStatus::Returned(_)));
        for budget in 0..=full.state.trace.len() + 1 {
            let expected = source
                .run_with_memory(&input, 4096, &memory, budget)
                .unwrap();
            let mut actual = compact
                .program()
                .run_with_memory(&dense, 4096, &memory, budget)
                .unwrap();
            if full.state.trace.get(budget) == Some(&slice.source_entry()) {
                for pointer in [4224, 4095, 4608, u64::MAX] {
                    let mut entry = actual.state.registers.clone();
                    entry[compact.dense_register(Reg(nirvana::x86::RDI)).unwrap().0] = pointer;
                    compare(
                        compact.program(),
                        &slice,
                        &entry,
                        4096,
                        &actual.state.memory,
                    );
                    regions += 1;
                }
                compare(
                    compact.program(),
                    &slice,
                    &actual.state.registers,
                    4096,
                    &[],
                );
                regions += 1;
            }
            actual.state.registers = compact
                .restore_registers(&input, &actual.state.registers)
                .unwrap();
            assert_eq!(actual, expected);
            prefixes += 1;
        }
        for pointer in [4095, 4608, u64::MAX] {
            let mut input = input.clone();
            input[nirvana::x86::RDI] = pointer;
            let expected = source.run_with_memory(&input, 4096, &memory, 4096).unwrap();
            let mut actual = compact
                .program()
                .run_with_memory(&compact.project_input(&input).unwrap(), 4096, &memory, 4096)
                .unwrap();
            actual.state.registers = compact
                .restore_registers(&input, &actual.state.registers)
                .unwrap();
            assert_eq!(actual, expected);
            prefixes += 1;
        }
    }
    let shared: Vec<_> = (0..compact.program().register_count()).map(Reg).collect();
    let outputs: Vec<_> = (0..slice.program().register_count()).map(Reg).collect();
    let query = query(slice.program(), slice.program(), &shared, &outputs).unwrap();
    std::fs::write(directory.join("selected-identity.smt2"), query.smt2()).unwrap();
    let solver = Solver::new(std::env::var("NIRVANA_Z3").unwrap())
        .with_timeout(std::time::Duration::from_secs(5));
    let now = std::time::Instant::now();
    assert_eq!(query.check(&solver), Verdict::EquivalentUnderModel);
    println!(
        "DISPLAY source_registers={} dense_registers={} region_registers={} prefix_comparisons={prefixes} region_comparisons={regions} identity_bytes={} ms={}",
        source.register_count(),
        compact.program().register_count(),
        slice.program().register_count(),
        query.smt2().len(),
        now.elapsed().as_millis()
    );
}

fn prepared_storage(bytes: &[u8]) -> (std::sync::Arc<Program>, Vec<Reg>) {
    use nirvana::readable::{self, ReadableOptions, SignedStorageProvenance};
    let raw = nirvana::frontend::lift_elf_auto(bytes, "fixture")
        .unwrap()
        .program;
    let output = readable::emit_middle_c_with_storage_provenance(
        &nirvana::middle_ir::Function::from_low(&raw).unwrap(),
        ReadableOptions {
            stack_register: Some(Reg(nirvana::x86::RSP)),
            recover_objects: true,
            coalesce_locals: true,
            compact_memory: true,
        },
    )
    .unwrap();
    let SignedStorageProvenance::Captured(snapshot) = output.signed_storage_provenance else {
        panic!("no prepared source");
    };
    (snapshot.source.clone(), output.parameters)
}

#[test]
#[ignore = "requires the Clang18 development fixture and Z3; validates real prepared storage lowering"]
fn actual_prepared_display_checked_storage_lowering() {
    use nirvana::block_verify::region::registers::compact;
    let directory = std::path::PathBuf::from(std::env::var("NIRVANA_REGION_OUTPUT").unwrap());
    std::fs::create_dir_all(&directory).unwrap();
    let bytes = std::fs::read(std::env::var("NIRVANA_REGION_OBJECT").unwrap()).unwrap();
    let (source, parameters) = prepared_storage(&bytes);
    let source = &source;
    let dense = compact(source).unwrap();
    let eligible: Vec<_> = dense
        .registers()
        .iter()
        .filter(|r| !parameters.contains(r))
        .copied()
        .collect();
    let allocation = nirvana::allocation::allocate_locals(source, &eligible).unwrap();
    let mapping: Vec<_> = eligible
        .iter()
        .map(|&r| (r, allocation.color(r).unwrap()))
        .collect();
    let lowered = nirvana::transform::allocated_storage::lower(source, &mapping).unwrap();
    lowered.validate().unwrap();
    let compacted = compact(lowered.program()).unwrap();
    let region = iteration(compacted.program());
    let mut comparisons = 0;
    for (input, memory) in fixture_states(source.register_count()) {
        let full = source.run_with_memory(&input, 4096, &memory, 4096).unwrap();
        assert!(matches!(full.status, RunStatus::Returned(_)));
        let mut extended = lowered.extend_input(&input, u64::MAX).unwrap();
        for (i, value) in extended.iter_mut().enumerate().skip(input.len()) {
            *value = (i as u64).wrapping_mul(0x9e3779b97f4a7c15);
        }
        let compact_input = compacted.project_input(&extended).unwrap();
        for budget in 0..=full.state.trace.len() + 1 {
            let expected = source
                .run_with_memory(&input, 4096, &memory, budget)
                .unwrap();
            let actual = compacted
                .program()
                .run_with_memory(&compact_input, 4096, &memory, budget)
                .unwrap();
            assert_eq!(actual.status, expected.status);
            assert_eq!(actual.state.memory, expected.state.memory);
            assert_eq!(actual.state.trace, expected.state.trace);
            assert_eq!(actual.state.instruction, expected.state.instruction);
            comparisons += 1;
            if full.state.trace.get(budget) == Some(&region.source_entry()) {
                compare(
                    compacted.program(),
                    &region,
                    &actual.state.registers,
                    4096,
                    &actual.state.memory,
                );
            }
        }
    }
    std::fs::write(
        directory.join("storage.ir"),
        format!(
            "entry={} registers={}\n{:#?}\n",
            compacted
                .program()
                .cfg()
                .block(compacted.program().cfg().entry())
                .start,
            compacted.program().register_count(),
            compacted.program().instructions()
        ),
    )
    .unwrap();
    let shared: Vec<_> = (0..compacted.program().register_count()).map(Reg).collect();
    let outputs: Vec<_> = (0..region.program().register_count()).map(Reg).collect();
    let query = query(region.program(), region.program(), &shared, &outputs).unwrap();
    std::fs::write(directory.join("storage-identity.smt2"), query.smt2()).unwrap();
    let solver = Solver::new(std::env::var("NIRVANA_Z3").unwrap())
        .with_timeout(std::time::Duration::from_secs(5));
    assert_eq!(query.check(&solver), Verdict::EquivalentUnderModel);
    println!(
        "STORAGE-IR source_registers={} mapped={} bank_registers={} dense_registers={} region_registers={} comparisons={comparisons} identity_bytes={}",
        source.register_count(),
        mapping.len(),
        lowered.program().register_count() - source.register_count(),
        compacted.program().register_count(),
        region.program().register_count(),
        query.smt2().len()
    );
}

#[path = "region_extraction/lanes.rs"]
mod lanes;

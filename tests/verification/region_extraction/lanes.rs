//! Actual object -> prepared display -> checked storage -> automatic lane groups.
use super::*;
use nirvana::block_verify::region::registers::compact;
use nirvana::lane_patterns::{PatternExpr, discover};

fn parameterized(expression: &PatternExpr) -> bool {
    match expression {
        PatternExpr::Lane => true,
        PatternExpr::Unary(_, value) => parameterized(value),
        PatternExpr::Binary(_, a, b) => parameterized(a) || parameterized(b),
        PatternExpr::Select(c, a, b) => parameterized(c) || parameterized(a) || parameterized(b),
        _ => false,
    }
}

fn checked_storage(bytes: &[u8]) -> (usize, Program, Vec<Reg>) {
    let (source, parameters) = prepared_storage(bytes);
    let dense = compact(&source).unwrap();
    let eligible: Vec<_> = dense
        .registers()
        .iter()
        .filter(|r| !parameters.contains(r))
        .copied()
        .collect();
    let allocation = nirvana::allocation::allocate_locals(&source, &eligible).unwrap();
    let colors: Vec<_> = eligible
        .iter()
        .map(|&reg| (reg, allocation.color(reg).unwrap()))
        .collect();
    let storage = nirvana::transform::allocated_storage::lower(&source, &colors).unwrap();
    storage.validate().unwrap();
    let compacted = compact(storage.program()).unwrap();
    let registers = compacted.registers().to_vec();
    (
        source.register_count(),
        compacted.program().clone(),
        registers,
    )
}

#[test]
#[ignore = "requires NIRVANA_REGION_OBJECT from the pinned Clang18 development fixture"]
fn actual_compiler_lane_discovery_has_varying_addresses_and_invariant_xor() {
    let directory = std::path::PathBuf::from(std::env::var("NIRVANA_REGION_OUTPUT").unwrap());
    std::fs::create_dir_all(&directory).unwrap();
    let bytes = std::fs::read(std::env::var("NIRVANA_REGION_OBJECT").unwrap()).unwrap();
    let (source_count, program, _registers) = checked_storage(&bytes);
    let program = &program;
    let found = discover(program).unwrap();
    assert!(found.belongs_to(program));
    assert_eq!(found.kernels().len(), 4);
    assert_eq!(found.groups().len(), 1, "{:#?}", found.kernels());
    let group = &found.groups()[0];
    assert_eq!(group.offsets, [1, 2, 3]);
    assert!(parameterized(&group.load_address));
    assert!(!parameterized(&group.update_expression));
    assert!(!parameterized(&group.store_address));
    let region = iteration(program);
    let interface = nirvana::block_verify::region::extraction::live_out::derive(&region).unwrap();
    assert!(interface.matches(&region));
    std::fs::write(
        directory.join("lanes.ir.txt"),
        format!(
            "entry={} registers={}\n{:#?}\n",
            program.cfg().block(program.cfg().entry()).start,
            program.register_count(),
            program.instructions()
        ),
    )
    .unwrap();
    std::fs::write(
        directory.join("lane-patterns.txt"),
        format!("{:#?}\n", found.groups()),
    )
    .unwrap();
    std::fs::write(
        directory.join("lane-interfaces.txt"),
        format!("{:#?}\n", interface.returns()),
    )
    .unwrap();
    println!(
        "LANE-DISCOVERY source_registers={} physical_registers={} kernels={} groups={} lanes={} offsets={:?} invariant_update=true varying_address=true source_bound=true interfaces={}",
        source_count,
        program.register_count(),
        found.kernels().len(),
        found.groups().len(),
        group.kernels.len(),
        group.offsets,
        interface.returns().len()
    );
}

#[allow(dead_code)]
#[path = "../../support/checked_c.rs"]
mod checked_c;
#[allow(dead_code)]
#[path = "../../support/native.rs"]
mod native;

#[test]
#[ignore = "requires NIRVANA_REGION_OBJECT, NIRVANA_REGION_OUTPUT and NIRVANA_Z3"]
fn actual_compiler_loop_proposal_records_gate_and_concrete_memory_behavior() {
    use nirvana::transform::rolled_loop::{self, Outcome as RollOutcome};
    let directory = std::path::PathBuf::from(std::env::var("NIRVANA_REGION_OUTPUT").unwrap());
    std::fs::create_dir_all(&directory).unwrap();
    let bytes = std::fs::read(std::env::var("NIRVANA_REGION_OBJECT").unwrap()).unwrap();
    let machine = nirvana::frontend::lift_elf_auto(&bytes, "fixture")
        .unwrap()
        .program;
    let (_, source, registers) = checked_storage(&bytes);
    let found = discover(&source).unwrap();
    let proposal = rolled_loop::propose(&source, &found, 0).unwrap();
    std::fs::write(
        directory.join("automatic-source.ir.txt"),
        format!(
            "entry={} registers={}\n{:#?}\n",
            source.cfg().block(source.cfg().entry()).start,
            source.register_count(),
            source.instructions()
        ),
    )
    .unwrap();

    let solver = Solver::new(std::env::var("NIRVANA_Z3").unwrap())
        .with_timeout(std::time::Duration::from_secs(15));
    let problem = proposal.verification_problem().unwrap();
    std::fs::write(
        directory.join("automatic.ir.txt"),
        format!("{:#?}\n", proposal.program().instructions()),
    )
    .unwrap();
    std::fs::write(
        directory.join("automatic-compare.smt2"),
        problem.query().smt2(),
    )
    .unwrap();
    std::fs::write(
        directory.join("automatic-complete.smt2"),
        problem.completion_query().smt2(),
    )
    .unwrap();
    if let Some(cases) = problem.input_partitions().unwrap() {
        for (n, script) in cases.smt2().enumerate() {
            std::fs::write(directory.join(format!("automatic-part-{n}.smt2")), script).unwrap();
        }
    }
    let start = std::time::Instant::now();
    let accepted = match problem.check(&solver) {
        RollOutcome::Verified(value) => {
            println!(
                "AUTOMATIC-GATE equivalent partitions={}",
                value.checked_partitions()
            );
            Some(value)
        }
        RollOutcome::Unknown(reason) => {
            println!("AUTOMATIC-GATE unknown reason={reason:?}");
            None
        }
        other => panic!("candidate failed its semantic gate: {other:?}"),
    };
    println!(
        "AUTOMATIC-ROLL adopted={} envelope={:?} selectors={:?} instructions={} proof_ms={}",
        accepted.is_some(),
        proposal.envelope(),
        proposal.selectors(),
        proposal.program().instructions().len(),
        start.elapsed().as_millis()
    );
    if std::env::var_os("NIRVANA_REQUIRE_ROLL_PROOF").is_some() {
        assert!(
            accepted.is_some(),
            "strict acceptance gate requires a completed universal proof"
        );
    }
    // This diagnostic also checks unproved proposals concretely. The status
    // above remains Unknown, and the normal emitter keeps its original source.
    let candidate = accepted
        .as_ref()
        .map_or(proposal.program(), |value| value.program());
    let stack = registers
        .iter()
        .position(|&reg| reg == Reg(4))
        .map(Reg)
        .unwrap();
    let mut emitted = nirvana::readable::emit_readable_c_with_options(
        candidate,
        nirvana::readable::ReadableOptions {
            stack_register: Some(stack),
            recover_objects: true,
            coalesce_locals: true,
            compact_memory: true,
        },
    )
    .unwrap();
    std::fs::write(directory.join("automatic.c"), &emitted.code).unwrap();
    for reg in &mut emitted.parameters {
        *reg = registers[reg.0];
        assert!(reg.0 < machine.register_count());
    }
    let harness = checked_c::source_with_stack(&emitted, machine.register_count(), 4, 512, 4600);
    let path = directory.join("automatic-harness.c");
    std::fs::write(&path, harness).unwrap();
    let vectors = std::fs::read_to_string("tools/corpora/structure-nested-v1.inputs.txt").unwrap();
    let mut rows = Vec::new();
    let mut expected = Vec::new();
    for line in vectors.lines().filter(|line| !line.trim().is_empty()) {
        let words: Vec<u64> = line
            .split_whitespace()
            .map(|word| word.parse().unwrap())
            .collect();
        for address in [4224u64, 4576, 4095, 4608, u64::MAX] {
            let mut memory: Vec<u8> = (0..512usize).map(|i| (i * 29 + 7) as u8).collect();
            for (n, value) in words.iter().enumerate() {
                if let Some(location) = address
                    .checked_add(n as u64 * 8)
                    .and_then(|v| v.checked_sub(4096))
                    .filter(|&v| v <= 504)
                {
                    memory[location as usize..location as usize + 8]
                        .copy_from_slice(&value.to_le_bytes());
                }
            }
            let mut input = vec![0; machine.register_count()];
            input[4] = 4600;
            input[7] = address;
            let left = machine
                .run_with_memory(&input, 4096, &memory, 8192)
                .unwrap();
            let mut compact_input: Vec<_> = registers
                .iter()
                .map(|reg| input.get(reg.0).copied().unwrap_or(u64::MAX))
                .collect();
            compact_input.push(0);
            let right = candidate
                .run_with_memory(&compact_input, 4096, &memory, 8192)
                .unwrap();
            assert_eq!(left.status, right.status);
            assert_eq!(left.state.memory, right.state.memory);
            let mut values = match left.status {
                RunStatus::Returned(value) => vec![0, 0, 0, 0, value],
                RunStatus::Fault(f) => vec![
                    1,
                    f.address,
                    match f.access {
                        nirvana::ir::AccessKind::Read => 1,
                        nirvana::ir::AccessKind::Write => 2,
                    },
                    f.width.bytes() as u64,
                    0,
                ],
                RunStatus::Suspended => panic!("machine suspended"),
            };
            values.extend(
                left.state
                    .memory
                    .chunks_exact(8)
                    .map(|b| u64::from_le_bytes(b.try_into().unwrap())),
            );
            expected.push(values);
            rows.push(format!(
                "{address} {} {} {} {}",
                words[0], words[1], words[2], words[3]
            ));
        }
    }
    for optimization in ["-O0", "-O2"] {
        let binary = directory.join(format!("automatic{optimization}"));
        native::compile_c(
            &path,
            &binary,
            &[
                optimization,
                "-fsanitize=undefined",
                "-fno-sanitize-recover=all",
            ],
        );
        assert_eq!(
            native::run_fields(&binary, &(rows.join("\n") + "\n"), 69),
            expected
        );
        println!(
            "AUTOMATIC-C opt={optimization} cases={} all_ram=true faults=true ubsan=true",
            rows.len()
        );
    }
}

#[test]
#[ignore = "requires NIRVANA_REGION_OBJECT, NIRVANA_REGION_OUTPUT and NIRVANA_Z3"]
fn actual_compiler_loop_composition_checks_source_derived_lane_relations() {
    use nirvana::block_verify::region::composition;
    use nirvana::transform::rolled_loop;
    let directory = std::path::PathBuf::from(std::env::var("NIRVANA_REGION_OUTPUT").unwrap());
    std::fs::create_dir_all(&directory).unwrap();
    let bytes = std::fs::read(std::env::var("NIRVANA_REGION_OBJECT").unwrap()).unwrap();
    let (_, source, _) = checked_storage(&bytes);
    let discovery = discover(&source).unwrap();
    let proposal = rolled_loop::propose(&source, &discovery, 0).unwrap();
    let problem = proposal.verification_problem().unwrap();
    let local = problem.composition_problem().unwrap();
    assert_eq!(local.cuts().len(), proposal.rounds() + 1);
    std::fs::write(
        directory.join("composition-cuts.txt"),
        format!("{:#?}\n", local.cuts()),
    )
    .unwrap();
    for (n, obligation) in local.obligations().iter().enumerate() {
        std::fs::write(
            directory.join(format!("composition-{n}.smt2")),
            obligation.query().smt2(),
        )
        .unwrap();
        println!(
            "COMPOSITION-OBLIGATION index={n} cut={} kind={:?} bytes={}",
            obligation.cut(),
            obligation.kind(),
            obligation.query().smt2().len()
        );
    }
    let solver = Solver::new(std::env::var("NIRVANA_Z3").unwrap())
        .with_timeout(std::time::Duration::from_secs(15));
    let start = std::time::Instant::now();
    match local.check(&solver, std::time::Duration::from_secs(15)) {
        composition::Outcome::Verified(seal) => {
            assert!(seal.matches(problem.query()));
            println!(
                "COMPOSITION-GATE equivalent obligations={} ms={}",
                seal.checked(),
                start.elapsed().as_millis()
            );
        }
        composition::Outcome::Unproved(failure) => {
            let status = match &failure.verdict {
                Verdict::Counterexample(witness) => format!(
                    "local_counterexample before={:?} after={:?} ram_equal={} registers={:?}",
                    witness.before.status,
                    witness.after.status,
                    witness.before.state.memory == witness.after.state.memory,
                    witness
                        .before
                        .state
                        .registers
                        .iter()
                        .zip(&witness.after.state.registers)
                        .enumerate()
                        .filter_map(|(n, (a, b))| (a != b).then_some((n, a, b)))
                        .collect::<Vec<_>>()
                ),
                other => format!("{other:?}"),
            };
            panic!(
                "local obligation {} cut={} kind={:?} status={status}",
                failure.checked, failure.cut, failure.kind
            );
        }
    }
    assert_eq!(
        problem.completion_query().check(&solver),
        Verdict::EquivalentUnderModel
    );
}

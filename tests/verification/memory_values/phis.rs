use super::*;

fn family_paths(family: usize) -> Vec<Vec<u64>> {
    match family {
        0 => vec![vec![0, 1, 3], vec![0, 2, 3]],
        1 => [1, 2]
            .into_iter()
            .flat_map(|a| [4, 5].into_iter().map(move |b| vec![0, a, 3, b, 6]))
            .collect(),
        _ => (0..=3)
            .map(|visits| {
                let mut rows = vec![0, 1];
                for _ in 0..visits {
                    rows.extend([3, 1]);
                }
                rows.push(2);
                rows
            })
            .collect(),
    }
}

fn path(source: &nirvana::ir::Program, addresses: &[u64]) -> nirvana::ir::Program {
    let rows = addresses
        .iter()
        .enumerate()
        .map(|(index, address)| {
            let mut row = source
                .instructions()
                .iter()
                .find(|i| i.address == *address)
                .unwrap()
                .clone();
            row.address = index as u64;
            row.size = 1;
            if !matches!(row.control, nirvana::ir::Control::Return(_)) {
                row.control = nirvana::ir::Control::Next;
            }
            row
        })
        .collect();
    nirvana::ir::Program::new(0, source.register_count(), rows).unwrap()
}

#[test]
#[ignore = "requires Z3; set NIRVANA_Z3"]
fn actual_register_phi_paths_have_checked_memory_proofs_and_a_replayed_unequal_arm() {
    use nirvana::block_verify::{self, BlockVerdict};
    use nirvana::ir::{Program, Reg};
    let solver = Solver::new(std::env::var("NIRVANA_Z3").unwrap_or_else(|_| "z3".into()));
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("target/verification/register-phi-values");
    std::fs::create_dir_all(&root).unwrap();
    let prefix: Vec<_> = (0..8).map(Reg).collect();
    let mut proved = 0;
    for (family, source) in crate::support::byte_values::register_phi_programs()
        .into_iter()
        .enumerate()
    {
        let plan = nirvana::memory_values::MemoryValuePlan::analyze(&source).unwrap();
        let candidate = plan.lower(&source).unwrap();
        let paths = family_paths(family);
        for (index, addresses) in paths.iter().enumerate() {
            let query = block_verify::block_query(
                &path(&source, addresses),
                &path(&candidate, addresses),
                0,
                &prefix,
                &prefix,
            )
            .unwrap();
            let name = format!("family-{family}-path-{index}");
            std::fs::write(
                root.join(format!("{name}.smt2")),
                format!("{}(check-sat)\n", query.smt2()),
            )
            .unwrap();
            let verdict = query.check(&solver);
            std::fs::write(root.join(format!("{name}.out")), format!("{verdict:?}\n")).unwrap();
            assert_eq!(verdict, BlockVerdict::EquivalentUnderModel, "{name}");
            proved += 1;
        }
        if family == 0 {
            let mut rows = source.instructions().to_vec();
            rows[2].assignments[0].value = Expr::load(b(B::Add, r(7), c(34)), Width::U16);
            let unequal = Program::new(0, 8, rows).unwrap();
            let mut rows = candidate.instructions().to_vec();
            rows[2].assignments[0] = unequal.instructions()[2].assignments[0].clone();
            let wrong = Program::new(0, candidate.register_count(), rows).unwrap();
            assert!(nirvana::memory_values::validate(&unequal, &plan, &wrong).is_err());
            let query = block_verify::block_query(
                &path(&unequal, &[0, 2, 3]),
                &path(&wrong, &[0, 2, 3]),
                0,
                &prefix,
                &prefix,
            )
            .unwrap();
            std::fs::write(
                root.join("unequal-arm.smt2"),
                format!("{}(check-sat)\n", query.smt2()),
            )
            .unwrap();
            let verdict = query.check(&solver);
            std::fs::write(root.join("unequal-arm.out"), format!("{verdict:?}\n")).unwrap();
            assert!(
                matches!(verdict, BlockVerdict::Counterexample(_)),
                "{verdict:?}"
            );
        }
    }
    assert_eq!(proved, 10);
    println!(
        "{proved} universal register-phi path/RAM/first-fault checks; 1 replayed unequal-arm SAT control"
    );
}

#[test]
#[ignore = "requires Z3; set NIRVANA_Z3"]
fn composed_phi_memory_plans_preserve_checked_paths_and_replay_a_bad_last_stage() {
    use nirvana::block_verify::{self, BlockVerdict};
    use nirvana::ir::{Control, Program, Reg};
    let solver = Solver::new(std::env::var("NIRVANA_Z3").unwrap_or_else(|_| "z3".into()));
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("target/verification/composed-memory-values");
    std::fs::create_dir_all(&root).unwrap();
    let prefix: Vec<_> = (0..8).map(Reg).collect();
    let mut proved = 0;
    for (family, source) in crate::support::byte_values::resaved_phi_programs()
        .into_iter()
        .enumerate()
    {
        let mut candidate = source.clone();
        for _ in 0..3 {
            let Some(plan) = nirvana::memory_values::MemoryValuePlan::analyze(&candidate) else {
                break;
            };
            candidate = plan.lower(&candidate).unwrap();
        }
        let paths = family_paths(family);
        for (index, addresses) in paths.iter().enumerate() {
            let query = block_verify::block_query(
                &path(&source, addresses),
                &path(&candidate, addresses),
                0,
                &prefix,
                &prefix,
            )
            .unwrap();
            let name = format!("family-{family}-path-{index}");
            std::fs::write(
                root.join(format!("{name}.smt2")),
                format!("{}(check-sat)\n", query.smt2()),
            )
            .unwrap();
            let verdict = query.check(&solver);
            std::fs::write(root.join(format!("{name}.out")), format!("{verdict:?}\n")).unwrap();
            assert_eq!(verdict, BlockVerdict::EquivalentUnderModel, "{name}");
            proved += 1;
        }
        if family == 0 {
            let mut rows = candidate.instructions().to_vec();
            let Control::Return(value) = &mut rows[3].control else {
                unreachable!()
            };
            *value = b(B::Xor, value.clone(), c(1));
            let bad = Program::new(0, candidate.register_count(), rows).unwrap();
            let query = block_verify::block_query(
                &path(&source, &[0, 1, 3]),
                &path(&bad, &[0, 1, 3]),
                0,
                &prefix,
                &prefix,
            )
            .unwrap();
            std::fs::write(
                root.join("bad-last-stage.smt2"),
                format!("{}(check-sat)\n", query.smt2()),
            )
            .unwrap();
            let verdict = query.check(&solver);
            std::fs::write(root.join("bad-last-stage.out"), format!("{verdict:?}\n")).unwrap();
            assert!(
                matches!(verdict, BlockVerdict::Counterexample(_)),
                "{verdict:?}"
            );
        }
    }
    assert_eq!(proved, 10);
    println!(
        "{proved} universal composed phi/memory path checks; 1 replayed last-stage SAT control"
    );
}

#[test]
#[ignore = "requires Z3; set NIRVANA_Z3"]
fn source_memory_recovery_then_reduction_keeps_return_ram_and_first_faults() {
    use nirvana::block_verify::{self, BlockVerdict};
    use nirvana::ir::{Control, Program, Reg};
    let solver = Solver::new(std::env::var("NIRVANA_Z3").unwrap_or_else(|_| "z3".into()));
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("target/verification/source-memory-reduction");
    std::fs::create_dir_all(&root).unwrap();
    let inputs: Vec<_> = (0..8).map(Reg).collect();
    let mut proved = 0;
    for (family, source) in crate::support::byte_values::resaved_phi_programs()
        .into_iter()
        .enumerate()
    {
        let plan = nirvana::memory_values::MemoryValuePlan::analyze(&source).unwrap();
        let captured = plan.lower(&source).unwrap();
        let reduced = nirvana::reduce::reduce(&captured).unwrap();
        assert!(
            reduced
                .parameters()
                .iter()
                .all(|r| r.0 < source.register_count())
        );
        let candidate = reduced.program();
        for (index, addresses) in family_paths(family).iter().enumerate() {
            let query = block_verify::block_query(
                &path(&source, addresses),
                &path(candidate, addresses),
                0,
                &inputs,
                &[],
            )
            .unwrap();
            let name = format!("family-{family}-path-{index}");
            std::fs::write(
                root.join(format!("{name}.smt2")),
                format!("{}(check-sat)\n", query.smt2()),
            )
            .unwrap();
            let verdict = query.check(&solver);
            std::fs::write(root.join(format!("{name}.out")), format!("{verdict:?}\n")).unwrap();
            assert_eq!(verdict, BlockVerdict::EquivalentUnderModel, "{name}");
            proved += 1;
        }
        if family == 0 {
            let mut rows = candidate.instructions().to_vec();
            let Control::Return(value) = &mut rows[3].control else {
                unreachable!()
            };
            *value = b(B::Xor, value.clone(), c(1));
            let bad = Program::new(0, candidate.register_count(), rows).unwrap();
            let query = block_verify::block_query(
                &path(&source, &[0, 1, 3]),
                &path(&bad, &[0, 1, 3]),
                0,
                &inputs,
                &[],
            )
            .unwrap();
            std::fs::write(
                root.join("bad-reduced-return.smt2"),
                format!("{}(check-sat)\n", query.smt2()),
            )
            .unwrap();
            let verdict = query.check(&solver);
            std::fs::write(
                root.join("bad-reduced-return.out"),
                format!("{verdict:?}\n"),
            )
            .unwrap();
            assert!(
                matches!(verdict, BlockVerdict::Counterexample(_)),
                "{verdict:?}"
            );
        }
    }
    assert_eq!(proved, 10);
    println!(
        "{proved} universal source-memory/reduction return/RAM/first-fault path checks; 1 replayed bad-return SAT control"
    );
}

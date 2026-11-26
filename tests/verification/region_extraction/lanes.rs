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

#[test]
#[ignore = "requires NIRVANA_REGION_OBJECT from the pinned Clang18 development fixture"]
fn actual_compiler_lane_discovery_has_varying_addresses_and_invariant_xor() {
    let directory = std::path::PathBuf::from(std::env::var("NIRVANA_REGION_OUTPUT").unwrap());
    std::fs::create_dir_all(&directory).unwrap();
    let bytes = std::fs::read(std::env::var("NIRVANA_REGION_OBJECT").unwrap()).unwrap();
    let (source, parameters) = prepared_storage(&bytes);
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
    let program = compacted.program();
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
        source.register_count(),
        program.register_count(),
        found.kernels().len(),
        found.groups().len(),
        group.kernels.len(),
        group.offsets,
        interface.returns().len()
    );
}

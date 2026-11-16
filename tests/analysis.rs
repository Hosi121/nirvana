use std::collections::BTreeSet;

use nirvana::analysis::ControlFlowAnalysis;
use nirvana::cfg::{BlockId, Cfg, Flow, Instruction};

fn cfg(entry: u64, flows: &[Flow]) -> Cfg {
    Cfg::build(
        entry,
        flows
            .iter()
            .enumerate()
            .map(|(address, &flow)| Instruction::new(address as u64, 1, flow))
            .collect(),
    )
    .unwrap()
}

fn blocks(cfg: &Cfg, addresses: &[u64]) -> BTreeSet<BlockId> {
    addresses
        .iter()
        .map(|&address| cfg.block_at(address).unwrap())
        .collect()
}

#[test]
fn diamond_has_the_entry_as_the_join_immediate_dominator() {
    let cfg = cfg(
        0,
        &[Flow::Branch(2), Flow::Jump(3), Flow::Next, Flow::Return],
    );
    let analysis = ControlFlowAnalysis::compute(&cfg).unwrap();
    let join = cfg.block_at(3).unwrap();
    assert_eq!(analysis.dominators(join), Some(&blocks(&cfg, &[0, 3])));
    assert_eq!(analysis.immediate_dominator(join), Some(cfg.entry()));
    assert_eq!(analysis.immediate_dominator(cfg.entry()), None);
    assert!(analysis.natural_loops().is_empty());
    assert!(analysis.is_reducible());
}

#[test]
fn finds_a_natural_loop_without_including_its_preheader_or_exit() {
    let cfg = cfg(
        0,
        &[
            Flow::Next,
            Flow::Branch(4),
            Flow::Next,
            Flow::Jump(1),
            Flow::Return,
        ],
    );
    let analysis = ControlFlowAnalysis::compute(&cfg).unwrap();
    assert_eq!(analysis.natural_loops().len(), 1);
    let natural_loop = &analysis.natural_loops()[0];
    assert_eq!(natural_loop.header, cfg.block_at(1).unwrap());
    assert_eq!(natural_loop.latches, blocks(&cfg, &[2]));
    assert_eq!(natural_loop.body, blocks(&cfg, &[1, 2]));
    assert!(analysis.is_reducible());
}

#[test]
fn self_loop_does_not_pull_in_predecessors_of_its_header() {
    let cfg = cfg(0, &[Flow::Jump(1), Flow::Branch(1), Flow::Return]);
    let analysis = ControlFlowAnalysis::compute(&cfg).unwrap();
    assert_eq!(analysis.natural_loops()[0].body, blocks(&cfg, &[1]));
    assert!(analysis.is_reducible());
}

#[test]
fn entry_can_have_a_back_edge() {
    let cfg = cfg(0, &[Flow::Jump(0)]);
    let analysis = ControlFlowAnalysis::compute(&cfg).unwrap();
    assert_eq!(analysis.natural_loops()[0].body, blocks(&cfg, &[0]));
    assert_eq!(analysis.dominators(cfg.entry()), Some(&blocks(&cfg, &[0])));
    assert!(analysis.is_reducible());
}

#[test]
fn merges_multiple_latches_for_one_header() {
    let cfg = cfg(
        0,
        &[
            Flow::Branch(5),
            Flow::Branch(3),
            Flow::Jump(0),
            Flow::Jump(0),
            Flow::Return,
            Flow::Return,
        ],
    );
    let analysis = ControlFlowAnalysis::compute(&cfg).unwrap();
    assert_eq!(analysis.natural_loops().len(), 1);
    let natural_loop = &analysis.natural_loops()[0];
    assert_eq!(natural_loop.latches, blocks(&cfg, &[2, 3]));
    assert_eq!(natural_loop.body, blocks(&cfg, &[0, 1, 2, 3]));
}

#[test]
fn finds_nested_loops() {
    let cfg = cfg(
        0,
        &[
            Flow::Jump(1),
            Flow::Branch(7),
            Flow::Branch(5),
            Flow::Next,
            Flow::Jump(2),
            Flow::Next,
            Flow::Jump(1),
            Flow::Return,
        ],
    );
    let analysis = ControlFlowAnalysis::compute(&cfg).unwrap();
    assert_eq!(analysis.natural_loops().len(), 2);
    let outer = &analysis.natural_loops()[0];
    let inner = &analysis.natural_loops()[1];
    assert_eq!(outer.header, cfg.block_at(1).unwrap());
    assert_eq!(outer.body, blocks(&cfg, &[1, 2, 3, 5]));
    assert_eq!(inner.header, cfg.block_at(2).unwrap());
    assert_eq!(inner.body, blocks(&cfg, &[2, 3]));
    assert!(inner.body.is_subset(&outer.body));
    assert!(analysis.is_reducible());
}

#[test]
fn unreachable_predecessor_does_not_change_dominance() {
    let cfg = cfg(0, &[Flow::Jump(2), Flow::Jump(2), Flow::Return]);
    let analysis = ControlFlowAnalysis::compute(&cfg).unwrap();
    let join = cfg.block_at(2).unwrap();
    assert_eq!(cfg.block(join).predecessors.len(), 2);
    assert_eq!(analysis.dominators(join), Some(&blocks(&cfg, &[0, 2])));
    assert_eq!(analysis.dominators(cfg.block_at(1).unwrap()), None);
}

#[test]
fn unreachable_cycles_do_not_change_reducibility() {
    let cfg = cfg(0, &[Flow::Return, Flow::Jump(2), Flow::Jump(1)]);
    let analysis = ControlFlowAnalysis::compute(&cfg).unwrap();
    assert!(analysis.natural_loops().is_empty());
    assert!(analysis.is_reducible());
}

#[test]
fn cycle_with_two_entries_is_irreducible() {
    let cfg = cfg(
        0,
        &[
            Flow::Branch(2),
            Flow::Jump(2),
            Flow::Branch(1),
            Flow::Return,
        ],
    );
    let analysis = ControlFlowAnalysis::compute(&cfg).unwrap();
    assert!(!analysis.is_reducible());
    // An empty natural-loop list is not a claim that this graph is acyclic.
    assert!(analysis.natural_loops().is_empty());
}

#[test]
fn detects_an_irreducible_cycle_inside_a_single_entry_outer_loop() {
    let cfg = cfg(
        0,
        &[
            Flow::Jump(1),
            Flow::Branch(3),
            Flow::Jump(3),
            Flow::Branch(2),
            Flow::Branch(1),
            Flow::Return,
        ],
    );
    let analysis = ControlFlowAnalysis::compute(&cfg).unwrap();
    assert!(!analysis.is_reducible());
    assert_eq!(analysis.natural_loops().len(), 1);
    assert_eq!(analysis.natural_loops()[0].header, cfg.block_at(1).unwrap());
}

#[test]
fn reachable_unknown_or_outside_edges_prevent_analysis() {
    for flows in [
        vec![Flow::IndirectJump],
        vec![Flow::Jump(99)],
        vec![Flow::Next],
        vec![Flow::Branch(0)],
    ] {
        let cfg = cfg(0, &flows);
        let error = ControlFlowAnalysis::compute(&cfg).unwrap_err();
        assert_eq!(error.block, cfg.entry());
    }
}

#[test]
fn unreachable_unknown_edge_does_not_prevent_entry_relative_analysis() {
    let cfg = cfg(0, &[Flow::Return, Flow::IndirectJump]);
    let analysis = ControlFlowAnalysis::compute(&cfg).unwrap();
    assert_eq!(analysis.reachable().len(), 1);
    assert!(analysis.is_reducible());
}

#[test]
fn unreachable_pre_entry_code_is_excluded_from_dominance() {
    let cfg = cfg(1, &[Flow::Next, Flow::Return]);
    let analysis = ControlFlowAnalysis::compute(&cfg).unwrap();
    assert_eq!(analysis.dominators(cfg.entry()), Some(&blocks(&cfg, &[1])));
    assert_eq!(analysis.dominators(cfg.block_at(0).unwrap()), None);
}

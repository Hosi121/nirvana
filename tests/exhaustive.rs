//! Cross-check small programs against independent graph definitions.

use std::collections::{BTreeMap, BTreeSet};

use nirvana::analysis::ControlFlowAnalysis;
use nirvana::cfg::{BlockId, Cfg, EdgeKind, Flow, Instruction, Target};
use nirvana::postdom::{PostDomError, PostDomNode, PostDominators};

fn reaches_exit_without(cfg: &Cfg, start: BlockId, removed: Option<BlockId>) -> bool {
    let mut seen = BTreeSet::new();
    let mut pending = vec![start];
    while let Some(id) = pending.pop() {
        if Some(id) == removed || !seen.insert(id) {
            continue;
        }
        if cfg.block(id).successors.is_empty() {
            return true;
        }
        for edge in &cfg.block(id).successors {
            if let Target::Block(target) = edge.target {
                pending.push(target);
            }
        }
    }
    false
}

fn assert_postdominance_matches_removed_vertex_paths(cfg: &Cfg) {
    let reachable = cfg.reachable_blocks();
    let no_exit: BTreeSet<_> = reachable
        .iter()
        .copied()
        .filter(|&id| !reaches_exit_without(cfg, id, None))
        .collect();
    match PostDominators::compute(cfg) {
        Err(PostDomError::NoExitPath(missing)) => assert_eq!(missing, no_exit),
        Err(error) => panic!("unexpected incomplete CFG: {error}"),
        Ok(postdom) => {
            assert!(no_exit.is_empty());
            for block in cfg.blocks() {
                if !reachable.contains(&block.id) {
                    assert_eq!(postdom.post_dominators(block.id), None);
                    continue;
                }
                assert!(postdom.post_dominates(PostDomNode::Exit, block.id));
                for candidate in cfg.blocks() {
                    assert_eq!(
                        postdom.post_dominates(PostDomNode::Block(candidate.id), block.id),
                        !reaches_exit_without(cfg, block.id, Some(candidate.id)),
                        "post-dominance mismatch: block={}, candidate={}",
                        block.id,
                        candidate.id
                    );
                }
                let immediate = postdom.immediate_post_dominator(block.id).unwrap();
                assert_ne!(immediate, PostDomNode::Block(block.id));
                for &strict in postdom.post_dominators(block.id).unwrap() {
                    if strict != PostDomNode::Block(block.id) {
                        match immediate {
                            PostDomNode::Block(id) => assert!(postdom.post_dominates(strict, id)),
                            PostDomNode::Exit => assert_eq!(strict, PostDomNode::Exit),
                        }
                    }
                }
            }
        }
    }
}

fn reachable_without(cfg: &Cfg, target: BlockId, removed: BlockId) -> bool {
    let mut seen = BTreeSet::new();
    let mut pending = vec![cfg.entry()];
    while let Some(id) = pending.pop() {
        if id == removed || !seen.insert(id) {
            continue;
        }
        if id == target {
            return true;
        }
        for edge in &cfg.block(id).successors {
            if let Target::Block(next) = edge.target {
                pending.push(next);
            }
        }
    }
    false
}

// Independent reducibility oracle: T1 removes self edges; T2 contracts a
// non-entry node with one distinct predecessor into that predecessor.
fn reducible_by_contraction(cfg: &Cfg) -> bool {
    let reachable = cfg.reachable_blocks();
    let mut graph: BTreeMap<BlockId, BTreeSet<BlockId>> = reachable
        .iter()
        .map(|&id| {
            let targets = cfg
                .block(id)
                .successors
                .iter()
                .filter_map(|edge| match edge.target {
                    Target::Block(target) => Some(target),
                    _ => None,
                })
                .collect();
            (id, targets)
        })
        .collect();
    loop {
        for (&id, successors) in &mut graph {
            successors.remove(&id);
        }
        let contraction = graph
            .keys()
            .copied()
            .filter(|&id| id != cfg.entry())
            .find_map(|id| {
                let predecessors: Vec<_> = graph
                    .iter()
                    .filter_map(|(&source, targets)| targets.contains(&id).then_some(source))
                    .collect();
                (predecessors.len() == 1).then(|| (id, predecessors[0]))
            });
        let Some((id, predecessor)) = contraction else {
            return graph.len() == 1;
        };
        let outgoing = graph.remove(&id).unwrap();
        let targets = graph.get_mut(&predecessor).unwrap();
        targets.remove(&id);
        targets.extend(outgoing);
    }
}

fn assert_instruction_transitions_preserved(cfg: &Cfg) {
    let mut covered = vec![false; cfg.instructions().len()];
    for block in cfg.blocks() {
        for i in block.instructions.clone() {
            assert!(!covered[i], "instruction belongs to two blocks");
            covered[i] = true;
            if i + 1 < block.instructions.end {
                assert_eq!(cfg.instructions()[i].flow, Flow::Next);
                assert_eq!(
                    cfg.instructions()[i].address + u64::from(cfg.instructions()[i].size),
                    cfg.instructions()[i + 1].address
                );
            }
        }
        let last = cfg.instructions()[block.instructions.end - 1];
        let expected = match last.flow {
            Flow::Next => vec![(EdgeKind::Fallthrough, last.address + u64::from(last.size))],
            Flow::Jump(target) => vec![(EdgeKind::Jump, target)],
            Flow::Branch(target) => vec![
                (EdgeKind::Taken, target),
                (EdgeKind::NotTaken, last.address + u64::from(last.size)),
            ],
            Flow::Return => vec![],
            _ => unreachable!("generator only uses closed, direct control flow"),
        };
        let actual: Vec<_> = block
            .successors
            .iter()
            .map(|edge| {
                let Target::Block(target) = edge.target else {
                    panic!("unexpected unresolved edge")
                };
                (edge.kind, cfg.block(target).start)
            })
            .collect();
        assert_eq!(actual, expected);
        for &pred in &block.predecessors {
            assert!(
                cfg.block(pred)
                    .successors
                    .iter()
                    .any(|edge| edge.target == Target::Block(block.id))
            );
        }
        for edge in &block.successors {
            let Target::Block(target) = edge.target else {
                unreachable!()
            };
            assert!(cfg.block(target).predecessors.contains(&block.id));
        }
    }
    assert!(covered.into_iter().all(|value| value));
}

#[test]
fn four_instruction_programs_match_transition_dominance_and_reducibility_oracles() {
    // Each of the first three instructions has ten choices; the last returns.
    // All four entry addresses are tested: 10^3 * 4 = 4,000 programs.
    let choices = [
        Flow::Next,
        Flow::Return,
        Flow::Jump(0),
        Flow::Jump(1),
        Flow::Jump(2),
        Flow::Jump(3),
        Flow::Branch(0),
        Flow::Branch(1),
        Flow::Branch(2),
        Flow::Branch(3),
    ];
    let mut checked = 0;
    for &first in &choices {
        for &second in &choices {
            for &third in &choices {
                for entry in 0..4 {
                    let flows = [first, second, third, Flow::Return];
                    let cfg = Cfg::build(
                        entry,
                        flows
                            .into_iter()
                            .enumerate()
                            .map(|(address, flow)| Instruction::new(address as u64, 1, flow))
                            .collect(),
                    )
                    .unwrap();
                    assert_instruction_transitions_preserved(&cfg);
                    assert_postdominance_matches_removed_vertex_paths(&cfg);
                    let analysis = ControlFlowAnalysis::compute(&cfg).unwrap();
                    for block in cfg.blocks() {
                        for candidate in cfg.blocks() {
                            let expected = analysis.reachable().contains(&block.id)
                                && !reachable_without(&cfg, block.id, candidate.id);
                            assert_eq!(
                                analysis.dominates(candidate.id, block.id),
                                expected,
                                "dominance mismatch: flows={flows:?}, entry={entry}, candidate={}, block={}",
                                candidate.id,
                                block.id
                            );
                        }
                        if let Some(idom) = analysis.immediate_dominator(block.id) {
                            assert_ne!(idom, block.id);
                            for &strict in analysis.dominators(block.id).unwrap() {
                                if strict != block.id {
                                    assert!(analysis.dominates(strict, idom));
                                }
                            }
                        } else {
                            assert!(
                                block.id == cfg.entry()
                                    || !analysis.reachable().contains(&block.id)
                            );
                        }
                    }
                    assert_eq!(
                        analysis.is_reducible(),
                        reducible_by_contraction(&cfg),
                        "reducibility mismatch: flows={flows:?}, entry={entry}"
                    );
                    checked += 1;
                }
            }
        }
    }
    assert_eq!(checked, 4_000);
}

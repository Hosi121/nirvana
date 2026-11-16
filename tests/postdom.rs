use nirvana::cfg::{Cfg, Flow, Instruction};
use nirvana::postdom::{PostDomError, PostDomNode, PostDominators};

fn cfg(flows: &[Flow]) -> Cfg {
    Cfg::build(
        0,
        flows
            .iter()
            .enumerate()
            .map(|(address, &flow)| Instruction::new(address as u64, 1, flow))
            .collect(),
    )
    .unwrap()
}

#[test]
fn finds_the_real_join_of_a_diamond() {
    let cfg = cfg(&[Flow::Branch(2), Flow::Jump(3), Flow::Next, Flow::Return]);
    let postdom = PostDominators::compute(&cfg).unwrap();
    let join = PostDomNode::Block(cfg.block_at(3).unwrap());
    assert_eq!(postdom.immediate_post_dominator(cfg.entry()), Some(join));
    assert!(!postdom.post_dominates(PostDomNode::Block(cfg.block_at(1).unwrap()), cfg.entry()));
    assert!(postdom.post_dominates(PostDomNode::Exit, cfg.entry()));
}

#[test]
fn distinct_returns_meet_at_the_virtual_exit() {
    let cfg = cfg(&[Flow::Branch(2), Flow::Return, Flow::Return]);
    let postdom = PostDominators::compute(&cfg).unwrap();
    assert_eq!(
        postdom.immediate_post_dominator(cfg.entry()),
        Some(PostDomNode::Exit)
    );
}

#[test]
fn loops_with_an_exit_use_finite_exit_paths_without_claiming_termination() {
    let cfg = cfg(&[Flow::Branch(0), Flow::Return]);
    let postdom = PostDominators::compute(&cfg).unwrap();
    assert_eq!(
        postdom.immediate_post_dominator(cfg.entry()),
        Some(PostDomNode::Block(cfg.block_at(1).unwrap()))
    );
}

#[test]
fn refuses_to_invent_an_exit_for_an_infinite_loop() {
    let cfg = cfg(&[Flow::Jump(0)]);
    assert!(
        matches!(PostDominators::compute(&cfg), Err(PostDomError::NoExitPath(blocks)) if blocks.contains(&cfg.entry()))
    );
}

#[test]
fn detects_a_non_exiting_arm_even_when_the_other_arm_returns() {
    let cfg = cfg(&[Flow::Branch(2), Flow::Return, Flow::Jump(2)]);
    let Err(PostDomError::NoExitPath(blocks)) = PostDominators::compute(&cfg) else {
        panic!("expected a non-exiting region")
    };
    assert_eq!(blocks.len(), 1);
    assert!(blocks.contains(&cfg.block_at(2).unwrap()));
}

#[test]
fn ignores_an_unreachable_infinite_loop() {
    let cfg = cfg(&[Flow::Return, Flow::Jump(1)]);
    let postdom = PostDominators::compute(&cfg).unwrap();
    assert_eq!(postdom.post_dominators(cfg.block_at(1).unwrap()), None);
}

#[test]
fn unresolved_edges_are_still_errors() {
    let cfg = cfg(&[Flow::IndirectJump]);
    assert!(matches!(
        PostDominators::compute(&cfg),
        Err(PostDomError::Unresolved(_))
    ));
}

#[test]
fn common_post_dominator_handles_real_joins_distinct_returns_and_empty_input() {
    let graph = cfg(&[Flow::Branch(2), Flow::Jump(3), Flow::Next, Flow::Return]);
    let postdom = PostDominators::compute(&graph).unwrap();
    let arms = [graph.block_at(1).unwrap(), graph.block_at(2).unwrap()];
    assert_eq!(
        postdom.nearest_common_post_dominator(&arms),
        Some(PostDomNode::Block(graph.block_at(3).unwrap()))
    );
    assert_eq!(
        postdom.nearest_common_post_dominator(&[arms[0]]),
        Some(PostDomNode::Block(arms[0]))
    );
    assert_eq!(postdom.nearest_common_post_dominator(&[]), None);
    let graph = cfg(&[Flow::Branch(2), Flow::Return, Flow::Return]);
    let postdom = PostDominators::compute(&graph).unwrap();
    assert_eq!(
        postdom.nearest_common_post_dominator(&[
            graph.block_at(1).unwrap(),
            graph.block_at(2).unwrap()
        ]),
        Some(PostDomNode::Exit)
    );
}

#[test]
fn common_post_dominator_does_not_include_unreachable_blocks() {
    let graph = cfg(&[Flow::Return, Flow::Return]);
    let postdom = PostDominators::compute(&graph).unwrap();
    assert_eq!(
        postdom.nearest_common_post_dominator(&[graph.entry(), graph.block_at(1).unwrap()]),
        None
    );
}

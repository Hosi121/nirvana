use nirvana::cfg::{BuildError, Cfg, Edge, EdgeKind, Flow, Instruction, Target};

fn instruction(address: u64, size: u32, flow: Flow) -> Instruction {
    Instruction::new(address, size, flow)
}

#[test]
fn straight_line_is_one_block() {
    let cfg = Cfg::build(
        0x1000,
        vec![
            instruction(0x1000, 3, Flow::Next),
            instruction(0x1003, 2, Flow::Next),
            instruction(0x1005, 1, Flow::Return),
        ],
    )
    .unwrap();
    assert_eq!(cfg.blocks().len(), 1);
    let block = cfg.block(cfg.entry());
    assert_eq!((block.start, block.end), (0x1000, 0x1006));
    assert_eq!(block.instructions, 0..3);
    assert!(block.successors.is_empty());
}

#[test]
fn branch_destinations_split_an_existing_instruction_run() {
    let cfg = Cfg::build(
        0,
        vec![
            instruction(0, 2, Flow::Next),
            instruction(2, 2, Flow::Next),
            instruction(4, 2, Flow::Branch(2)),
            instruction(6, 1, Flow::Return),
        ],
    )
    .unwrap();
    assert_eq!(
        cfg.blocks().iter().map(|b| b.start).collect::<Vec<_>>(),
        vec![0, 2, 6]
    );
    let branch = cfg.block(cfg.block_at(2).unwrap());
    assert_eq!(branch.instructions, 1..3);
    assert_eq!(
        branch.successors,
        vec![
            Edge {
                kind: EdgeKind::Taken,
                target: Target::Block(branch.id)
            },
            Edge {
                kind: EdgeKind::NotTaken,
                target: Target::Block(cfg.block_at(6).unwrap())
            },
        ]
    );
}

#[test]
fn same_target_branch_preserves_both_arms_but_deduplicates_predecessors() {
    let cfg = Cfg::build(
        0,
        vec![
            instruction(0, 1, Flow::Branch(1)),
            instruction(1, 1, Flow::Return),
        ],
    )
    .unwrap();
    let target = cfg.block_at(1).unwrap();
    assert_eq!(
        cfg.block(cfg.entry()).successors,
        vec![
            Edge {
                kind: EdgeKind::Taken,
                target: Target::Block(target)
            },
            Edge {
                kind: EdgeKind::NotTaken,
                target: Target::Block(target)
            },
        ]
    );
    assert_eq!(cfg.block(target).predecessors, vec![cfg.entry()]);
}

#[test]
fn jump_does_not_fall_through_and_preserves_dead_instructions() {
    let cfg = Cfg::build(
        0,
        vec![
            instruction(0, 1, Flow::Jump(2)),
            instruction(1, 1, Flow::Return),
            instruction(2, 1, Flow::Return),
        ],
    )
    .unwrap();
    assert_eq!(cfg.blocks().len(), 3);
    assert_eq!(cfg.block(cfg.entry()).successors.len(), 1);
    assert!(!cfg.reachable_blocks().contains(&cfg.block_at(1).unwrap()));
}

#[test]
fn return_and_stop_have_no_successors() {
    for flow in [Flow::Return, Flow::Stop] {
        let cfg = Cfg::build(
            0,
            vec![instruction(0, 1, flow), instruction(1, 1, Flow::Return)],
        )
        .unwrap();
        assert_eq!(cfg.blocks().len(), 2);
        assert!(cfg.block(cfg.entry()).successors.is_empty());
        assert_eq!(cfg.reachable_blocks().len(), 1);
    }
}

#[test]
fn layout_gap_does_not_create_a_fallthrough_to_the_next_supplied_instruction() {
    let cfg = Cfg::build(
        0,
        vec![
            instruction(0, 2, Flow::Next),
            instruction(10, 1, Flow::Return),
        ],
    )
    .unwrap();
    assert_eq!(cfg.blocks().len(), 2);
    assert_eq!(
        cfg.block(cfg.entry()).successors,
        vec![Edge {
            kind: EdgeKind::Fallthrough,
            target: Target::Outside(2)
        },]
    );
    assert_eq!(cfg.reachable_blocks().len(), 1);
}

#[test]
fn final_next_is_an_unresolved_fallthrough() {
    let cfg = Cfg::build(0, vec![instruction(0, 1, Flow::Next)]).unwrap();
    assert_eq!(
        cfg.block(cfg.entry()).successors[0].target,
        Target::Outside(1)
    );
}

#[test]
fn outside_jump_is_preserved() {
    let cfg = Cfg::build(0, vec![instruction(0, 1, Flow::Jump(0x1000))]).unwrap();
    assert_eq!(
        cfg.block(cfg.entry()).successors[0].target,
        Target::Outside(0x1000)
    );
}

#[test]
fn missing_branch_fallthrough_is_preserved() {
    let cfg = Cfg::build(0, vec![instruction(0, 1, Flow::Branch(0))]).unwrap();
    assert_eq!(
        cfg.block(cfg.entry()).successors[1],
        Edge {
            kind: EdgeKind::NotTaken,
            target: Target::Outside(1),
        }
    );
}

#[test]
fn indirect_jump_has_an_explicit_unknown_destination() {
    let cfg = Cfg::build(0, vec![instruction(0, 1, Flow::IndirectJump)]).unwrap();
    assert_eq!(
        cfg.block(cfg.entry()).successors,
        vec![Edge {
            kind: EdgeKind::Indirect,
            target: Target::Unknown
        },]
    );
}

#[test]
fn instruction_order_does_not_change_the_graph() {
    let input = vec![
        instruction(0, 1, Flow::Branch(2)),
        instruction(1, 1, Flow::Jump(3)),
        instruction(2, 1, Flow::Next),
        instruction(3, 1, Flow::Return),
    ];
    let cfg = Cfg::build(0, input.clone()).unwrap();
    let mut reversed = input;
    reversed.reverse();
    let other = Cfg::build(0, reversed).unwrap();
    assert_eq!(cfg.instructions(), other.instructions());
    assert_eq!(cfg.blocks(), other.blocks());
}

#[test]
fn entry_can_be_inside_the_supplied_instruction_list() {
    let cfg = Cfg::build(
        1,
        vec![
            instruction(0, 1, Flow::Next),
            instruction(1, 1, Flow::Return),
        ],
    )
    .unwrap();
    assert_eq!(cfg.block(cfg.entry()).start, 1);
    assert_eq!(cfg.blocks().len(), 2);
    assert_eq!(cfg.reachable_blocks().len(), 1);
}

#[test]
fn rejects_empty_input() {
    assert_eq!(Cfg::build(0, vec![]).unwrap_err(), BuildError::EmptyInput);
}

#[test]
fn rejects_zero_sized_instructions() {
    assert_eq!(
        Cfg::build(0, vec![instruction(0, 0, Flow::Return)]).unwrap_err(),
        BuildError::ZeroSize(0)
    );
}

#[test]
fn rejects_address_overflow() {
    assert_eq!(
        Cfg::build(u64::MAX, vec![instruction(u64::MAX, 1, Flow::Return)]).unwrap_err(),
        BuildError::AddressOverflow(u64::MAX)
    );
}

#[test]
fn rejects_duplicate_instruction_addresses() {
    assert_eq!(
        Cfg::build(
            0,
            vec![
                instruction(0, 1, Flow::Next),
                instruction(0, 1, Flow::Return)
            ]
        )
        .unwrap_err(),
        BuildError::DuplicateAddress(0)
    );
}

#[test]
fn rejects_overlapping_decodings() {
    assert_eq!(
        Cfg::build(
            0,
            vec![
                instruction(0, 3, Flow::Next),
                instruction(2, 1, Flow::Return)
            ]
        )
        .unwrap_err(),
        BuildError::OverlappingInstructions {
            first: 0,
            second: 2
        }
    );
}

#[test]
fn rejects_missing_or_interior_entry() {
    for entry in [1, 10] {
        assert_eq!(
            Cfg::build(entry, vec![instruction(0, 3, Flow::Return)]).unwrap_err(),
            BuildError::MissingEntry(entry)
        );
    }
}

#[test]
fn rejects_a_direct_branch_into_an_instruction() {
    for flow in [Flow::Jump(4), Flow::Branch(4)] {
        assert_eq!(
            Cfg::build(
                0,
                vec![instruction(0, 2, flow), instruction(2, 3, Flow::Return)]
            )
            .unwrap_err(),
            BuildError::TargetInsideInstruction {
                source: 0,
                target: 4,
                instruction: 2
            }
        );
    }
}

#[test]
fn dot_shows_unknown_targets_and_unreachable_blocks() {
    let cfg = Cfg::build(
        0,
        vec![
            instruction(0, 1, Flow::IndirectJump),
            instruction(1, 1, Flow::Return),
        ],
    )
    .unwrap();
    let dot = cfg.to_dot();
    assert!(dot.contains("label=\"unknown\""));
    assert!(dot.contains("style=dashed"));
    assert!(dot.contains("label=\"indirect\""));
    assert!(dot.contains("entry -> bb0"));
}

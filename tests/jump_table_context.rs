use nirvana::ir::Width;
use nirvana::jump_tables::{self, MAX_CONTEXT_INSTRUCTIONS, MAX_CONTEXT_PATHS, MAX_CONTEXT_WORK};
use nirvana::x86::{Addressing, Alu, DecodedInstruction, Operand, Operation, Register, Unary};

fn reg(index: u8) -> Register {
    Register {
        index,
        width: Width::U64,
        shift: 0,
    }
}
fn i(address: u64, operation: Operation) -> DecodedInstruction {
    DecodedInstruction {
        address,
        size: 1,
        operation,
    }
}
fn jump(base: Option<u8>, displacement: i64) -> Operation {
    Operation::IndirectJump(Operand::Memory {
        address: Addressing {
            base,
            index: Some(7),
            scale: 8,
            displacement,
            rip_relative: false,
        },
        width: Width::U64,
    })
}
fn memory() -> Vec<u8> {
    [0x1080u64, 0x1081, 0x1082, 0x1083]
        .into_iter()
        .flat_map(u64::to_le_bytes)
        .collect()
}
fn search(graph: &[DecodedInstruction], branch: u64) -> jump_tables::ContextSearch {
    jump_tables::discover_cfg(graph, branch, 0x2000, &memory(), 0x1000..0x1100)
}

#[test]
fn taken_bounds_and_noncontiguous_direct_edges_retain_the_actual_path() {
    for (condition, maximum) in [(6, 1), (2, 2)] {
        let graph = [
            i(
                0x1000,
                Operation::Alu {
                    kind: Alu::Cmp,
                    destination: Operand::Register(reg(7)),
                    source: Operand::Immediate(maximum),
                },
            ),
            i(
                0x1001,
                Operation::Branch {
                    condition,
                    target: 0x1020,
                },
            ),
            i(0x1002, Operation::Return { extra_pop: 0 }),
            i(0x1020, Operation::Jump(0x1040)),
            i(0x1040, jump(None, 0x2000)),
        ];
        let found = search(&graph, 0x1040);
        assert!(!found.reached_limit);
        assert_eq!(found.candidates.len(), 1);
        assert_eq!(found.candidates[0].entry_limit_hint, Some(2));
        assert_eq!(found.candidates[0].entries.len(), 2);
    }
}

#[test]
fn joins_keep_alternative_bases_separate_and_ignore_input_order() {
    let mut graph = vec![
        i(
            0x1000,
            Operation::Branch {
                condition: 5,
                target: 0x1020,
            },
        ),
        i(
            0x1001,
            Operation::Mov {
                destination: Operand::Register(reg(2)),
                source: Operand::Immediate(0x2000),
            },
        ),
        i(0x1002, Operation::Jump(0x1040)),
        i(
            0x1020,
            Operation::Mov {
                destination: Operand::Register(reg(2)),
                source: Operand::Immediate(0x2010),
            },
        ),
        i(0x1021, Operation::Jump(0x1040)),
        i(
            0x1040,
            Operation::Alu {
                kind: Alu::And,
                destination: Operand::Register(reg(7)),
                source: Operand::Immediate(1),
            },
        ),
        i(0x1041, jump(Some(2), 0)),
    ];
    let found = search(&graph, 0x1041);
    assert_eq!(
        found.candidates.iter().map(|t| t.table).collect::<Vec<_>>(),
        [0x2000, 0x2010]
    );
    assert!(found.candidates.iter().all(|t| t.entries.len() == 2));
    graph.reverse();
    assert_eq!(search(&graph, 0x1041), found);
    // An unmodeled definition must not retain either incoming base.
    graph.push(i(
        0x1041,
        Operation::Unary {
            kind: Unary::Inc,
            destination: Operand::Register(reg(2)),
        },
    ));
    graph[0].address = 0x1042;
    assert!(search(&graph, 0x1042).candidates.is_empty());
}

#[test]
fn cycles_keep_the_entry_context_and_report_the_unexplored_residual() {
    let graph = [
        i(
            0x1000,
            Operation::Mov {
                destination: Operand::Register(reg(2)),
                source: Operand::Immediate(0x2000),
            },
        ),
        i(0x1001, Operation::Jump(0x1010)),
        i(0x1010, Operation::Nop),
        i(
            0x1011,
            Operation::Branch {
                condition: 5,
                target: 0x1010,
            },
        ),
        i(0x1012, jump(Some(2), 0)),
    ];
    let found = search(&graph, 0x1012);
    assert!(found.reached_limit);
    assert_eq!(found.candidates.len(), 1);
    assert_eq!(found.candidates[0].table, 0x2000);
}

#[test]
fn the_same_table_merges_extents_without_erasing_the_wider_context() {
    let graph = [
        i(
            0x1000,
            Operation::Branch {
                condition: 5,
                target: 0x1020,
            },
        ),
        i(
            0x1001,
            Operation::Alu {
                kind: Alu::And,
                destination: Operand::Register(reg(7)),
                source: Operand::Immediate(1),
            },
        ),
        i(0x1002, Operation::Jump(0x1040)),
        i(
            0x1020,
            Operation::Alu {
                kind: Alu::And,
                destination: Operand::Register(reg(7)),
                source: Operand::Immediate(3),
            },
        ),
        i(0x1021, Operation::Jump(0x1040)),
        i(0x1040, jump(None, 0x2000)),
    ];
    let found = search(&graph, 0x1040);
    assert_eq!(found.candidates.len(), 1);
    assert_eq!(found.candidates[0].entries.len(), 4);
    assert_eq!(found.candidates[0].entry_limit_hint, Some(4));
}

#[test]
fn call_effects_and_redefined_flags_do_not_inherit_earlier_facts() {
    for barrier in [
        Operation::Call(0x3000),
        Operation::IndirectCall(Operand::Register(reg(0))),
    ] {
        let graph = [
            i(
                0x1000,
                Operation::Mov {
                    destination: Operand::Register(reg(2)),
                    source: Operand::Immediate(0x2000),
                },
            ),
            i(0x1001, barrier),
            i(0x1002, jump(Some(2), 0)),
        ];
        assert!(search(&graph, 0x1002).candidates.is_empty());
    }
    let graph = [
        i(
            0x1000,
            Operation::Alu {
                kind: Alu::Cmp,
                destination: Operand::Register(reg(7)),
                source: Operand::Immediate(1),
            },
        ),
        i(
            0x1001,
            Operation::Alu {
                kind: Alu::Test,
                destination: Operand::Register(reg(0)),
                source: Operand::Register(reg(0)),
            },
        ),
        i(
            0x1002,
            Operation::Branch {
                condition: 7,
                target: 0x1020,
            },
        ),
        i(0x1003, jump(None, 0x2000)),
        i(0x1020, Operation::Return { extra_pop: 0 }),
    ];
    let found = search(&graph, 0x1003);
    assert_eq!(found.candidates[0].entry_limit_hint, None);
    assert_eq!(found.candidates[0].entries.len(), 4);
}

#[test]
fn depth_path_and_graph_limits_bound_adversarial_contexts() {
    let mut graph: Vec<_> = (0..MAX_CONTEXT_INSTRUCTIONS + 1)
        .map(|n| i(0x1000 + n as u64, Operation::Nop))
        .collect();
    let branch = 0x1000 + graph.len() as u64;
    graph.push(i(branch, jump(None, 0x2000)));
    let found = search(&graph, branch);
    assert!(found.reached_limit);
    assert_eq!(found.candidates.len(), 1);

    let mut graph: Vec<_> = (0..100)
        .map(|n| {
            i(
                0x1000 + n,
                Operation::Branch {
                    condition: 5,
                    target: 0x1002 + n,
                },
            )
        })
        .collect();
    graph.push(i(0x1064, jump(None, 0x2000)));
    let found = search(&graph, 0x1064);
    assert!(found.reached_limit);
    assert!(found.paths <= MAX_CONTEXT_PATHS);
    assert!(found.work <= MAX_CONTEXT_WORK);
    assert_eq!(found.candidates.len(), 1);
    assert!(
        jump_tables::to_json_with_context_limits(&found.candidates, &[], &[0x1064])
            .unwrap()
            .contains("\"context_limited_branches\":[4196]")
    );

    graph.push(graph[0]);
    assert!(search(&graph, 0x1064).candidates.is_empty());
    let oversized = vec![i(0x1000, Operation::Nop); 16_385];
    assert!(search(&oversized, 0x1000).reached_limit);
}

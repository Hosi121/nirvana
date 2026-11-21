use nirvana::analysis::ControlFlowAnalysis;
use nirvana::cfg::BlockId;
use nirvana::goto_layout::{GotoLayout, MAX_LAYOUT_BLOCKS};
use nirvana::ir::{
    AccessKind, Assignment, BinaryOp, BlockExit, Control, Expr, IrInstruction, MemoryFault, Place,
    Program, Reg, RunStatus, Width,
};

fn register(index: usize) -> Expr {
    Expr::Register(Reg(index))
}

fn binary(operator: BinaryOp, left: Expr, right: Expr) -> Expr {
    Expr::binary(operator, left, right)
}

fn assign(index: usize, value: Expr) -> Assignment {
    Assignment {
        destination: Reg(index).into(),
        value,
    }
}

fn instruction(address: u64, assignments: Vec<Assignment>, control: Control) -> IrInstruction {
    IrInstruction {
        address,
        size: 1,
        assignments,
        control,
    }
}

fn jump(address: u64, target: u64) -> IrInstruction {
    instruction(address, vec![], Control::Jump(target))
}

fn returning(address: u64, value: u64) -> IrInstruction {
    instruction(address, vec![], Control::Return(Expr::Const(value)))
}

fn program(entry: u64, instructions: Vec<IrInstruction>) -> Program {
    Program::new(entry, 3, instructions).unwrap()
}

fn block(program: &Program, address: u64) -> BlockId {
    program.cfg().block_at(address).unwrap()
}

fn addresses(program: &Program, layout: &GotoLayout) -> Vec<u64> {
    layout
        .blocks()
        .iter()
        .map(|&id| program.cfg().block(id).start)
        .collect()
}

// Independently execute only retained blocks, resolving each original block
// exit through the plan. Block replay uses the checked IR machine, including
// faulting expressions, ordered assignments, and partially committed stores.
// Synthetic routing elimination intentionally changes traces and step counts.
fn replay(program: &Program, layout: &GotoLayout, input: &[u64], memory: &[u8]) {
    let expected = program.run_with_memory(input, 0, memory, 10_000).unwrap();
    let mut registers = input.to_vec();
    let mut memory = memory.to_vec();
    let mut current = layout.entry();
    let mut status = RunStatus::Suspended;
    for _ in 0..1_000 {
        assert!(layout.blocks().contains(&current));
        let report = program
            .run_block_with_memory(program.cfg().block(current).start, &registers, 0, &memory)
            .unwrap();
        registers = report.state.registers;
        memory = report.state.memory;
        match report.exit {
            BlockExit::Next(address) => current = layout.resolve(block(program, address)),
            BlockExit::Returned(value) => {
                status = RunStatus::Returned(value);
                break;
            }
            BlockExit::Fault(fault) => {
                status = RunStatus::Fault(fault);
                break;
            }
        }
    }
    assert_eq!(status, expected.status);
    assert_eq!(registers, expected.state.registers);
    assert_eq!(memory, expected.state.memory);
}

#[test]
fn unconditional_entry_chains_resolve_to_one_retained_return() {
    let p = program(0, vec![jump(0, 10), jump(10, 20), returning(20, 42)]);
    let layout = GotoLayout::compute(&p).unwrap();
    assert_eq!(addresses(&p, &layout), [20]);
    assert_eq!(layout.entry(), block(&p, 20));
    for address in [0, 10, 20] {
        assert_eq!(layout.resolve(block(&p, address)), block(&p, 20));
    }
    replay(&p, &layout, &[1, 2, 3], &[]);
}

#[test]
fn next_routes_are_threaded_without_requiring_a_literal_jump() {
    // The unreachable jump makes address 1 a block leader, so address 0's Next
    // is an actual inter-block fallthrough, not part of one merged block.
    let p = program(
        0,
        vec![
            instruction(0, vec![], Control::Next),
            jump(1, 20),
            jump(10, 1),
            returning(20, 42),
        ],
    );
    let layout = GotoLayout::compute(&p).unwrap();
    assert_eq!(addresses(&p, &layout), [20]);
    assert_eq!(layout.resolve(block(&p, 0)), block(&p, 20));
    replay(&p, &layout, &[1, 2, 3], &[]);
}

#[test]
fn shared_routing_tails_do_not_drop_the_branch_that_selects_them() {
    let p = program(
        0,
        vec![
            instruction(
                0,
                vec![],
                Control::Branch {
                    condition: register(0),
                    target: 20,
                },
            ),
            jump(1, 30),
            jump(20, 30),
            jump(30, 40),
            returning(40, 42),
        ],
    );
    let layout = GotoLayout::compute(&p).unwrap();
    assert_eq!(addresses(&p, &layout), [0, 40]);
    for address in [1, 20, 30] {
        assert_eq!(layout.resolve(block(&p, address)), block(&p, 40));
    }
    for condition in [0, 1, u64::MAX] {
        replay(&p, &layout, &[condition, 2, 3], &[]);
    }
}

#[test]
fn traversal_is_deterministic_and_visits_not_taken_before_taken() {
    let p = program(
        0,
        vec![
            instruction(
                0,
                vec![],
                Control::Branch {
                    condition: register(0),
                    target: 20,
                },
            ),
            instruction(1, vec![assign(1, Expr::Const(1))], Control::Jump(30)),
            instruction(20, vec![assign(1, Expr::Const(2))], Control::Jump(30)),
            instruction(30, vec![], Control::Return(register(1))),
        ],
    );
    let layout = GotoLayout::compute(&p).unwrap();
    assert_eq!(addresses(&p, &layout), [0, 1, 30, 20]);
    assert_eq!(layout.blocks(), GotoLayout::compute(&p).unwrap().blocks());
    for condition in [0, 1, u64::MAX] {
        replay(&p, &layout, &[condition, 2, 3], &[]);
    }
}

#[test]
fn same_target_and_pure_branches_are_always_retained() {
    for condition in [Expr::Const(0), Expr::Const(1), Expr::Const(u64::MAX)] {
        let p = program(
            0,
            vec![
                instruction(
                    0,
                    vec![],
                    Control::Branch {
                        condition,
                        target: 1,
                    },
                ),
                jump(1, 20),
                returning(20, 42),
            ],
        );
        let layout = GotoLayout::compute(&p).unwrap();
        assert_eq!(addresses(&p, &layout), [0, 20]);
        assert_eq!(layout.resolve(block(&p, 0)), block(&p, 0));
        replay(&p, &layout, &[1, 2, 3], &[]);
    }
}

#[test]
fn same_target_faulting_conditions_still_fault_before_the_shared_tail() {
    let p = program(
        0,
        vec![
            instruction(
                0,
                vec![],
                Control::Branch {
                    condition: Expr::load(Expr::Const(12), Width::U16),
                    target: 1,
                },
            ),
            jump(1, 20),
            returning(20, 42),
        ],
    );
    let layout = GotoLayout::compute(&p).unwrap();
    assert_eq!(addresses(&p, &layout), [0, 20]);
    assert_eq!(
        p.run_with_memory(&[1, 2, 3], 0, &[0; 8], 10)
            .unwrap()
            .status,
        RunStatus::Fault(MemoryFault {
            access: AccessKind::Read,
            address: 12,
            width: Width::U16
        })
    );
    replay(&p, &layout, &[1, 2, 3], &[0; 8]);
}

#[test]
fn every_assignment_is_retained_including_dead_pure_and_faulting_reads() {
    for value in [
        Expr::Const(7),
        register(2),
        Expr::load(Expr::Const(12), Width::U8),
    ] {
        let p = program(
            0,
            vec![
                instruction(0, vec![assign(1, value)], Control::Next),
                jump(1, 20),
                returning(20, 42),
            ],
        );
        let layout = GotoLayout::compute(&p).unwrap();
        assert_eq!(addresses(&p, &layout), [0, 20]);
        // The assignment is in the first instruction, not the terminator.
        assert_eq!(p.cfg().block(block(&p, 0)).instructions.len(), 2);
        replay(&p, &layout, &[1, 2, 3], &[0; 8]);
    }
}

#[test]
fn empty_self_loop_and_multiblock_cycles_keep_a_canonical_representative() {
    let p = program(0, vec![jump(0, 0)]);
    let layout = GotoLayout::compute(&p).unwrap();
    assert_eq!(addresses(&p, &layout), [0]);
    assert_eq!(layout.resolve(layout.entry()), layout.entry());
    replay(&p, &layout, &[1, 2, 3], &[]);

    for entry in [0, 10, 20] {
        let p = program(entry, vec![jump(0, 20), jump(10, 20), jump(20, 10)]);
        let layout = GotoLayout::compute(&p).unwrap();
        assert_eq!(addresses(&p, &layout), [10]);
        assert_eq!(layout.entry(), block(&p, 10));
        for address in [0, 10, 20] {
            assert_eq!(layout.resolve(block(&p, address)), block(&p, 10));
        }
        replay(&p, &layout, &[1, 2, 3], &[]);
    }
}

#[test]
fn branches_can_select_between_returning_and_empty_divergent_paths() {
    let p = program(
        0,
        vec![
            instruction(
                0,
                vec![],
                Control::Branch {
                    condition: register(0),
                    target: 100,
                },
            ),
            jump(1, 10),
            jump(10, 20),
            jump(20, 10),
            returning(100, 42),
        ],
    );
    let layout = GotoLayout::compute(&p).unwrap();
    assert_eq!(addresses(&p, &layout), [0, 10, 100]);
    for condition in [0, 1, u64::MAX] {
        replay(&p, &layout, &[condition, 2, 3], &[]);
    }
}

#[test]
fn effectful_irreducible_cycles_replay_with_exact_memory_and_return() {
    let increment = || assign(1, binary(BinaryOp::Add, register(1), Expr::Const(1)));
    let keep_running = || binary(BinaryOp::Ult, register(1), register(0));
    let p = program(
        0,
        vec![
            instruction(
                0,
                vec![],
                Control::Branch {
                    condition: register(2),
                    target: 20,
                },
            ),
            jump(1, 10),
            instruction(
                10,
                vec![
                    increment(),
                    Assignment {
                        destination: Place::Memory {
                            address: Expr::Const(0),
                            width: Width::U8,
                        },
                        value: register(1),
                    },
                ],
                Control::Branch {
                    condition: keep_running(),
                    target: 20,
                },
            ),
            jump(11, 30),
            instruction(
                20,
                vec![increment()],
                Control::Branch {
                    condition: keep_running(),
                    target: 10,
                },
            ),
            jump(21, 30),
            instruction(30, vec![], Control::Return(register(1))),
        ],
    );
    assert!(
        !ControlFlowAnalysis::compute(p.cfg())
            .unwrap()
            .is_reducible()
    );
    let layout = GotoLayout::compute(&p).unwrap();
    let mut kept = addresses(&p, &layout);
    kept.sort_unstable();
    assert_eq!(kept, [0, 10, 20, 30]);
    for count in 0..10 {
        for initial_arm in [0, 1] {
            replay(&p, &layout, &[count, 0, initial_arm], &[0xa5; 8]);
        }
    }
    replay(&p, &layout, &[4, 0, 0], &[]);
}

#[test]
fn unreachable_effectful_blocks_are_not_emitted_but_resolve_is_total() {
    let p = program(10, vec![returning(0, 99), jump(10, 20), returning(20, 42)]);
    let layout = GotoLayout::compute(&p).unwrap();
    assert_eq!(addresses(&p, &layout), [20]);
    assert_eq!(layout.resolve(block(&p, 0)), block(&p, 0));
    replay(&p, &layout, &[1, 2, 3], &[]);
}

#[test]
fn an_unresolved_unreachable_edge_rejects_the_entire_layout() {
    let p = program(0, vec![returning(0, 42), jump(10, 999)]);
    assert!(GotoLayout::compute(&p).is_none());
}

#[test]
fn resource_exhaustion_returns_none_instead_of_a_partial_plan() {
    // Only entry is reachable, keeping Program's dominator construction small.
    let p = program(
        0,
        (0..=MAX_LAYOUT_BLOCKS)
            .map(|address| returning(address as u64, 42))
            .collect(),
    );
    assert!(GotoLayout::compute(&p).is_none());
}

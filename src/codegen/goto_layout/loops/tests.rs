use super::*;
use crate::model::ir::{Assignment, Expr, IrInstruction, Reg};

fn nested() -> Program {
    let branch = |reg, target| Control::Branch {
        condition: Expr::Register(Reg(reg)),
        target,
    };
    Program::new(
        0,
        3,
        vec![
            IrInstruction {
                address: 0,
                size: 1,
                assignments: vec![],
                control: branch(0, 2),
            },
            IrInstruction {
                address: 1,
                size: 1,
                assignments: vec![],
                control: Control::Return(Expr::Register(Reg(2))),
            },
            IrInstruction {
                address: 2,
                size: 1,
                assignments: vec![],
                control: branch(1, 4),
            },
            IrInstruction {
                address: 3,
                size: 1,
                assignments: vec![],
                control: Control::Jump(0),
            },
            IrInstruction {
                address: 4,
                size: 1,
                assignments: vec![Assignment {
                    destination: Reg(2).into(),
                    value: Expr::Const(7),
                }],
                control: Control::Jump(2),
            },
        ],
    )
    .unwrap()
}

#[test]
fn nested_exit_breaks_to_an_outer_header_without_falling_out_of_both_loops() {
    let program = nested();
    let flat = GotoLayout::compute(&program).unwrap();
    let layout = LoopLayout::compute(&program, &flat).unwrap();
    assert_eq!(layout.loop_count(), 2);
    assert_eq!(layout.goto_count(), 0);
    let at = |pc| program.cfg().block_at(pc).unwrap();
    assert_eq!(flat.resolve(at(3)), at(0));
    assert_eq!(layout.transfer(at(2), at(0)), Some(Transfer::Break));
    assert_eq!(layout.transfer(at(0), at(1)), Some(Transfer::Break));
    assert!(check::validate(&program, &flat, &layout));
}

#[test]
fn altered_transfers_steps_and_loop_scopes_fail_the_source_checker() {
    let program = nested();
    let flat = GotoLayout::compute(&program).unwrap();
    let good = LoopLayout::compute(&program, &flat).unwrap();
    let at = |pc| program.cfg().block_at(pc).unwrap();
    for transfer in [
        Transfer::Continue,
        Transfer::Fallthrough,
        Transfer::Goto(at(4)),
    ] {
        let mut bad = good.clone();
        bad.edges.insert((at(2), at(0)), transfer);
        assert!(!check::validate(&program, &flat, &bad));
    }
    let mut missing = good.clone();
    missing.events.retain(|e| *e != Event::Block(at(4)));
    assert!(!check::validate(&program, &flat, &missing));
    let mut duplicate = good.clone();
    duplicate.events.push(Event::Block(at(1)));
    assert!(!check::validate(&program, &flat, &duplicate));
    let mut wrong_close = good.clone();
    let close = wrong_close
        .events
        .iter_mut()
        .find(|e| **e == Event::Close(at(2)))
        .unwrap();
    *close = Event::Close(at(0));
    assert!(!check::validate(&program, &flat, &wrong_close));
    let mut lost_scope = good.clone();
    lost_scope
        .events
        .retain(|e| !matches!(*e, Event::Open(id) | Event::Close(id) if id == at(2)));
    assert!(!check::validate(&program, &flat, &lost_scope));
}

#[test]
fn a_routing_cycle_remains_a_genuine_loop_and_a_return_is_not_one() {
    let program = Program::new(
        0,
        1,
        vec![IrInstruction {
            address: 0,
            size: 1,
            assignments: vec![],
            control: Control::Jump(0),
        }],
    )
    .unwrap();
    let flat = GotoLayout::compute(&program).unwrap();
    let layout = LoopLayout::compute(&program, &flat).unwrap();
    assert_eq!(layout.loop_count(), 1);
    assert_eq!(layout.goto_count(), 0);
    let id = flat.entry();
    let returned = Program::new(
        0,
        1,
        vec![IrInstruction {
            address: 0,
            size: 1,
            assignments: vec![],
            control: Control::Return(Expr::Const(0)),
        }],
    )
    .unwrap();
    let flat_returned = GotoLayout::compute(&returned).unwrap();
    let fake = LoopLayout {
        events: vec![Event::Open(id), Event::Block(id), Event::Close(id)],
        edges: BTreeMap::new(),
        entry: id,
    };
    assert!(!check::validate(&returned, &flat_returned, &fake));
}

#[test]
fn an_irreducible_inner_cycle_keeps_its_gotos_inside_a_genuine_outer_loop() {
    let program = Program::new(
        0,
        3,
        (0..6)
            .map(|pc| IrInstruction {
                address: pc,
                size: 1,
                assignments: vec![Assignment {
                    destination: Reg(2).into(),
                    value: Expr::Const(pc),
                }],
                control: if pc == 5 {
                    Control::Return(Expr::Register(Reg(2)))
                } else {
                    Control::Branch {
                        condition: Expr::Register(Reg(0)),
                        target: [3, 4, 1, 0, 2][pc as usize],
                    }
                },
            })
            .collect(),
    )
    .unwrap();
    assert!(
        !ControlFlowAnalysis::compute(program.cfg())
            .unwrap()
            .is_reducible()
    );
    let flat = GotoLayout::compute(&program).unwrap();
    let layout = LoopLayout::compute(&program, &flat).unwrap();
    assert_eq!(layout.loop_count(), 1);
    assert!(layout.goto_count() > 0);
    assert_eq!(
        layout
            .events()
            .iter()
            .filter(|e| matches!(e, Event::Block(_)))
            .count(),
        flat.blocks().len()
    );
    assert!(check::validate(&program, &flat, &layout));
}

#[test]
fn optional_region_limits_keep_the_original_flat_fallback_available() {
    let program = Program::new(
        0,
        1,
        (0..=MAX_BLOCKS)
            .map(|pc| IrInstruction {
                address: pc as u64,
                size: 1,
                assignments: vec![],
                control: Control::Return(Expr::Const(0)),
            })
            .collect(),
    )
    .unwrap();
    let flat = GotoLayout::compute(&program).unwrap();
    assert!(LoopLayout::compute(&program, &flat).is_none());
    assert_eq!(flat.blocks().len(), 1);
}

#[test]
fn a_foreign_routing_projection_cannot_hide_source_effects() {
    let source = nested();
    let flat = GotoLayout::compute(&source).unwrap();
    let layout = LoopLayout::compute(&source, &flat).unwrap();
    let mut instructions = source.instructions().to_vec();
    instructions[3].assignments.push(Assignment {
        destination: Reg(2).into(),
        value: Expr::Const(99),
    });
    let changed = Program::new(0, 3, instructions).unwrap();
    assert!(!check::validate(&changed, &flat, &layout));
    assert!(LoopLayout::compute(&changed, &flat).is_none());
    let changed_flat = GotoLayout::compute(&changed).unwrap();
    let changed_layout = LoopLayout::compute(&changed, &changed_flat).unwrap();
    assert!(
        changed_layout
            .events()
            .contains(&Event::Block(changed.cfg().block_at(3).unwrap()))
    );
}

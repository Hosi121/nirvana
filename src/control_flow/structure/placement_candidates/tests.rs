use super::*;
use crate::model::ir::IrInstruction;

fn chain() -> Program {
    Program::new(
        0,
        1,
        (0..10)
            .map(|address| IrInstruction {
                address,
                size: 1,
                assignments: vec![],
                control: if address == 9 {
                    Control::Return(Expr::Const(0))
                } else {
                    Control::Jump(address + 1)
                },
            })
            .collect(),
    )
    .unwrap()
}

#[test]
fn a_choice_is_revalidated_in_each_branch_and_lexical_stop() {
    let program = chain();
    let id = |address| program.cfg().block_at(address).unwrap();
    let mut plan = PlacementPlan {
        chosen: Some(Choice::Join {
            branch: id(0),
            join: Some(id(8)),
        }),
        ..PlacementPlan::default()
    };
    assert_eq!(
        plan.branch_join(id(0), Some(id(4)), Some(id(8)), None),
        Some(id(8))
    );
    // The same branch can be emitted in another active lexical region. Its
    // override must still be an available placement in that occurrence.
    assert_eq!(
        plan.branch_join(id(0), Some(id(4)), Some(id(9)), Some(id(4))),
        Some(id(4))
    );
    assert_eq!(
        plan.branch_join(id(1), Some(id(4)), Some(id(8)), None),
        Some(id(4))
    );
}

#[test]
fn independent_arms_keep_a_real_enclosing_stop() {
    let program = chain();
    let id = |address| program.cfg().block_at(address).unwrap();
    let mut plan = PlacementPlan {
        chosen: Some(Choice::Join {
            branch: id(0),
            join: None,
        }),
        ..PlacementPlan::default()
    };
    assert_eq!(plan.branch_join(id(0), Some(id(4)), None, None), None);
    assert_eq!(
        plan.branch_join(id(0), Some(id(4)), None, Some(id(4))),
        Some(id(4))
    );
}

#[test]
fn loop_follows_keep_the_active_parent_and_ancestor_boundaries() {
    let program = chain();
    let id = |address| program.cfg().block_at(address).unwrap();
    let mut contexts = [LoopContext {
        header: id(0),
        body: (0..9).map(id).collect(),
        exits: BTreeSet::from([id(9)]),
        follow: Some(id(9)),
    }];
    let exits = BTreeSet::from([id(0), id(7), id(9)]);
    let mut discovery = PlacementPlan::default();
    assert_eq!(
        discovery.loop_follow(id(3), &exits, &contexts, Ok(Some(id(9)))),
        Ok(Some(id(9)))
    );
    assert_eq!(
        discovery.follows,
        [Choice::Follow {
            header: id(3),
            follow: id(7)
        }]
    );
    let mut selected = PlacementPlan {
        chosen: Some(discovery.follows[0]),
        ..PlacementPlan::default()
    };
    assert_eq!(
        selected.loop_follow(id(3), &exits, &contexts, Ok(Some(id(9)))),
        Ok(Some(id(7)))
    );
    contexts[0].body.remove(&id(7));
    assert_eq!(
        selected.loop_follow(id(3), &exits, &contexts, Ok(Some(id(9)))),
        Ok(Some(id(9)))
    );
}

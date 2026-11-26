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
    let mut plan = JoinPlan {
        chosen: Some(Choice {
            branch: id(0),
            join: Some(id(8)),
        }),
        ..JoinPlan::default()
    };
    assert_eq!(
        plan.select(id(0), Some(id(4)), Some(id(8)), None),
        Some(id(8))
    );
    // The same branch can be emitted in another active lexical region. Its
    // override must still be an available placement in that occurrence.
    assert_eq!(
        plan.select(id(0), Some(id(4)), Some(id(9)), Some(id(4))),
        Some(id(4))
    );
    assert_eq!(
        plan.select(id(1), Some(id(4)), Some(id(8)), None),
        Some(id(4))
    );
}

#[test]
fn independent_arms_keep_a_real_enclosing_stop() {
    let program = chain();
    let id = |address| program.cfg().block_at(address).unwrap();
    let mut plan = JoinPlan {
        chosen: Some(Choice {
            branch: id(0),
            join: None,
        }),
        ..JoinPlan::default()
    };
    assert_eq!(plan.select(id(0), Some(id(4)), None, None), None);
    assert_eq!(
        plan.select(id(0), Some(id(4)), None, Some(id(4))),
        Some(id(4))
    );
}

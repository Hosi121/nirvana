use nirvana::ir::{Assignment, BinaryOp, Control, Expr, IrInstruction, Place, Program, Reg, Width};
use nirvana::structure::{Node, StructuredFunction};
use nirvana::structure_verify;

fn c(value: u64) -> Expr {
    Expr::Const(value)
}
fn r(index: usize) -> Expr {
    Expr::Register(Reg(index))
}

fn early_return_and_shared_store() -> Program {
    let store = |value| {
        vec![Assignment {
            destination: Place::Memory {
                address: r(1),
                width: Width::U8,
            },
            value: c(value),
        }]
    };
    let rows = vec![
        (
            vec![],
            Control::Branch {
                condition: Expr::binary(BinaryOp::And, r(0), c(1)),
                target: 3,
            },
        ),
        (
            vec![],
            Control::Branch {
                condition: Expr::binary(BinaryOp::And, r(0), c(2)),
                target: 4,
            },
        ),
        (vec![], Control::Return(Expr::load(r(1), Width::U64))),
        (store(10), Control::Jump(5)),
        (store(20), Control::Jump(5)),
        (vec![], Control::Return(Expr::load(r(1), Width::U8))),
    ];
    Program::new(
        0,
        2,
        rows.into_iter()
            .enumerate()
            .map(|(address, (assignments, control))| IrInstruction {
                address: address as u64,
                size: 1,
                assignments,
                control,
            })
            .collect(),
    )
    .unwrap()
}

#[test]
fn partial_joins_preserve_faulting_returns_stores_and_every_instruction_budget() {
    let p = early_return_and_shared_store();
    let f = StructuredFunction::recover_with_copy_limit(&p, 1).unwrap();
    assert_eq!(f.stats().extra_block_copies, 0);
    assert_eq!(f.evidence().original_steps, 6);
    assert_eq!(f.evidence().compared_copies, 6);
    assert_eq!(
        structure_verify::validate(&p, f.body()).unwrap(),
        f.evidence()
    );
    for input in 0..8 {
        for address in [0, 1, 7, 8, u64::MAX] {
            for base in [0, u64::MAX - 7] {
                for limit in 0..8 {
                    assert_eq!(
                        p.run_with_memory(
                            &[input, address],
                            base,
                            &[0, 1, 2, 3, 4, 5, 6, 7],
                            limit
                        ),
                        f.run_with_memory(
                            &[input, address],
                            base,
                            &[0, 1, 2, 3, 4, 5, 6, 7],
                            limit
                        ),
                        "input={input}, address={address}, base={base}, limit={limit}"
                    );
                }
            }
        }
    }
}

#[test]
fn a_misplaced_hoisted_tail_is_rejected_even_if_all_original_steps_are_present() {
    let p = early_return_and_shared_store();
    let mut body = StructuredFunction::recover(&p).unwrap().body().to_vec();
    let tail = body
        .iter()
        .position(|node| matches!(node, Node::Step { address: 5, .. }))
        .unwrap();
    let step = body.remove(tail);
    body.insert(0, step);
    assert!(structure_verify::validate(&p, &body).is_err());
}

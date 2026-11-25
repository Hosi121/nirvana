//! Check the actual inferred edge caps against the independent u64 SMT model.
//! These obligations cover one block's comparisons, not CFG-wide equivalence.

use crate::support::ir::{c, r};
use nirvana::{
    ir::{Assignment, BinaryOp as B, Control, Expr, IrInstruction, Program, Reg},
    value_width::ValueWidths,
    verify::{Solver, Verdict},
};

fn b(op: B, a: Expr, z: Expr) -> Expr {
    Expr::binary(op, a, z)
}

fn set(reg: usize, value: Expr) -> Assignment {
    Assignment {
        destination: Reg(reg).into(),
        value,
    }
}

fn hull(bits: u8) -> u64 {
    ((1u128 << bits) - 1) as u64
}

#[test]
#[ignore = "requires Z3; set NIRVANA_Z3"]
fn inferred_unsigned_guard_caps_hold_for_all_u64_inputs_with_replayed_mutants() {
    let solver = Solver::new(std::env::var_os("NIRVANA_Z3").expect("set NIRVANA_Z3"));
    let mut obligations = 0;
    let mut mutants = 0;
    for bound in [1, 2, 4, 16, 255, 256, 65535, 65536, 1 << 63, u64::MAX] {
        // Cover both relations and both truth values. On false arms the
        // variable is the right operand, so each case supplies an upper cap.
        for (op, truth, cap) in [
            (B::Ult, true, bound - 1),
            (B::Ult, false, bound),
            (B::Ule, true, bound),
            (B::Ule, false, bound - 1),
        ] {
            let (left, right) = if truth { (r(2), r(3)) } else { (r(3), r(2)) };
            let relation = b(op, left, right);
            let input_relation = if truth {
                b(op, r(0), c(bound))
            } else {
                b(op, c(bound), r(0))
            };
            let assumption = if truth {
                input_relation
            } else {
                b(B::Eq, input_relation, c(0))
            };
            for inverted in [false, true] {
                let condition = if inverted {
                    b(B::Xor, r(4), c(1))
                } else {
                    r(4)
                };
                let program = Program::new(
                    0,
                    5,
                    vec![
                        IrInstruction {
                            address: 0,
                            size: 1,
                            assignments: vec![
                                set(1, c(bound)),
                                set(2, r(0)),
                                set(3, r(1)),
                                set(4, relation.clone()),
                            ],
                            control: Control::Branch {
                                condition,
                                target: 2,
                            },
                        },
                        IrInstruction {
                            address: 1,
                            size: 1,
                            assignments: vec![],
                            control: Control::Return(r(0)),
                        },
                        IrInstruction {
                            address: 2,
                            size: 1,
                            assignments: vec![],
                            control: Control::Return(r(0)),
                        },
                    ],
                )
                .unwrap();
                let target = if truth != inverted { 2 } else { 1 };
                let widths = ValueWidths::analyze(&program);
                assert!(
                    widths.verification().is_ok(),
                    "{op:?}/{truth}/{bound}/{inverted}"
                );
                let index = program
                    .cfg()
                    .blocks()
                    .iter()
                    .position(|block| block.start == target)
                    .unwrap();
                let actual = widths.incoming().unwrap()[index].as_ref().unwrap()[0];
                let expected = (64 - cap.leading_zeros()) as u8;
                assert_eq!(actual, expected, "{op:?}/{truth}/{bound}/{inverted}");
                let violation =
                    |bits| Expr::select(assumption.clone(), b(B::Ult, c(hull(bits)), r(0)), c(0));
                assert_eq!(
                    solver.check(&violation(actual), &c(0)),
                    Verdict::EquivalentUnderModel
                );
                obligations += 1;
                if actual > 0 {
                    let Verdict::Counterexample(witness) =
                        solver.check(&violation(actual - 1), &c(0))
                    else {
                        panic!(
                            "missing too-narrow counterexample: {op:?}/{truth}/{bound}/{inverted}"
                        );
                    };
                    let input = witness
                        .registers
                        .iter()
                        .find(|(reg, _)| *reg == Reg(0))
                        .unwrap()
                        .1;
                    let execution = program.execute(&[input, 0, 0, 0, 0], 2).unwrap();
                    assert_eq!(execution.trace, [0, target]);
                    assert!(execution.value > hull(actual - 1));
                    mutants += 1;
                }
            }
        }
    }
    assert_eq!(obligations, 80);
    assert_eq!(mutants, 76);
    println!(
        "{obligations} inferred-cap u64 obligations; {mutants} too-narrow SAT controls replayed through source IR"
    );
}

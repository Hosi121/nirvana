use super::*;
use crate::ir::BinaryOp;

#[test]
fn store_obligations_use_the_value_at_the_ordered_assignment() {
    for overwrite in [false, true] {
        let mut assignments = vec![Assignment {
            destination: Reg(0).into(),
            value: Expr::binary(BinaryOp::Sub, Expr::Register(RSP), Expr::Const(8)),
        }];
        if overwrite {
            assignments.push(Assignment {
                destination: Reg(0).into(),
                value: Expr::Register(Reg(1)),
            });
        }
        let store = assignments.len();
        assignments.push(Assignment {
            destination: Place::Memory {
                address: Expr::Register(Reg(0)),
                width: Width::U64,
            },
            value: Expr::Const(7),
        });
        let source = [
            Instruction::Core(IrInstruction {
                address: 1,
                size: 1,
                assignments,
                control: Control::Next,
            }),
            Instruction::Return {
                address: 2,
                size: 1,
                extra_pop: 0,
            },
        ];
        let mut work = Work::default();
        preflight(&source, module_ir::REGISTER_COUNT, &mut work).unwrap();
        let projected = stack_program(&source, 1, &mut work).unwrap();
        let proposed = StackAnalysis::try_analyze(&projected, RSP).unwrap();
        let stack = stack::validate(&projected, RSP, &proposed).unwrap();
        assert_eq!(
            check_store(&stack, 1, store, &Expr::Register(Reg(0)), 8, &mut work).is_ok(),
            !overwrite
        );
    }
}

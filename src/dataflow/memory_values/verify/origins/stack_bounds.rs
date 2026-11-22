use super::*;
use crate::model::ir::IrInstruction;

#[test]
fn deep_saved_expressions_fit_a_two_megabyte_analysis_stack() {
    std::thread::Builder::new()
        .stack_size(2 * 1024 * 1024)
        .spawn(|| {
            let r = |n| Expr::Register(Reg(n));
            let mut value = r(0);
            for n in 0..60 {
                value = Expr::binary(B::Add, value, Expr::Const(n));
            }
            let source = Program::new(
                0,
                8,
                vec![IrInstruction {
                    address: 0,
                    size: 1,
                    assignments: vec![
                        Assignment {
                            destination: Place::Memory {
                                address: r(7),
                                width: Width::U64,
                            },
                            value,
                        },
                        Assignment {
                            destination: Reg(2).into(),
                            value: Expr::load(r(7), Width::U64),
                        },
                    ],
                    control: Control::Return(r(2)),
                }],
            )
            .unwrap();
            let plan = MemoryValuePlan::analyze(&source).unwrap();
            let candidate = plan.lower(&source).unwrap();
            for value in [0, 1, 1 << 63, u64::MAX] {
                let mut input = vec![0; 8];
                input[0] = value;
                input[7] = 4096;
                let before = source.run_with_memory(&input, 4096, &[0; 64], 1).unwrap();
                input.resize(candidate.register_count(), u64::MAX);
                let mut after = candidate
                    .run_with_memory(&input, 4096, &[0; 64], 1)
                    .unwrap();
                after.state.registers.truncate(8);
                assert_eq!(before, after);
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

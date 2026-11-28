//! Stable-load lowering reaches C allocation with intervening observations.
use super::*;

#[test]
fn stable_load_context_preserves_old_accumulator_stores_before_aliases_and_faults() {
    let set = |n, value| Assignment {
        destination: Reg(n).into(),
        value,
    };
    let program = Program::new(
        0,
        6,
        vec![
            instruction(0, vec![set(5, load(c(4104)))], Control::Next),
            instruction(1, vec![set(2, load(r(0)))], Control::Next),
            instruction(
                2,
                vec![
                    store(c(4104), Width::U64, r(5)),
                    set(4, load(b(BinaryOp::Add, r(0), c(8)))),
                ],
                Control::Next,
            ),
            instruction(
                3,
                vec![set(5, b(BinaryOp::Add, r(5), b(BinaryOp::Xor, r(2), r(1))))],
                Control::Next,
            ),
            instruction(
                4,
                vec![store(c(4096), Width::U64, r(5))],
                Control::Return(b(BinaryOp::Xor, r(5), r(4))),
            ),
        ],
    )
    .unwrap();
    let lowering =
        nirvana::load_consumer::lower_with_stable_inputs(&program, &[Reg(0), Reg(1)]).unwrap();
    lowering.validate().unwrap();
    assert_eq!(lowering.model_id(), nirvana::load_consumer::STABLE_MODEL_ID);
    let inputs: Vec<_> = [4095, 4096, 4097, 4104, 4111, u64::MAX]
        .into_iter()
        .flat_map(|address| [0, 1, 1 << 63, u64::MAX].map(|value| [address, value]))
        .collect();
    compare(&program, &inputs);
    compare(lowering.program(), &inputs);
}

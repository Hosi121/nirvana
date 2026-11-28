//! Context registers need an independent frame proof, not an address heuristic.
use super::*;

#[test]
fn stable_contexts_keep_aliases_fault_order_and_every_nonprivate_prefix() {
    let mut contexts = Vec::new();
    for op in [
        B::Add,
        B::Sub,
        B::Mul,
        B::And,
        B::Or,
        B::Xor,
        B::Shl,
        B::Shr,
        B::AShr,
        B::UMulHigh,
        B::SMulHigh,
        B::UDiv,
        B::URem,
        B::SDiv,
        B::SRem,
    ] {
        contexts.extend([b(op, r(1), r(4)), b(op, r(4), r(1))]);
    }
    contexts.push(b(B::Add, r(2), b(B::Xor, r(1), r(5))));
    for context in contexts {
        let source = basic(context);
        assert!(load_consumer::propose(&source, &[]).is_none());
        let lowered = load_consumer::lower_with_stable_inputs(
            &source,
            &[Reg(0), Reg(2), Reg(4), Reg(5), Reg(7)],
        )
        .unwrap();
        assert_eq!(lowered.model_id(), load_consumer::STABLE_MODEL_ID);
        lowered.validate().unwrap();
        assert_eq!(lowered.evidence().folds.len(), 1);
        assert!(!lowered.evidence().folds[0].inputs.is_empty());
        assert!(load_consumer::validate(&source, lowered.program(), &[]).is_err());
        compare(&source, lowered.program(), &[Reg(1)]);
    }
}

#[test]
fn assignment_order_and_consumer_destination_reads_define_the_frame_endpoints() {
    let source = program(vec![(
        vec![
            set(4, c(7)),
            set(1, Expr::load(r(0), Width::U64)),
            set(2, b(B::Add, r(1), r(4))),
            set(4, c(9)),
        ],
        Control::Return(r(2)),
    )]);
    let lowered = load_consumer::lower_with_stable_inputs(&source, &[Reg(0)]).unwrap();
    assert_eq!(lowered.evidence().folds[0].inputs, vec![Reg(4)]);
    compare(&source, lowered.program(), &[Reg(1)]);
    let source = basic(b(B::Add, r(1), r(2)));
    let candidate = load_consumer::propose_with_stable_inputs(&source, &[]).unwrap();
    load_consumer::validate_with_stable_inputs(&source, &candidate, &[]).unwrap();
    compare(&source, &candidate, &[Reg(1)]);
}

#[test]
fn intervening_register_definitions_are_rejected_in_same_and_different_instructions() {
    for same_instruction in [false, true] {
        let rows = if same_instruction {
            vec![(
                vec![
                    set(1, Expr::load(r(0), Width::U64)),
                    set(4, b(B::Add, r(4), c(1))),
                    set(2, b(B::Xor, r(1), r(4))),
                ],
                Control::Return(r(2)),
            )]
        } else {
            vec![
                (vec![set(1, Expr::load(r(0), Width::U64))], Control::Next),
                (vec![set(4, b(B::Add, r(4), c(1)))], Control::Next),
                (vec![set(2, b(B::Xor, r(1), r(4)))], Control::Return(r(2))),
            ]
        };
        let source = program(rows);
        assert!(load_consumer::propose_with_stable_inputs(&source, &[]).is_none());
        let mut instructions = source.instructions().to_vec();
        instructions[0].assignments[0].value = b(B::Xor, Expr::load(r(0), Width::U64), r(4));
        let last = instructions.last_mut().unwrap();
        last.assignments.last_mut().unwrap().value = r(1);
        let wrong = Program::new(0, 8, instructions).unwrap();
        assert!(load_consumer::validate_with_stable_inputs(&source, &wrong, &[]).is_err());
        let mut input = [0; 8];
        input[0] = 4096;
        let a = source.run_with_memory(&input, 4096, &[0; 32], 8).unwrap();
        let b = wrong.run_with_memory(&input, 4096, &[0; 32], 8).unwrap();
        assert_ne!(
            a.status, b.status,
            "the refused hoist really changes the return"
        );
    }
}

#[test]
fn load_address_registers_are_not_confused_with_consumer_context_inputs() {
    let source = changed(&basic(b(B::Add, r(1), r(4))), |rows| {
        rows[1].assignments.push(set(0, b(B::Add, r(0), c(1))))
    });
    let lowered = load_consumer::lower_with_stable_inputs(&source, &[Reg(0), Reg(7)]).unwrap();
    assert_eq!(lowered.evidence().folds[0].inputs, vec![Reg(4)]);
    compare(&source, lowered.program(), &[Reg(1)]);
    let unstable = changed(&source, |rows| {
        rows[2].assignments[0].value = b(B::Add, r(1), r(0))
    });
    assert!(load_consumer::propose_with_stable_inputs(&unstable, &[]).is_none());
}

#[test]
fn two_loads_sharing_a_consumer_keep_the_original_order_and_one_private_value() {
    let source = program(vec![
        (vec![set(1, Expr::load(r(0), Width::U64))], Control::Next),
        (vec![set(4, Expr::load(r(7), Width::U64))], Control::Next),
        (vec![set(2, b(B::Add, r(1), r(4)))], Control::Return(r(2))),
    ]);
    let lowered = load_consumer::lower_with_stable_inputs(&source, &[Reg(0), Reg(7)]).unwrap();
    lowered.validate().unwrap();
    assert_eq!(lowered.evidence().folds.len(), 1);
    assert_eq!(lowered.evidence().folds[0].temporary, Reg(4));
    assert_eq!(lowered.evidence().folds[0].inputs, vec![Reg(1)]);
    compare(&source, lowered.program(), &[Reg(4)]);
}

#[test]
fn constant_only_contexts_retain_the_v1_model_and_effectful_or_lazy_contexts_stay_outside() {
    let source = basic(b(B::Add, r(1), c(1)));
    let old = load_consumer::lower(&source, &[]).unwrap();
    let stable = load_consumer::lower_with_stable_inputs(&source, &[]).unwrap();
    assert_eq!(stable.model_id(), load_consumer::MODEL_ID);
    assert_eq!(old.evidence(), stable.evidence());
    assert_eq!(
        old.program().instructions(),
        stable.program().instructions()
    );
    for value in [
        Expr::select(r(4), r(1), c(0)),
        b(B::Add, r(1), Expr::load(r(4), Width::U8)),
        b(B::Add, r(1), r(1)),
    ] {
        assert!(load_consumer::propose_with_stable_inputs(&basic(value), &[]).is_none());
    }
}

#[test]
fn context_input_quota_bounds_matching_and_pair_acceptance() {
    let count = load_consumer::MAX_CONTEXT_INPUTS + 4;
    let context = |leaf, inputs| (2..2 + inputs).fold(leaf, |expr, n| b(B::Add, expr, r(n)));
    for inputs in [
        load_consumer::MAX_CONTEXT_INPUTS,
        load_consumer::MAX_CONTEXT_INPUTS + 1,
    ] {
        let source = Program::new(
            0,
            count,
            vec![
                IrInstruction {
                    address: 0,
                    size: 1,
                    assignments: vec![set(1, Expr::load(r(0), Width::U64))],
                    control: Control::Next,
                },
                IrInstruction {
                    address: 1,
                    size: 1,
                    assignments: vec![set(0, context(r(1), inputs))],
                    control: Control::Return(r(0)),
                },
            ],
        )
        .unwrap();
        if inputs == load_consumer::MAX_CONTEXT_INPUTS {
            let lower = load_consumer::lower_with_stable_inputs(&source, &[Reg(0)]).unwrap();
            lower.validate().unwrap();
            assert_eq!(lower.evidence().folds[0].inputs.len(), inputs);
            let mut initial = vec![3; count];
            initial[0] = 4096;
            for budget in 0..=3 {
                let mut a = source
                    .run_with_memory(&initial, 4096, &[5; 32], budget)
                    .unwrap();
                let mut b = lower
                    .program()
                    .run_with_memory(&initial, 4096, &[5; 32], budget)
                    .unwrap();
                a.state.registers[1] = 0;
                b.state.registers[1] = 0;
                assert_eq!(a, b);
            }
            continue;
        }
        assert!(load_consumer::propose_with_stable_inputs(&source, &[]).is_none());
        let mut rows = source.instructions().to_vec();
        rows[0].assignments[0].value = context(Expr::load(r(0), Width::U64), inputs);
        rows[1].assignments[0].value = r(1);
        let wrong = Program::new(0, count, rows).unwrap();
        assert_eq!(
            load_consumer::validate_with_stable_inputs(&source, &wrong, &[]),
            Err(Error::ResourceLimit)
        );
    }
}

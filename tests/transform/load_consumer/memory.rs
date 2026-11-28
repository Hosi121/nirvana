//! Whole producer expressions stay opaque, including lazy internal effects.
use super::*;
use nirvana::load_consumer::ProducerKind;

fn with_producer(producer: Expr, consumer: Expr) -> Program {
    changed(&basic(consumer), |rows| {
        rows[0].assignments[1].value = producer
    })
}

#[test]
fn opaque_memory_values_preserve_internal_loads_lazy_paths_aliases_and_faults() {
    let load = || Expr::load(r(0), Width::U64);
    let other = || Expr::load(r(7), Width::U8);
    let producers = [
        b(B::And, load(), c(255)),
        b(B::And, load(), c(0)),
        Expr::unary(nirvana::ir::UnaryOp::SignExtend(Width::U8), load()),
        b(B::Add, load(), other()),
        Expr::select(r(5), load(), other()),
        b(
            B::Xor,
            Expr::load(
                Expr::select(r(5), r(0), Expr::load(r(7), Width::U64)),
                Width::U8,
            ),
            c(3),
        ),
        // Same operator inside and outside the captured subtree.
        b(B::Add, load(), c(7)),
    ];
    for producer in producers {
        for consumer in [
            b(B::Add, r(1), r(4)),
            b(B::Sub, r(2), r(1)),
            b(B::Add, b(B::Add, r(1), c(7)), c(3)),
        ] {
            let source = with_producer(producer.clone(), consumer.clone());
            assert!(load_consumer::propose(&source, &[]).is_none());
            assert!(load_consumer::propose_with_stable_inputs(&source, &[]).is_none());
            let lower =
                load_consumer::lower_memory_values(&source, &[Reg(0), Reg(2), Reg(4), Reg(7)])
                    .unwrap();
            lower.validate().unwrap();
            assert_eq!(lower.model_id(), load_consumer::MEMORY_MODEL_ID);
            let fold = &lower.evidence().folds[0];
            assert_eq!(fold.producer_kind, ProducerKind::MemoryExpression);
            assert_eq!(fold.expression, consumer);
            assert!(
                load_consumer::validate_with_stable_inputs(&source, lower.program(), &[]).is_err()
            );
            compare(&source, lower.program(), &[Reg(1)]);
        }
    }
}

#[test]
fn the_exact_whole_memory_subtree_is_required_not_just_the_root_operator_or_load_count() {
    let load = || Expr::load(r(0), Width::U64);
    let other = || Expr::load(r(7), Width::U8);
    let producer = b(B::Xor, load(), other());
    let source = with_producer(producer.clone(), b(B::Add, r(1), r(4)));
    let lower = load_consumer::lower_memory_values(&source, &[]).unwrap();
    for wrong_producer in [
        load(),
        b(B::Xor, other(), load()),
        b(B::Xor, load(), load()),
        b(B::Xor, Expr::load(r(0), Width::U8), other()),
        b(B::Xor, Expr::load(r(4), Width::U64), other()),
        Expr::select(c(0), producer.clone(), c(0)),
        b(B::Add, producer.clone(), Expr::load(r(4), Width::U8)),
    ] {
        let wrong = changed(lower.program(), |rows| {
            rows[0].assignments[1].value = b(B::Add, wrong_producer, r(4))
        });
        assert!(load_consumer::validate_memory_values(&source, &wrong, &[]).is_err());
    }
    for wrong_value in [
        b(B::Add, producer.clone(), producer.clone()),
        Expr::select(r(4), producer.clone(), c(0)),
    ] {
        let wrong = changed(lower.program(), |rows| {
            rows[0].assignments[1].value = wrong_value
        });
        assert!(load_consumer::validate_memory_values(&source, &wrong, &[]).is_err());
    }
}

#[test]
fn context_frame_and_global_private_checks_still_apply_to_memory_producers() {
    let source = with_producer(
        b(B::And, Expr::load(r(0), Width::U64), c(255)),
        b(B::Add, r(1), r(4)),
    );
    let lower = load_consumer::lower_memory_values(&source, &[]).unwrap();
    // Producer-only inputs are read at the unchanged source point. Their later
    // definitions do not belong to the moved outer context's frame.
    let changed_address = changed(&source, |rows| {
        rows[1].assignments.push(set(0, b(B::Add, r(0), c(1))))
    });
    let retained = load_consumer::lower_memory_values(&changed_address, &[]).unwrap();
    assert_eq!(retained.evidence().folds[0].inputs, vec![Reg(4)]);
    compare(&changed_address, retained.program(), &[Reg(1)]);
    for register in [1, 4] {
        let original = changed(&source, |rows| {
            rows[1].assignments.push(set(register, c(19)))
        });
        let wrong = changed(lower.program(), |rows| {
            rows[1].assignments.push(set(register, c(19)))
        });
        assert!(load_consumer::propose_memory_values(&original, &[]).is_none());
        assert!(load_consumer::validate_memory_values(&original, &wrong, &[]).is_err());
    }
    assert!(load_consumer::lower_memory_values(&source, &[Reg(1)]).is_none());
    let extra_use = changed(&source, |rows| rows[1].assignments.push(set(6, r(1))));
    assert!(load_consumer::lower_memory_values(&extra_use, &[]).is_none());
    let pure = with_producer(b(B::Add, r(0), c(3)), b(B::Add, r(1), r(4)));
    assert!(load_consumer::lower_memory_values(&pure, &[]).is_none());
    for consumer in [
        Expr::select(r(4), r(1), c(0)),
        b(B::Add, r(1), Expr::load(r(4), Width::U8)),
        b(B::Add, r(1), r(1)),
    ] {
        let source = with_producer(b(B::And, Expr::load(r(0), Width::U64), c(255)), consumer);
        assert!(load_consumer::lower_memory_values(&source, &[]).is_none());
    }
}

#[test]
fn a_path_that_bypasses_the_producer_prevents_cross_block_hoisting() {
    let producer = b(B::And, Expr::load(r(0), Width::U64), c(255));
    let source = program(vec![
        (
            vec![],
            Control::Branch {
                condition: r(5),
                target: 2,
            },
        ),
        (vec![set(1, producer.clone())], Control::Next),
        (vec![set(2, b(B::Add, r(1), r(4)))], Control::Return(r(2))),
    ]);
    assert!(load_consumer::propose_memory_values(&source, &[]).is_none());
    let wrong = changed(&source, |rows| {
        rows[1].assignments[0].value = b(B::Add, producer, r(4));
        rows[2].assignments[0].value = r(1);
    });
    assert!(load_consumer::validate_memory_values(&source, &wrong, &[]).is_err());
    let mut input = [1; 8];
    input[0] = 4096;
    let a = source.run_with_memory(&input, 4096, &[0; 32], 8).unwrap();
    let z = wrong.run_with_memory(&input, 4096, &[0; 32], 8).unwrap();
    assert_ne!(a.status, z.status);
}

#[test]
fn narrower_producer_shapes_keep_their_original_model_ids_and_pairs() {
    for (consumer, model) in [
        (b(B::Add, r(1), c(3)), load_consumer::MODEL_ID),
        (b(B::Add, r(1), r(4)), load_consumer::STABLE_MODEL_ID),
    ] {
        let source = basic(consumer);
        let broad = load_consumer::lower_memory_values(&source, &[]).unwrap();
        let old = load_consumer::lower_with_stable_inputs(&source, &[]).unwrap();
        assert_eq!(broad.model_id(), model);
        assert_eq!(broad.evidence(), old.evidence());
        assert_eq!(broad.program().instructions(), old.program().instructions());
        broad.validate().unwrap();
    }
}

#[test]
fn checked_mask_producers_compose_after_local_value_reduction() {
    let source = program(vec![
        (vec![set(1, Expr::load(r(0), Width::U64))], Control::Next),
        (vec![set(2, b(B::And, r(1), c(255)))], Control::Next),
        (vec![set(6, b(B::Add, r(2), r(4)))], Control::Jump(3)),
        (vec![], Control::Return(r(6))),
    ]);
    let masked = nirvana::load_mask::propose(&source, &[Reg(0), Reg(4)]).unwrap();
    nirvana::load_mask::validate(&source, &masked, &[Reg(0), Reg(4)]).unwrap();
    let reduced = nirvana::reduce::reduce(&masked).unwrap();
    let lower =
        load_consumer::lower_memory_values(reduced.program(), reduced.parameters()).unwrap();
    lower.validate().unwrap();
    assert_eq!(lower.model_id(), load_consumer::MEMORY_MODEL_ID);
}

#[test]
fn opaque_producer_composition_keeps_input_and_combined_depth_quotas() {
    let count = load_consumer::MAX_CONTEXT_INPUTS + 4;
    for inputs in [
        load_consumer::MAX_CONTEXT_INPUTS,
        load_consumer::MAX_CONTEXT_INPUTS + 1,
    ] {
        let producer = b(B::And, Expr::load(r(0), Width::U64), c(255));
        let context = |leaf| (2..2 + inputs).fold(leaf, |expr, n| b(B::Add, expr, r(n)));
        let source = Program::new(
            0,
            count,
            vec![IrInstruction {
                address: 0,
                size: 1,
                assignments: vec![set(1, producer.clone()), set(0, context(r(1)))],
                control: Control::Return(r(0)),
            }],
        )
        .unwrap();
        if inputs == load_consumer::MAX_CONTEXT_INPUTS {
            let lower = load_consumer::lower_memory_values(&source, &[Reg(0)]).unwrap();
            lower.validate().unwrap();
            assert_eq!(lower.model_id(), load_consumer::MEMORY_MODEL_ID);
            assert_eq!(lower.evidence().folds[0].inputs.len(), inputs);
            let mut initial = vec![7; count];
            initial[0] = 4096;
            for budget in 0..=2 {
                let mut a = source
                    .run_with_memory(&initial, 4096, &[3; 32], budget)
                    .unwrap();
                let mut z = lower
                    .program()
                    .run_with_memory(&initial, 4096, &[3; 32], budget)
                    .unwrap();
                a.state.registers[1] = 0;
                z.state.registers[1] = 0;
                assert_eq!(a, z);
            }
        } else {
            assert!(load_consumer::lower_memory_values(&source, &[]).is_none());
            let wrong = Program::new(
                0,
                count,
                vec![IrInstruction {
                    address: 0,
                    size: 1,
                    assignments: vec![set(1, context(producer)), set(0, r(1))],
                    control: Control::Return(r(0)),
                }],
            )
            .unwrap();
            assert_eq!(
                load_consumer::validate_memory_values(&source, &wrong, &[]),
                Err(Error::ResourceLimit)
            );
        }
    }
    let nest = |mut value, depth| {
        for _ in 0..depth {
            value = Expr::unary(
                nirvana::ir::UnaryOp::Extract {
                    start: 0,
                    width: Width::U64,
                },
                value,
            );
        }
        value
    };
    let producer = nest(Expr::load(r(0), Width::U64), 80);
    let source = program(vec![(
        vec![set(1, producer.clone()), set(2, nest(r(1), 60))],
        Control::Return(r(2)),
    )]);
    assert!(load_consumer::lower_memory_values(&source, &[]).is_none());
    let wrong = changed(&source, |rows| {
        rows[0].assignments[0].value = nest(producer, 60);
        rows[0].assignments[1].value = r(1);
    });
    assert_eq!(
        load_consumer::validate_memory_values(&source, &wrong, &[]),
        Err(Error::ResourceLimit)
    );
}

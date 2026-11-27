use super::*;

fn checked(source: &Program) -> Program {
    let plan = BitPlan::analyze(source).unwrap();
    let (candidate, evidence) = plan.propose(source).expect("partial-bit identity");
    assert!(evidence.replacements > 0);
    assert_eq!(
        known_bits::validate(source, plan.graph(), plan.values(), &candidate).unwrap(),
        evidence
    );
    compare(source, &candidate);
    candidate
}

#[test]
fn nonconstant_masks_keep_the_correct_captured_operand_and_all_machine_prefixes() {
    let source = program(vec![
        ins(
            0,
            vec![
                set(1, Expr::load(r(7), Width::U8)),
                set(2, b(B::Or, r(6), c(255))),
                set(3, b(B::And, r(1), c(255))),
                set(4, b(B::And, r(2), r(3))),
                set(0, c(u64::MAX)),
            ],
            Control::Next,
        ),
        ins(
            1,
            vec![],
            Control::Return(Expr::unary(
                UnaryOp::Extract {
                    start: 0,
                    width: Width::U8,
                },
                r(4),
            )),
        ),
    ]);
    let candidate = checked(&source);
    assert_eq!(candidate.instructions()[0].assignments[2].value, r(1));
    assert_eq!(candidate.instructions()[0].assignments[3].value, r(3));
    assert_eq!(candidate.instructions()[1].control, Control::Return(r(4)));
}

#[test]
fn nested_equal_operator_heads_accept_partial_or_complete_identity_removal() {
    let source = program(vec![ins(
        0,
        vec![
            set(1, b(B::Or, r(0), c(255))),
            set(2, b(B::And, r(6), c(255))),
            set(3, b(B::Or, r(2), r(1))),
            set(4, b(B::Or, b(B::Or, r(3), c(3)), c(7))),
        ],
        Control::Return(b(B::Add, r(4), r(0))),
    )]);
    let candidate = checked(&source);
    assert_eq!(candidate.instructions()[0].assignments[2].value, r(1));
    assert_eq!(candidate.instructions()[0].assignments[3].value, r(3));
    let mut partial = source.instructions().to_vec();
    partial[0].assignments[3].value = b(B::Or, r(3), c(3));
    let partial = Program::new(0, 8, partial).unwrap();
    let plan = BitPlan::analyze(&source).unwrap();
    assert!(known_bits::validate(&source, plan.graph(), plan.values(), &partial).is_ok());
    compare(&source, &partial);
    let mut wrong = partial.instructions().to_vec();
    wrong[0].assignments[3].value = r(2);
    let wrong = Program::new(0, 8, wrong).unwrap();
    assert!(known_bits::validate(&source, plan.graph(), plan.values(), &wrong).is_err());
}

#[test]
fn kept_loads_and_lazy_arms_preserve_faults_even_when_another_load_is_bit_redundant() {
    let source = program(vec![ins(
        0,
        vec![
            set(1, b(B::Or, r(6), c(255))),
            set(2, b(B::Or, r(6), c(65535))),
        ],
        Control::Return(Expr::select(
            r(0),
            b(B::And, Expr::load(r(7), Width::U8), r(2)),
            b(B::Or, r(1), Expr::load(r(7), Width::U8)),
        )),
    )]);
    let candidate = checked(&source);
    let Control::Return(Expr::Select {
        taken, not_taken, ..
    }) = &candidate.instructions()[0].control
    else {
        panic!()
    };
    assert_eq!(**taken, Expr::load(r(7), Width::U8));
    assert!(matches!(&**not_taken,Expr::Binary(B::Or,_,load)if matches!(&**load,Expr::Load {..})));
    let mut wrong = candidate.instructions().to_vec();
    let Control::Return(Expr::Select { not_taken, .. }) = &mut wrong[0].control else {
        panic!()
    };
    **not_taken = r(1);
    let wrong = Program::new(0, 8, wrong).unwrap();
    let plan = BitPlan::analyze(&source).unwrap();
    assert!(known_bits::validate(&source, plan.graph(), plan.values(), &wrong).is_err());
    let mut input = [0; 8];
    input[7] = u64::MAX;
    assert_ne!(
        source.run_with_memory(&input, 4096, &[0; 32], 2),
        wrong.run_with_memory(&input, 4096, &[0; 32], 2)
    );
}

#[test]
fn sign_extension_requires_proved_high_bits_and_a_consistent_sign() {
    let source = program(vec![ins(
        0,
        vec![
            set(1, b(B::And, r(0), c(127))),
            set(2, Expr::unary(UnaryOp::SignExtend(Width::U8), r(1))),
            set(3, b(B::Or, r(6), c(!127))),
            set(4, Expr::unary(UnaryOp::SignExtend(Width::U8), r(3))),
        ],
        Control::Return(b(B::Xor, r(2), r(4))),
    )]);
    let candidate = checked(&source);
    assert_eq!(candidate.instructions()[0].assignments[1].value, r(1));
    assert_eq!(candidate.instructions()[0].assignments[3].value, r(3));
    let mut unknown = source.instructions().to_vec();
    unknown[0].assignments[0].value = b(B::And, r(0), c(255));
    let unknown = Program::new(0, 8, unknown).unwrap();
    let plan = BitPlan::analyze(&unknown).unwrap();
    assert!(known_bits::validate(&unknown, plan.graph(), plan.values(), &candidate).is_err());
}

#[test]
fn equally_valued_operands_keep_the_effectful_one() {
    let load = Expr::load(r(7), Width::U8);
    let source = program(vec![ins(
        0,
        vec![set(1, b(B::And, c(0), b(B::And, load.clone(), c(0))))],
        Control::Return(r(1)),
    )]);
    let candidate = checked(&source);
    assert_eq!(
        candidate.instructions()[0].assignments[0].value,
        b(B::And, load, c(0))
    );
    let mut wrong = candidate.instructions().to_vec();
    wrong[0].assignments[0].value = c(0);
    let wrong = Program::new(0, 8, wrong).unwrap();
    let plan = BitPlan::analyze(&source).unwrap();
    assert!(known_bits::validate(&source, plan.graph(), plan.values(), &wrong).is_err());
}

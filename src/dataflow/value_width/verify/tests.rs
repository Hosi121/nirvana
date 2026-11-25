use super::*;
use crate::dataflow::value_width::ValueWidths;
use crate::model::ir::{Assignment, BinaryOp as B, IrInstruction, Reg, UnaryOp};

fn c(value: u64) -> Expr {
    Expr::Const(value)
}
fn r(register: usize) -> Expr {
    Expr::Register(Reg(register))
}
fn b(op: B, left: Expr, right: Expr) -> Expr {
    Expr::binary(op, left, right)
}
fn set(register: usize, value: Expr) -> Assignment {
    Assignment {
        destination: Reg(register).into(),
        value,
    }
}
fn ins(address: u64, assignments: Vec<Assignment>, control: Control) -> IrInstruction {
    IrInstruction {
        address,
        size: 1,
        assignments,
        control,
    }
}
fn source(instructions: Vec<IrInstruction>) -> Program {
    Program::new(0, 8, instructions).unwrap()
}
fn straight(assignments: Vec<Assignment>, result: Expr) -> Program {
    source(vec![ins(0, assignments, Control::Return(result))])
}
fn proposal(source: &Program) -> (Vec<Width>, Vec<Option<Vec<u8>>>) {
    let candidate = ValueWidths::analyze_bounded(source).unwrap();
    assert!(validate(source, &candidate.0, &candidate.1).is_ok());
    assert!(ValueWidths::analyze(source).verification().is_ok());
    assert!(
        validate(
            source,
            &vec![Width::U64; source.register_count()],
            &candidate.1
        )
        .is_ok()
    );
    candidate
}

#[test]
fn overwrite_before_read_and_nonliteral_zero_shift_keep_current_storage() {
    let source = straight(
        vec![
            set(1, c(255)),
            set(2, c(0)),
            set(3, b(B::Shl, r(1), r(2))),
            set(1, c(65535)),
            set(4, c(0)),
        ],
        r(3),
    );
    let (widths, incoming) = proposal(&source);
    assert_eq!(widths[1], Width::U16);
    assert_eq!(widths[2], Width::U8);
    assert_eq!(widths[3], Width::U8);
    assert_eq!(widths[4], Width::U8);
    assert_eq!(widths[5], Width::U64); // Never observed; no zero assumption.
    assert_eq!(
        incoming[source.cfg().entry().index()].as_ref().unwrap(),
        &vec![64; 8]
    );
    assert_eq!(source.execute(&[u64::MAX; 8], 1).unwrap().value, 255);
    let evidence = validate(&source, &widths, &incoming).unwrap();
    assert_eq!(evidence.assignments, 5);
    assert_eq!(evidence.reads, 3);
}

#[test]
fn local_point_caps_survive_a_wider_later_write_to_the_same_register() {
    let source = straight(
        vec![
            set(1, Expr::load(c(4096), Width::U8)),
            set(2, b(B::Shl, r(1), c(1))),
            set(1, Expr::load(c(4097), Width::U16)),
        ],
        r(2),
    );
    let (widths, incoming) = proposal(&source);
    assert_eq!(widths[1], Width::U16);
    assert_eq!(widths[2], Width::U16);
    assert_eq!(
        source
            .execute_with_memory(&[0; 8], 4096, &[255; 3], 1)
            .unwrap()
            .value,
        510
    );
    let mut wrong = widths;
    wrong[2] = Width::U8;
    assert_eq!(
        validate(&source, &wrong, &incoming),
        Err(Invalid("storage write bound"))
    );
}

#[test]
fn an_earlier_wide_write_is_checked_even_when_only_the_last_value_is_read() {
    let source = straight(vec![set(0, c(u64::MAX)), set(0, c(0))], r(0));
    let (mut widths, incoming) = proposal(&source);
    assert_eq!(widths[0], Width::U64);
    assert_eq!(source.execute(&[0; 8], 1).unwrap().value, 0);
    let prefix = straight(vec![set(0, c(u64::MAX))], r(0));
    assert_eq!(prefix.execute(&[0; 8], 1).unwrap().value, u64::MAX);
    widths[0] = Width::U8;
    assert_eq!(
        validate(&source, &widths, &incoming),
        Err(Invalid("storage write bound"))
    );
    let fallback = ValueWidths::checked(&source, widths, incoming);
    assert_eq!(
        fallback.verification(),
        Err(&Invalid("storage write bound"))
    );
    for register in 0..=source.register_count() {
        assert_eq!(fallback.width(Reg(register)), Width::U64);
    }
}

#[test]
fn every_diamond_path_must_cover_unoverwritten_initial_values() {
    let source = source(vec![
        ins(
            0,
            vec![],
            Control::Branch {
                condition: r(7),
                target: 2,
            },
        ),
        ins(1, vec![set(0, c(0))], Control::Jump(3)),
        ins(2, vec![], Control::Jump(3)),
        ins(3, vec![], Control::Return(r(0))),
    ]);
    let (mut widths, incoming) = proposal(&source);
    assert_eq!(widths[0], Width::U64);
    let mut input = [0; 8];
    input[0] = u64::MAX;
    input[7] = 1;
    assert_eq!(source.execute(&input, 3).unwrap().value, u64::MAX);
    widths[0] = Width::U8;
    assert_eq!(
        validate(&source, &widths, &incoming),
        Err(Invalid("storage read bound"))
    );
    let mut concealed = incoming;
    let join = source.cfg().block_at(3).unwrap();
    concealed[join.index()].as_mut().unwrap()[0] = 0;
    assert_eq!(
        validate(&source, &widths, &concealed),
        Err(Invalid("successor entry bound"))
    );
}

fn counter(masked: bool) -> Program {
    let increment = b(B::Add, r(0), c(1));
    source(vec![
        ins(0, vec![set(0, c(0))], Control::Jump(1)),
        ins(
            1,
            vec![set(
                0,
                if masked {
                    b(B::And, increment, c(255))
                } else {
                    increment
                },
            )],
            Control::Branch {
                condition: r(1),
                target: 1,
            },
        ),
        ins(2, vec![], Control::Return(r(0))),
    ])
}

#[test]
fn masked_loop_invariants_are_inductive_and_unmasked_growth_cannot_narrow() {
    let source = counter(true);
    let (widths, incoming) = proposal(&source);
    assert_eq!(widths[0], Width::U8);
    let mut input = [0; 8];
    input[1] = 1;
    assert_eq!(
        source
            .run_with_memory(&input, 0, &[], 256)
            .unwrap()
            .state
            .registers[0],
        255
    );
    assert_eq!(
        source
            .run_with_memory(&input, 0, &[], 257)
            .unwrap()
            .state
            .registers[0],
        0
    );
    let header = source.cfg().block_at(1).unwrap();
    for bits in [0, 7] {
        let mut too_small = incoming.clone();
        too_small[header.index()].as_mut().unwrap()[0] = bits;
        assert_eq!(
            validate(&source, &widths, &too_small),
            Err(Invalid("successor entry bound"))
        );
    }
    let unmasked = counter(false);
    let (mut widths, incoming) = proposal(&unmasked);
    assert_eq!(widths[0], Width::U64);
    assert_eq!(
        unmasked
            .run_with_memory(&input, 0, &[], 257)
            .unwrap()
            .state
            .registers[0],
        256
    );
    widths[0] = Width::U8;
    assert!(matches!(
        validate(&unmasked, &widths, &incoming),
        Err(Invalid(_))
    ));
}

#[test]
fn entry_backedges_cannot_erase_the_virtual_arbitrary_u64_boundary() {
    let source = source(vec![
        ins(
            0,
            vec![set(6, r(0)), set(0, c(0))],
            Control::Branch {
                condition: r(7),
                target: 0,
            },
        ),
        ins(1, vec![], Control::Return(r(6))),
    ]);
    let (mut widths, incoming) = proposal(&source);
    let mut input = [0; 8];
    input[0] = u64::MAX;
    assert_eq!(source.execute(&input, 2).unwrap().value, u64::MAX);
    let mut wrong = incoming.clone();
    wrong[source.cfg().entry().index()].as_mut().unwrap()[0] = 0;
    assert_eq!(
        validate(&source, &widths, &wrong),
        Err(Invalid("arbitrary initial boundary"))
    );
    widths[0] = Width::U8;
    assert_eq!(
        validate(&source, &widths, &incoming),
        Err(Invalid("storage read bound"))
    );
}

#[test]
fn store_addresses_load_addresses_control_and_select_arms_are_observed() {
    let source = straight(
        vec![
            Assignment {
                destination: Place::Memory {
                    address: r(0),
                    width: Width::U8,
                },
                value: Expr::select(c(0), r(1), Expr::load(r(2), Width::U8)),
            },
            set(0, c(0)),
            set(1, c(0)),
            set(2, c(0)),
        ],
        Expr::select(r(3), c(0), c(0)),
    );
    let (widths, incoming) = proposal(&source);
    for register in 0..4 {
        assert_eq!(widths[register], Width::U64);
        let mut wrong = widths.clone();
        wrong[register] = Width::U8;
        assert_eq!(
            validate(&source, &wrong, &incoming),
            Err(Invalid("storage read bound"))
        );
    }
}

#[test]
fn full_word_total_division_and_negative_remainder_reject_narrow_storage() {
    for (expression, expected) in [
        (b(B::UDiv, c(0), r(0)), u64::MAX),
        (b(B::SRem, c(1 << 63), c(u64::MAX - 2)), u64::MAX - 1),
    ] {
        let source = straight(vec![set(6, expression)], r(6));
        let (mut widths, incoming) = proposal(&source);
        assert_eq!(source.execute(&[0; 8], 1).unwrap().value, expected);
        widths[6] = Width::U32;
        assert_eq!(
            validate(&source, &widths, &incoming),
            Err(Invalid("storage write bound"))
        );
    }
}

#[test]
fn dimensions_coverage_and_resource_failures_never_publish_partial_narrowing() {
    let source = counter(true);
    let (widths, incoming) = proposal(&source);
    assert_eq!(
        validate(&source, &widths[..7], &incoming),
        Err(Invalid("candidate dimensions"))
    );
    assert_eq!(
        validate(&source, &widths, &incoming[..incoming.len() - 1]),
        Err(Invalid("candidate dimensions"))
    );
    let header = source.cfg().block_at(1).unwrap().index();
    for kind in 0..3 {
        let mut wrong = incoming.clone();
        match kind {
            0 => wrong[header] = None,
            1 => wrong[header].as_mut().unwrap().push(0),
            _ => wrong[header].as_mut().unwrap()[0] = 65,
        }
        assert!(matches!(
            validate(&source, &widths, &wrong),
            Err(Invalid(_))
        ));
    }
    assert_eq!(
        validate_bounded(&source, &widths, &incoming, 0),
        Err(Unavailable("work limit"))
    );
    assert!(matches!(
        ValueWidths::default().verification(),
        Err(ValidationError::Unavailable(_))
    ));
    assert_eq!(ValueWidths::default().width(Reg(usize::MAX)), Width::U64);
}

#[test]
fn larger_register_files_original_depth_limit_and_unreachable_syntax_stay_supported() {
    let large = Program::new(
        0,
        4097,
        vec![ins(0, vec![set(4096, c(7))], Control::Return(r(4096)))],
    )
    .unwrap();
    let (widths, _) = proposal(&large);
    assert_eq!(widths[4096], Width::U8);
    for depth in [MAX_DEPTH, MAX_DEPTH + 1] {
        let mut expression = c(7);
        for _ in 0..depth {
            expression = Expr::unary(
                UnaryOp::Extract {
                    start: 0,
                    width: Width::U64,
                },
                expression,
            );
        }
        let source = straight(vec![set(6, expression.clone())], r(6));
        let widths = ValueWidths::analyze(&source);
        if depth == MAX_DEPTH {
            assert!(widths.verification().is_ok());
            assert_eq!(widths.width(Reg(6)), Width::U8);
        } else {
            assert!(matches!(
                widths.verification(),
                Err(ValidationError::Unavailable(_))
            ));
            assert_eq!(widths.width(Reg(6)), Width::U64);
            let unreachable = self::source(vec![
                ins(0, vec![set(6, c(0))], Control::Return(r(6))),
                ins(1, vec![set(6, expression)], Control::Jump(0)),
            ]);
            let (widths, incoming) = proposal(&unreachable);
            assert_eq!(widths[6], Width::U8);
            let mut spurious = incoming;
            let dead = unreachable.cfg().block_at(1).unwrap();
            spurious[dead.index()] = Some(vec![64; 8]);
            assert_eq!(
                validate(&unreachable, &widths, &spurious),
                Err(Invalid("reachable block coverage"))
            );
        }
    }
}

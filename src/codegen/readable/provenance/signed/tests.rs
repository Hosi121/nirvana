use super::*;
use crate::codegen::readable::STORAGE_CAPTURE_LIMITS;
use crate::dataflow::signed_width;
use crate::model::ir::{Assignment, Control, Expr, IrInstruction, Reg, UnaryOp, Width};

fn source() -> Arc<Program> {
    Arc::new(
        Program::new(
            0,
            2,
            vec![IrInstruction {
                address: 0,
                size: 1,
                assignments: vec![Assignment {
                    destination: Reg(1).into(),
                    value: Expr::unary(UnaryOp::SignExtend(Width::U32), Expr::Register(Reg(0))),
                }],
                control: Control::Return(Expr::Register(Reg(1))),
            }],
        )
        .unwrap(),
    )
}

#[test]
fn signed_capture_shares_the_final_source_and_consumed_certificate() {
    let source = source();
    let widths = SignedWidths::analyze(&source);
    assert_eq!(widths.width(Reg(1)), Width::U32);
    let selected = capture(CapturePolicy::On(STORAGE_CAPTURE_LIMITS), &source, widths);
    let SignedStorageProvenance::Captured(snapshot) = selected else {
        panic!("small checked signed analysis must be captured");
    };
    assert!(Arc::ptr_eq(&snapshot.source, &source));
    assert_eq!(Arc::strong_count(&source), 2);
    signed_width::validate(&source, &snapshot.widths).unwrap();
}

#[test]
fn signed_capture_off_does_not_retain_source_or_walk_capture_limits() {
    let source = source();
    let result = capture(CapturePolicy::Off, &source, SignedWidths::analyze(&source));
    assert!(matches!(result, SignedStorageProvenance::NotCaptured));
    assert_eq!(Arc::strong_count(&source), 1);
}

#[test]
fn signed_source_limits_omit_capture_without_retaining_an_arc() {
    let source = source();
    for limits in [
        StorageCaptureLimits {
            points: 0,
            ..STORAGE_CAPTURE_LIMITS
        },
        StorageCaptureLimits {
            expressions: 0,
            ..STORAGE_CAPTURE_LIMITS
        },
        StorageCaptureLimits {
            depth: 0,
            ..STORAGE_CAPTURE_LIMITS
        },
        StorageCaptureLimits {
            retained_bytes: 0,
            ..STORAGE_CAPTURE_LIMITS
        },
    ] {
        let result = capture(
            CapturePolicy::On(limits),
            &source,
            SignedWidths::analyze(&source),
        );
        assert!(matches!(result, SignedStorageProvenance::Unavailable(_)));
        assert_eq!(Arc::strong_count(&source), 1);
    }
}

#[test]
fn signed_retained_byte_limit_includes_ssa_and_claims() {
    let source = source();
    let source_bytes = source_budget(
        &source,
        STORAGE_CAPTURE_LIMITS,
        size_of::<SignedStorageSnapshot>(),
    )
    .unwrap()
    .bytes;
    let result = capture(
        CapturePolicy::On(StorageCaptureLimits {
            retained_bytes: source_bytes,
            ..STORAGE_CAPTURE_LIMITS
        }),
        &source,
        SignedWidths::analyze(&source),
    );
    assert!(matches!(
        result,
        SignedStorageProvenance::Unavailable("storage capture retained-byte limit")
    ));
    assert_eq!(Arc::strong_count(&source), 1);
}

#[test]
fn signed_failures_keep_their_reason_and_publish_no_snapshot() {
    let source = source();
    let result = capture(
        CapturePolicy::On(STORAGE_CAPTURE_LIMITS),
        &source,
        SignedWidths::default(),
    );
    assert!(matches!(result, SignedStorageProvenance::Unavailable(_)));
    let result = capture_with_status(
        CapturePolicy::On(StorageCaptureLimits {
            retained_bytes: 0,
            ..STORAGE_CAPTURE_LIMITS
        }),
        &source,
        SignedWidths::analyze(&source),
        Err(ValidationError::Invalid("known signed rejection")),
    );
    assert!(matches!(
        result,
        SignedStorageProvenance::Rejected("known signed rejection")
    ));
    assert_eq!(Arc::strong_count(&source), 1);
}

#[test]
fn signed_final_display_binding_differs_from_an_earlier_dead_write_source() {
    use crate::codegen::readable::provenance::{
        StorageProvenance, StorageSourcePhase, WidthAnalysis,
    };

    let final_display = source();
    let mut earlier = final_display.instructions().to_vec();
    earlier[0].assignments.insert(
        0,
        Assignment {
            destination: Reg(1).into(),
            value: Expr::Const(1 << 40),
        },
    );
    let earlier = Program::new(0, 2, earlier).unwrap();
    let (_, unsigned) = WidthAnalysis::before_presentation(&earlier).finish(
        CapturePolicy::On(STORAGE_CAPTURE_LIMITS),
        &earlier,
        &final_display,
    );
    let signed = capture(
        CapturePolicy::On(STORAGE_CAPTURE_LIMITS),
        &final_display,
        SignedWidths::analyze(&final_display),
    );
    let StorageProvenance::Captured(unsigned) = unsigned else {
        panic!("unsigned source missing")
    };
    let SignedStorageProvenance::Captured(signed) = signed else {
        panic!("signed source missing")
    };
    assert_eq!(
        unsigned.source_phase,
        StorageSourcePhase::BeforePresentation
    );
    assert_ne!(unsigned.source.instructions(), signed.source.instructions());
    assert!(Arc::ptr_eq(&signed.source, &final_display));
    assert_eq!(unsigned.widths.width(Reg(1)), Width::U64);
    assert_eq!(signed.widths.width(Reg(1)), Width::U32);
    signed_width::validate(&signed.source, &signed.widths).unwrap();
    assert!(signed_width::validate(&earlier, &signed.widths).is_err());
}

use super::*;
use crate::model::ir::{BinaryOp, UnaryOp};

fn source() -> Program {
    Program::new(
        0,
        2,
        vec![IrInstruction {
            address: 0,
            size: 1,
            assignments: vec![Assignment {
                destination: Reg(1).into(),
                value: Expr::unary(
                    UnaryOp::Extract {
                        start: 0,
                        width: Width::U8,
                    },
                    Expr::binary(BinaryOp::Add, Expr::Register(Reg(0)), Expr::Const(1)),
                ),
            }],
            control: Control::Return(Expr::Register(Reg(1))),
        }],
    )
    .unwrap()
}

#[test]
fn capture_limits_reject_before_retaining_a_source() {
    let source = source();
    let display = Arc::new(source.clone());
    let limits = [
        (
            StorageCaptureLimits {
                points: 0,
                ..STORAGE_CAPTURE_LIMITS
            },
            "storage capture point limit",
        ),
        (
            StorageCaptureLimits {
                expressions: 0,
                ..STORAGE_CAPTURE_LIMITS
            },
            "storage capture expression-node limit",
        ),
        (
            StorageCaptureLimits {
                depth: 0,
                ..STORAGE_CAPTURE_LIMITS
            },
            "storage capture expression-depth limit",
        ),
        (
            StorageCaptureLimits {
                retained_bytes: 0,
                ..STORAGE_CAPTURE_LIMITS
            },
            "storage capture retained-byte limit",
        ),
    ];
    for (limits, expected) in limits {
        let (widths, capture) =
            WidthAnalysis::after_dce(&display).finish(CapturePolicy::On(limits), &source, &display);
        assert!(matches!(capture, StorageProvenance::Unavailable(reason) if reason == expected));
        assert_eq!(widths.width(Reg(1)), Width::U8);
        assert_eq!(Arc::strong_count(&display), 1);
    }
}

#[test]
fn disabled_capture_retains_no_program_or_certificate() {
    let source = source();
    let display = Arc::new(source.clone());
    let (widths, capture) =
        WidthAnalysis::after_dce(&display).finish(CapturePolicy::Off, &source, &display);
    assert!(matches!(capture, StorageProvenance::NotCaptured));
    assert_eq!(Arc::strong_count(&display), 1);
    assert_eq!(widths.width(Reg(1)), Width::U8);
}

#[test]
fn failed_inference_does_not_bypass_source_retention_limits() {
    let source = source();
    let display = Arc::new(source.clone());
    let analysis = WidthAnalysis {
        widths: ValueWidths::default(),
        phase: StorageSourcePhase::DisplayAfterDce,
    };
    let (widths, capture) = analysis.finish(
        CapturePolicy::On(StorageCaptureLimits {
            expressions: 0,
            ..STORAGE_CAPTURE_LIMITS
        }),
        &source,
        &display,
    );
    assert!(widths.verification().is_err());
    assert!(matches!(capture, StorageProvenance::Unavailable(_)));
    assert_eq!(Arc::strong_count(&display), 1);
}

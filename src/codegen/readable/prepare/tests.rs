use super::*;
use crate::codegen::readable::{STORAGE_CAPTURE_LIMITS, StorageSourcePhase};
use crate::dataflow::value_width::validate;
use crate::model::ir::{IrInstruction, UnaryOp};

fn source(dead_wide_write: bool) -> Program {
    let mut assignments = Vec::new();
    if dead_wide_write {
        assignments.push(Assignment {
            destination: Reg(1).into(),
            value: Expr::Const(1 << 40),
        });
    }
    assignments.push(Assignment {
        destination: Reg(1).into(),
        value: Expr::binary(BinaryOp::And, Expr::Register(Reg(0)), Expr::Const(255)),
    });
    Program::new(
        0,
        2,
        vec![IrInstruction {
            address: 0,
            size: 1,
            assignments,
            control: Control::Return(Expr::unary(
                UnaryOp::Extract {
                    start: 0,
                    width: Width::U8,
                },
                Expr::Register(Reg(1)),
            )),
        }],
    )
    .unwrap()
}

#[test]
fn initial_storage_snapshot_keeps_the_input_before_presentation() {
    let source = source(false);
    let analysis = WidthAnalysis::before_presentation(&source);
    let display = Arc::new(presentation_program(&source, &|r| analysis.width(r)).unwrap());
    assert_ne!(source.instructions(), display.instructions());
    let (_, capture) =
        analysis.finish(CapturePolicy::On(STORAGE_CAPTURE_LIMITS), &source, &display);
    let StorageProvenance::Captured(snapshot) = capture else {
        panic!("bounded storage input must be retained");
    };
    assert_eq!(
        snapshot.source_phase,
        StorageSourcePhase::BeforePresentation
    );
    assert_eq!(snapshot.source.instructions(), source.instructions());
    assert!(!Arc::ptr_eq(&snapshot.source, &display));
    validate(
        &snapshot.source,
        snapshot.widths.widths().unwrap(),
        snapshot.widths.incoming().unwrap(),
    )
    .unwrap();
}

#[test]
fn checked_display_rebinds_storage_to_the_actual_dce_result() {
    let expanded = source(true);
    let before = WidthAnalysis::before_presentation(&expanded);
    assert_eq!(before.width(Reg(1)), Width::U64);
    let (candidate, analysis, _, ()) = checked_display(expanded.clone(), false, ()).unwrap();
    assert_ne!(candidate.instructions(), expanded.instructions());
    assert_eq!(analysis.width(Reg(1)), Width::U8);
    let display = Arc::new(candidate);
    let (widths, capture) = analysis.finish(
        CapturePolicy::On(STORAGE_CAPTURE_LIMITS),
        &expanded,
        &display,
    );
    let StorageProvenance::Captured(snapshot) = capture else {
        panic!("checked display source must be retained");
    };
    assert_eq!(snapshot.source_phase, StorageSourcePhase::DisplayAfterDce);
    assert!(Arc::ptr_eq(&snapshot.source, &display));
    assert_eq!(snapshot.widths.widths(), widths.widths());
    validate(
        &snapshot.source,
        snapshot.widths.widths().unwrap(),
        snapshot.widths.incoming().unwrap(),
    )
    .unwrap();
    assert!(
        validate(
            &expanded,
            snapshot.widths.widths().unwrap(),
            snapshot.widths.incoming().unwrap(),
        )
        .is_err(),
        "the dead wide write makes the earlier input an invalid binding"
    );
}

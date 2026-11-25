use super::*;
use crate::dataflow::value_width;
use std::sync::Arc;

fn source() -> Program {
    Program::new(
        0,
        8,
        vec![crate::ir::IrInstruction {
            address: 0,
            size: 1,
            assignments: vec![
                Assignment {
                    destination: Reg(0).into(),
                    value: Expr::load(Expr::Register(Reg(7)), Width::U8),
                },
                Assignment {
                    destination: Reg(1).into(),
                    value: Expr::binary(BinaryOp::Add, Expr::Register(Reg(0)), Expr::Const(1)),
                },
                Assignment {
                    destination: Place::Memory {
                        address: Expr::binary(
                            BinaryOp::Add,
                            Expr::Register(Reg(7)),
                            Expr::Const(1),
                        ),
                        width: Width::U8,
                    },
                    value: Expr::Register(Reg(1)),
                },
            ],
            control: Control::Return(Expr::binary(
                BinaryOp::Xor,
                Expr::Register(Reg(0)),
                Expr::Register(Reg(1)),
            )),
        }],
    )
    .unwrap()
}

#[test]
fn capture_budget_omission_preserves_normal_render_and_candidate_choice() {
    let source = source();
    let options = ReadableOptions {
        coalesce_locals: true,
        compact_memory: true,
        ..ReadableOptions::default()
    };
    let ordinary = emit_readable_c_with_options(&source, options).unwrap();
    let observed = emit_readable(
        &source,
        EmissionContext {
            options,
            capture: CapturePolicy::On(StorageCaptureLimits {
                retained_bytes: 0,
                ..STORAGE_CAPTURE_LIMITS
            }),
        },
    )
    .unwrap();
    assert_eq!(ordinary.code, observed.code);
    assert_eq!(ordinary.locals, observed.locals);
    assert_eq!(ordinary.memory_value_rounds, observed.memory_value_rounds);
    assert!(matches!(
        observed.storage_provenance,
        StorageProvenance::Unavailable("storage capture retained-byte limit")
    ));
    assert!(matches!(
        observed.signed_storage_provenance,
        SignedStorageProvenance::Unavailable("storage capture retained-byte limit")
    ));
}

#[test]
fn fallback_render_retains_its_actual_prepared_storage_snapshot() {
    let source = source();
    let reduced = reduce(&source).unwrap();
    let prepared = prepare::prepare_original(
        reduced.program(),
        reduced.parameters(),
        WebRecovery::RenderingFallback(ReadableError::LoopLabelsUnavailable),
        prepare::MemoryRecovery::Disabled,
        CapturePolicy::On(STORAGE_CAPTURE_LIMITS),
    )
    .unwrap();
    let StorageProvenance::Captured(selected) = &prepared.storage_provenance else {
        panic!("bounded fallback must retain its own source");
    };
    let selected = Arc::clone(selected);
    let final_display = Arc::clone(&prepared.program);
    let output = emit_prepared_c(
        &reduced,
        EmissionContext::with_storage_provenance(ReadableOptions::default()),
        prepared,
    )
    .unwrap();
    assert!(matches!(
        output.web_recovery,
        WebRecovery::RenderingFallback(_)
    ));
    let StorageProvenance::Captured(actual) = &output.storage_provenance else {
        panic!("selected fallback snapshot was lost");
    };
    assert!(Arc::ptr_eq(&selected, actual));
    let SignedStorageProvenance::Captured(signed) = &output.signed_storage_provenance else {
        panic!("selected signed fallback snapshot was lost");
    };
    assert!(Arc::ptr_eq(&signed.source, &final_display));
    crate::dataflow::signed_width::validate(&signed.source, &signed.widths).unwrap();
    value_width::validate(
        &actual.source,
        actual.widths.widths().unwrap(),
        actual.widths.incoming().unwrap(),
    )
    .unwrap();
    for local in &output.locals {
        assert!(
            local
                .registers
                .iter()
                .all(|&reg| actual.widths.width(reg).bits() <= local.width.bits())
        );
    }
}

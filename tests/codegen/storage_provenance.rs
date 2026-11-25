//! Observe the selected storage input through the ordinary candidate pipeline.
use crate::support::byte_values;
use nirvana::dataflow::value_width;
use nirvana::ir::Reg;
use nirvana::readable::{
    ReadableC, ReadableOptions, StorageProvenance, emit_middle_c_with_options,
    emit_middle_c_with_storage_provenance, emit_readable_c_with_options,
    emit_readable_c_with_storage_provenance,
};

fn check_selected(ordinary: &ReadableC, observed: &ReadableC) {
    assert_eq!(ordinary.code, observed.code, "capture changes generated C");
    assert_eq!(ordinary.parameters, observed.parameters);
    assert_eq!(ordinary.locals, observed.locals);
    assert!(matches!(
        ordinary.storage_provenance,
        StorageProvenance::NotCaptured
    ));
    let StorageProvenance::Captured(snapshot) = &observed.storage_provenance else {
        panic!("bounded evaluation programs must retain storage provenance");
    };
    value_width::validate(
        &snapshot.source,
        snapshot.widths.widths().unwrap(),
        snapshot.widths.incoming().unwrap(),
    )
    .unwrap();
    for local in &observed.locals {
        assert_eq!(local.registers.first(), Some(&local.register));
        for &member in &local.registers {
            assert!(member.0 < snapshot.source.register_count());
            assert!(snapshot.widths.width(member).bits() <= local.width.bits());
        }
    }
}

#[test]
fn selected_storage_capture_keeps_readable_and_middle_c_bytes_identical() {
    let options = ReadableOptions {
        stack_register: Some(Reg(4)),
        recover_objects: true,
        coalesce_locals: true,
        compact_memory: true,
    };
    let mut sources = byte_values::programs();
    sources.truncate(2);
    sources.push(byte_values::resaved_phi_programs().remove(0));
    sources.push(byte_values::invariant_loop_programs().remove(0));
    let mut checked_memory_rounds = false;
    for source in sources {
        let ordinary = emit_readable_c_with_options(&source, options).unwrap();
        let observed = emit_readable_c_with_storage_provenance(&source, options).unwrap();
        checked_memory_rounds |= observed.memory_value_rounds.len() >= 2;
        check_selected(&ordinary, &observed);
        let middle = nirvana::middle_ir::Function::from_low(&source).unwrap();
        let ordinary = emit_middle_c_with_options(&middle, options).unwrap();
        let observed = emit_middle_c_with_storage_provenance(&middle, options).unwrap();
        check_selected(&ordinary, &observed);
    }
    assert!(
        checked_memory_rounds,
        "exercise actual selected memory feedback"
    );
}

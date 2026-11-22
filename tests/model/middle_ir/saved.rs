use super::*;
use crate::support::byte_values;

fn compare_saved(source: &Program) -> usize {
    let middle = Function::from_low(source).unwrap();
    let (saved, evidence) = middle
        .recover_saved_values()
        .unwrap()
        .expect("checked saved values");
    assert!(evidence.annotated_reads > 0);
    assert_eq!(middle.validate_saved_recovery(&saved).unwrap(), evidence);
    assert_eq!(saved.lower().unwrap().instructions(), source.instructions());
    let (again, repeated) = saved.recover_saved_values().unwrap().unwrap();
    assert_eq!(repeated, evidence);
    assert_eq!(again.to_text().unwrap(), saved.to_text().unwrap());
    let lowered = saved.lower_saved_values().unwrap().unwrap();
    assert_eq!(lowered.source_registers(), source.register_count());
    let mut count = 0;
    for value in [0u64, 1, 0x1122334455667788, u64::MAX] {
        for branch in [0u64, 1, 3] {
            let mut memory = [0xa5; 64];
            memory[..8].copy_from_slice(&value.to_le_bytes());
            memory[8..16].copy_from_slice(&branch.to_le_bytes());
            memory[24..32].copy_from_slice(&branch.to_le_bytes());
            for pointer in [4096, 4097, 4127, u64::MAX] {
                let mut input = vec![value; source.register_count()];
                input[1] = branch;
                input[7] = pointer;
                let mut extended = input.clone();
                extended.resize(lowered.program().register_count(), 0xdeadbeefcafebabe);
                for budget in [0, 1, 2, 3, 4, 8, 16, 32] {
                    let expected = source
                        .run_with_memory(&input, 4096, &memory, budget)
                        .unwrap();
                    assert_eq!(
                        saved
                            .run_with_memory(&input, 4096, &memory, budget)
                            .unwrap(),
                        expected
                    );
                    let actual = lowered
                        .program()
                        .run_with_memory(&extended, 4096, &memory, budget)
                        .unwrap();
                    assert_eq!(
                        lowered.project_report(actual).unwrap(),
                        expected,
                        "value={value:x}, branch={branch}, pointer={pointer}, budget={budget}"
                    );
                    count += 1;
                }
            }
        }
    }
    count
}

#[test]
fn dynamic_saved_words_cross_partial_writes_overwrites_phis_and_loops_in_middle_ir() {
    let mut count = 0;
    let mut programs = 0;
    for source in byte_values::programs() {
        count += compare_saved(&source);
        programs += 1;
    }
    println!(
        "{programs} shared saved-value programs, {count} native MIR/projected lowering prefixes"
    );
}

#[test]
fn equal_phi_inputs_share_a_snapshot_and_different_inputs_keep_the_phi() {
    for source in byte_values::register_phi_programs() {
        let middle = Function::from_low(&source).unwrap();
        let (saved, evidence) = middle.recover_saved_values().unwrap().unwrap();
        assert!(evidence.phi_values > 0);
        let view = saved.saved_values().unwrap();
        assert_eq!(view.snapshots.len(), 1);
        assert!(
            view.values
                .iter()
                .flatten()
                .any(|s| s.start == 8 && s.width == Width::U16)
        );
        assert!(saved.to_text().unwrap().contains("saved #0 bits 8:16"));
    }
    let source = byte_values::register_phi_programs().remove(0);
    let original_plan = nirvana::memory_values::MemoryValuePlan::analyze(&source).unwrap();
    for replacement in [
        vec![set(2, Expr::load(b(B::Add, r(7), c(34)), Width::U16))],
        vec![set(2, Expr::load(b(B::Add, r(7), c(48)), Width::U16))],
        vec![],
    ] {
        let mut rows = source.instructions().to_vec();
        rows[2].assignments = replacement;
        let changed = Program::new(0, 8, rows).unwrap();
        assert!(original_plan.inspect(&changed).is_err());
        let middle = Function::from_low(&changed).unwrap();
        if let Some((saved, _)) = middle.recover_saved_values().unwrap() {
            let block = saved.blocks().iter().find(|b| b.address == 3).unwrap();
            let Terminator::Return(value) = &block.terminator else {
                panic!()
            };
            assert!(
                value
                    .bindings
                    .iter()
                    .all(|b| !matches!(b.operation, Operation::ReadSaved { .. }))
            );
        }
    }
}

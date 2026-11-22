use crate::support::{byte_values, checked_c, native};
use nirvana::ir::{AccessKind, Reg, RunStatus};
use std::fmt::Write as _;

#[test]
fn resaved_phi_slices_share_storage_after_checked_memory_rounds() {
    let source = byte_values::resaved_phi_programs().remove(0);
    let out = nirvana::readable::emit_readable_c_with_options(
        &source,
        nirvana::readable::ReadableOptions {
            stack_register: Some(Reg(4)),
            coalesce_locals: true,
            recover_objects: true,
            compact_memory: true,
        },
    )
    .unwrap();
    assert!(
        out.locals.len() <= 2,
        "saved input and branch condition suffice: {}",
        out.locals.len()
    );
    assert!(
        out.memory_value_rounds.len() >= 2,
        "the selected C must use checked feedback"
    );
}

#[test]
fn partial_saved_values_keep_full_ram_first_faults_and_aliases_in_portable_c() {
    let scratch = native::Scratch::new();
    let mut checked = 0;
    let mut adopted = 0;
    let mut middle_adopted = 0;
    let mut all_statuses = [0; 3];
    for (index, source) in byte_values::programs().into_iter().enumerate() {
        assert!(nirvana::memory_values::MemoryValuePlan::analyze(&source).is_some());
        let mut input = String::new();
        let mut expected = Vec::new();
        let mut statuses = [0; 3];
        for pointer in [
            4096u64,
            4097,
            4104,
            4112,
            4120,
            4123,
            4125,
            4127,
            4136,
            4152,
            4159,
            u64::MAX,
        ] {
            for value in [
                0u64,
                1,
                2,
                3,
                127,
                128,
                255,
                256,
                1 << 31,
                1 << 63,
                u64::MAX,
                0x1234_5678_9abc_def0,
            ] {
                for flag in [0u64, 1] {
                    let words = [value, value ^ (value >> 8), 19, flag];
                    writeln!(
                        input,
                        "{pointer} {} {} {} {}",
                        words[0], words[1], words[2], words[3]
                    )
                    .unwrap();
                    let mut ram: Vec<_> = (0..64u8)
                        .map(|i| i.wrapping_mul(29).wrapping_add(7))
                        .collect();
                    for (word, value) in words.into_iter().enumerate() {
                        if let Some(offset) = pointer
                            .checked_add(word as u64 * 8)
                            .and_then(|p| p.checked_sub(4096))
                            .filter(|n| *n <= 56)
                        {
                            ram[offset as usize..offset as usize + 8]
                                .copy_from_slice(&value.to_le_bytes());
                        }
                    }
                    let mut regs = [0; 8];
                    regs[7] = pointer;
                    regs[4] = 4160;
                    let report = source.run_with_memory(&regs, 4096, &ram, 1000).unwrap();
                    let mut row = match report.status {
                        RunStatus::Returned(v) => {
                            statuses[0] += 1;
                            vec![0, 0, 0, 0, v]
                        }
                        RunStatus::Fault(f) => {
                            let kind = if f.access == AccessKind::Read { 1 } else { 2 };
                            statuses[kind] += 1;
                            vec![1, f.address, kind as u64, f.width.bytes() as u64, 0]
                        }
                        _ => panic!("bounded saved-value family"),
                    };
                    row.extend(
                        report
                            .state
                            .memory
                            .chunks_exact(8)
                            .map(|w| u64::from_le_bytes(w.try_into().unwrap())),
                    );
                    expected.push(row);
                }
            }
        }
        assert!(statuses[0] > 0, "family {index} returns");
        assert!(
            statuses[1] + statuses[2] > 0,
            "family {index} has a first fault"
        );
        // Store-only prefixes fault on the write before any later read.
        for (all, count) in all_statuses.iter_mut().zip(statuses) {
            *all += count;
        }
        for coalesce in [false, true] {
            for objects in [false, true] {
                let options = nirvana::readable::ReadableOptions {
                    stack_register: Some(Reg(4)),
                    coalesce_locals: coalesce,
                    recover_objects: objects,
                    compact_memory: true,
                };
                let out =
                    nirvana::readable::emit_readable_c_with_options(&source, options).unwrap();
                adopted += usize::from(out.memory_values.is_some());
                let mut outputs = vec![("readable", out)];
                if coalesce && objects {
                    let middle = nirvana::middle_ir::Function::from_low(&source).unwrap();
                    let (saved, _) = middle.recover_saved_values().unwrap().unwrap();
                    let lowered = saved.lower_saved_values().unwrap().unwrap();
                    let materialized =
                        nirvana::readable::emit_readable_c_with_options(lowered.program(), options)
                            .unwrap();
                    let selected =
                        nirvana::readable::emit_middle_c_with_options(&middle, options).unwrap();
                    assert_eq!(selected.parameters, outputs[0].1.parameters);
                    let cost = |out: &nirvana::readable::ReadableC| {
                        (
                            out.locals.len(),
                            out.code
                                .split_once("uint64_t nirvana_readable(")
                                .unwrap()
                                .1
                                .len(),
                            out.code.len(),
                        )
                    };
                    assert!(cost(&selected) <= cost(&outputs[0].1));
                    middle_adopted += usize::from(selected.middle_saved.is_some());
                    outputs.extend([("saved", materialized), ("middle", selected)]);
                }
                for (backend, out) in outputs {
                    let path = scratch.0.join(format!(
                        "byte-values-{index}-{coalesce}-{objects}-{backend}.c"
                    ));
                    std::fs::write(&path, checked_c::source(&out, 8, 4)).unwrap();
                    for opt in ["-O0", "-O2"] {
                        let binary = path.with_extension(format!("{opt}.bin"));
                        native::compile_c(
                            &path,
                            &binary,
                            &[
                                opt,
                                "-fsanitize=undefined",
                                "-fno-sanitize-recover=undefined",
                            ],
                        );
                        assert_eq!(
                            native::run_fields(&binary, &input, 13),
                            expected,
                            "family {index}/{coalesce}/{objects}/{backend}/{opt}"
                        );
                        checked += expected.len();
                    }
                }
            }
        }
    }
    assert!(all_statuses.into_iter().all(|n| n > 0));
    assert!(adopted > 0, "source recovery must reach selected C output");
    println!(
        "{checked} partial saved-value C/full-RAM/first-fault observations; {adopted} render configurations adopted value snapshots; {middle_adopted} selected native MIR snapshots"
    );
}

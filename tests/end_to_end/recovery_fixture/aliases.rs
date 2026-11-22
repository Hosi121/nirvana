//! Guest inputs may overlap the callee's stack, beyond an ordinary C call ABI.
use super::*;
use crate::support::checked_c;
use nirvana::ir::{AccessKind, RunStatus};

#[test]
fn early_saved_values_keep_real_gcc_stack_aliases_and_first_faults() {
    const MEMORY_SIZE: usize = 256;
    let scratch = Scratch::new();
    let object_path = scratch.0.join("signed-compare.o");
    object(
        &fixture_root().join("recovery/signed-compare.c"),
        &object_path,
        "-O0",
        "fixture",
    );
    let source = frontend::lift_elf_auto(&std::fs::read(&object_path).unwrap(), "fixture")
        .unwrap()
        .program;
    let plan = nirvana::memory_values::MemoryValuePlan::analyze(&source).unwrap();
    let captured = plan.lower(&source).unwrap();
    let mut input = String::new();
    let mut expected = Vec::new();
    let mut statuses = [0; 3];
    let mut state_checks = 0;
    for pointer in [
        4096u64,
        4097,
        4224,
        4264,
        4272,
        4280,
        4288,
        4296,
        4328,
        4344,
        4351,
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
                let words = [value, value.rotate_left(17) ^ flag, 19, flag];
                writeln!(
                    input,
                    "{pointer} {} {} {} {}",
                    words[0], words[1], words[2], words[3]
                )
                .unwrap();
                let mut memory: Vec<_> = (0..MEMORY_SIZE)
                    .map(|i| (i as u8).wrapping_mul(29).wrapping_add(7))
                    .collect();
                for (word, value) in words.into_iter().enumerate() {
                    if let Some(offset) = pointer
                        .checked_add(word as u64 * 8)
                        .and_then(|p| p.checked_sub(4096))
                        .filter(|o| *o <= (MEMORY_SIZE - 8) as u64)
                    {
                        memory[offset as usize..offset as usize + 8]
                            .copy_from_slice(&value.to_le_bytes());
                    }
                }
                let mut registers = vec![0; source.register_count()];
                registers[x86::RDI] = pointer;
                registers[x86::RSP] = 4096 + MEMORY_SIZE as u64;
                let mut extended = registers.clone();
                extended.resize(captured.register_count(), 0xdead_beef_1234_5678);
                for limit in [0, 1, 2, 4, 8, 16, 32, 64, 128] {
                    let before = source
                        .run_with_memory(&registers, 4096, &memory, limit)
                        .unwrap();
                    let mut after = captured
                        .run_with_memory(&extended, 4096, &memory, limit)
                        .unwrap();
                    after.state.registers.truncate(source.register_count());
                    assert_eq!(before, after, "{pointer}/{value}/{flag}/{limit}");
                    state_checks += 1;
                }
                let report = source
                    .run_with_memory(&registers, 4096, &memory, 128)
                    .unwrap();
                let mut row = match report.status {
                    RunStatus::Returned(value) => {
                        statuses[0] += 1;
                        vec![0, 0, 0, 0, value]
                    }
                    RunStatus::Fault(fault) => {
                        let access = if fault.access == AccessKind::Read {
                            1
                        } else {
                            2
                        };
                        statuses[access] += 1;
                        vec![
                            1,
                            fault.address,
                            access as u64,
                            fault.width.bytes() as u64,
                            0,
                        ]
                    }
                    _ => panic!("bounded signed comparisons"),
                };
                row.extend(
                    report
                        .state
                        .memory
                        .chunks_exact(8)
                        .map(|b| u64::from_le_bytes(b.try_into().unwrap())),
                );
                expected.push(row);
            }
        }
    }
    assert!(statuses.into_iter().all(|n| n > 0), "{statuses:?}");
    let mut checked = 0;
    for coalesce in [false, true] {
        for objects in [false, true] {
            let out = readable::emit_readable_c_with_options(
                &source,
                readable::ReadableOptions {
                    stack_register: Some(Reg(x86::RSP)),
                    coalesce_locals: coalesce,
                    recover_objects: objects,
                    compact_memory: true,
                },
            )
            .unwrap();
            let path = scratch.0.join(format!("aliases-{coalesce}-{objects}.c"));
            std::fs::write(
                &path,
                checked_c::source_with_size(&out, source.register_count(), 4, MEMORY_SIZE),
            )
            .unwrap();
            for optimization in ["-O0", "-O2"] {
                let binary = path.with_extension(format!("{optimization}.bin"));
                native::compile_c(
                    &path,
                    &binary,
                    &[
                        optimization,
                        "-fsanitize=undefined",
                        "-fno-sanitize-recover=undefined",
                    ],
                );
                assert_eq!(
                    run_fields(&binary, &input, 5 + MEMORY_SIZE / 8),
                    expected,
                    "{coalesce}/{objects}/{optimization}"
                );
                checked += expected.len();
            }
        }
    }
    println!(
        "{state_checks} GCC stack-alias full-state budget observations; {checked} exact C RAM/first-fault observations"
    );
}

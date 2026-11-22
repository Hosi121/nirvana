use super::*;

#[test]
fn real_gcc_functions_keep_full_state_across_middle_ir_and_back() {
    use crate::support::native;
    let scratch = native::Scratch::new();
    let mut observations = 0;
    for name in ["shared-tail", "multi-exit-prefix"] {
        for opt in ["-O0", "-O2", "-O3"] {
            let object = scratch.0.join(format!("{name}-{opt}.o"));
            native::object(
                &native::fixture_root().join(format!("cases/{name}.c")),
                &object,
                opt,
                "fixture",
            );
            let source =
                nirvana::frontend::lift_elf_auto(&std::fs::read(object).unwrap(), "fixture")
                    .unwrap()
                    .program;
            let mut inputs = Vec::new();
            let mut memory: Vec<_> = (0..65536).map(|n| (n as u8).wrapping_mul(29)).collect();
            for n in 0..4 {
                memory[4096 + n * 8..4104 + n * 8].copy_from_slice(&(n as u64).to_le_bytes());
            }
            for value in [0, 1, 3, u64::MAX] {
                for pointer in [8192, 67568, u64::MAX] {
                    let mut regs = vec![value; source.register_count()];
                    regs[nirvana::x86::RSP] = 67584;
                    regs[nirvana::x86::RDI] = pointer;
                    inputs.push(regs);
                }
            }
            observations += compare(&source, &inputs, &memory, &[0, 1, 2, 5, 20, 200]);
        }
    }
    assert_eq!(observations, 432);
    println!("{observations} actual GCC full-state MIR/lowered prefix observations");
}

#[test]
fn real_byte_stores_recover_middle_values_at_optimized_load_sites() {
    use crate::support::native;
    let scratch = native::Scratch::new();
    let path = scratch.0.join("byte-constants.c");
    // Volatile keeps the reads in the machine-code input. The comparison uses
    // the closed RAM model, including the retained reads and stack writes.
    std::fs::write(
        &path,
        r#"#include <stdint.h>
uint64_t fixture(uint64_t *state) {
    volatile unsigned char *p = (volatile unsigned char *)state;
    p[0] = 0x11;
    p[1] = 0x22;
    return (uint64_t)p[0] | ((uint64_t)p[1] << 8);
}
"#,
    )
    .unwrap();
    for opt in ["-O0", "-O2", "-O3"] {
        let object = path.with_extension(format!("{opt}.o"));
        native::object(&path, &object, opt, "fixture");
        let low = nirvana::frontend::lift_elf_auto(&std::fs::read(object).unwrap(), "fixture")
            .unwrap()
            .program;
        let middle = Function::from_low(&low).unwrap();
        let (_, evidence) = middle.recover_memory_constants().unwrap();
        if opt != "-O0" {
            assert_eq!((evidence.loads, evidence.proved_loads), (2, 2));
        }
        let inputs: Vec<_> = [8192u64, 69631, u64::MAX]
            .map(|pointer| {
                let mut regs = vec![0; low.register_count()];
                regs[nirvana::x86::RDI] = pointer;
                regs[nirvana::x86::RSP] = 69632;
                regs
            })
            .into();
        assert_eq!(
            compare(&low, &inputs, &[0; 65536], &[0, 1, 2, 4, 8, 32, 128]),
            21
        );
    }
}

#[test]
#[ignore = "requires retained M0 input objects; set NIRVANA_MIDDLE_OBJECTS"]
fn retained_m0_objects_keep_direct_middle_execution_and_exact_low_reconstruction() {
    let directory = std::path::PathBuf::from(
        std::env::var("NIRVANA_MIDDLE_OBJECTS").expect("NIRVANA_MIDDLE_OBJECTS"),
    );
    let mut objects: Vec<_> = std::fs::read_dir(directory)
        .unwrap()
        .map(|e| e.unwrap().path().join("input.o"))
        .filter(|p| p.is_file())
        .collect();
    objects.sort();
    assert_eq!(
        objects.len(),
        16,
        "the frozen four-family GCC/Clang O2/O3 smoke cohort"
    );
    let mut observations = 0;
    let mut source_values = 0;
    let mut canonical_values = 0;
    let mut memory_loads = 0;
    let mut proved_loads = 0;
    for object in objects {
        let source = nirvana::frontend::lift_elf_auto(&std::fs::read(&object).unwrap(), "fixture")
            .unwrap()
            .program;
        let middle = Function::from_low(&source).unwrap();
        source_values += middle.source_value_count();
        canonical_values += middle.value_count();
        let (_, evidence) = middle.recover_memory_constants().unwrap();
        memory_loads += evidence.loads;
        proved_loads += evidence.proved_loads;
        println!(
            "{}: {} loads, {} proved",
            object
                .parent()
                .unwrap()
                .file_name()
                .unwrap()
                .to_string_lossy(),
            evidence.loads,
            evidence.proved_loads
        );
        for seed in 0u64..8 {
            let mut memory: Vec<_> = (0..65536)
                .map(|n| (n as u8).wrapping_mul(29).wrapping_add(7))
                .collect();
            for pointer in [8192u64, 67568] {
                for (index, value) in [
                    seed,
                    if seed == 7 { u64::MAX } else { seed % 4 },
                    seed ^ 9,
                    seed * 17,
                ]
                .into_iter()
                .enumerate()
                {
                    let offset = (pointer - 4096) as usize + index * 8;
                    memory[offset..offset + 8].copy_from_slice(&value.to_le_bytes());
                }
            }
            let inputs: Vec<_> = [8192, 67568, u64::MAX]
                .map(|pointer| {
                    let mut registers = vec![seed.rotate_left(17); source.register_count()];
                    registers[nirvana::x86::RSP] = 67584;
                    registers[nirvana::x86::RDI] = pointer;
                    registers
                })
                .into();
            observations += compare(
                &source,
                &inputs,
                &memory,
                &[0, 1, 2, 4, 8, 16, 32, 64, 128, 256],
            );
        }
    }
    assert_eq!(observations, 3840);
    println!(
        "16 frozen M0 objects; {observations} original/refined MIR/lowered full-state prefix observations; {source_values} source values -> {canonical_values} canonical values; {proved_loads}/{memory_loads} memory loads proved"
    );
}

#[test]
fn gcc_saved_value_fixtures_keep_middle_identity_and_projected_state_at_every_budget() {
    use crate::support::{checked_c, native};
    use nirvana::ir::{AccessKind, RunStatus};
    use std::fmt::Write;
    let scratch = native::Scratch::new();
    let mut observations = 0;
    let mut recovered = 0;
    let mut c_observations = 0;
    for name in [
        "byte-saved-value",
        "phi-saved-value",
        "loop-saved-value",
        "resaved-value",
    ] {
        for opt in ["-O0", "-O2", "-O3"] {
            let object = scratch.0.join(format!("{name}-{opt}.o"));
            native::object(
                &native::fixture_root().join(format!("recovery/{name}.c")),
                &object,
                opt,
                "fixture",
            );
            let low = nirvana::frontend::lift_elf_auto(&std::fs::read(object).unwrap(), "fixture")
                .unwrap()
                .program;
            let middle = Function::from_low(&low).unwrap();
            let saved = middle.recover_saved_values().unwrap();
            recovered += usize::from(saved.is_some());
            if name == "byte-saved-value" && opt != "-O0" {
                assert!(saved.as_ref().unwrap().1.memory.proved_loads >= 2);
            }
            let mut c_input = String::new();
            let mut expected = Vec::new();
            for seed in [0u64, 1, 3, u64::MAX] {
                let mut memory = vec![0xa5; 65536];
                for (n, v) in [seed, seed & 7, 0, seed ^ 9].into_iter().enumerate() {
                    memory[4096 + n * 8..4104 + n * 8].copy_from_slice(&v.to_le_bytes());
                }
                let inputs: Vec<_> = [8192, 69616, u64::MAX]
                    .map(|pointer| {
                        let mut input = vec![seed; low.register_count()];
                        input[nirvana::x86::RDI] = pointer;
                        input[nirvana::x86::RSP] = 69632;
                        input
                    })
                    .into();
                observations +=
                    compare(&low, &inputs, &memory, &[0, 1, 2, 4, 8, 16, 32, 128, 1024]);
                for mut input in inputs {
                    let pointer = input[nirvana::x86::RDI];
                    let words = [seed, seed & 7, 0, seed ^ 9];
                    writeln!(
                        c_input,
                        "{pointer} {} {} {} {}",
                        words[0], words[1], words[2], words[3]
                    )
                    .unwrap();
                    let mut ram: Vec<_> = (0..65536usize).map(|i| (i * 29 + 7) as u8).collect();
                    for (n, value) in words.into_iter().enumerate() {
                        if let Some(offset) = pointer
                            .checked_add(n as u64 * 8)
                            .and_then(|p| p.checked_sub(4096))
                            .filter(|n| *n <= 65528)
                        {
                            ram[offset as usize..offset as usize + 8]
                                .copy_from_slice(&value.to_le_bytes());
                        }
                    }
                    input.fill(0);
                    input[nirvana::x86::RDI] = pointer;
                    input[nirvana::x86::RSP] = 69632;
                    let report = low.run_with_memory(&input, 4096, &ram, 4096).unwrap();
                    let mut row = match report.status {
                        RunStatus::Returned(value) => vec![0, 0, 0, 0, value],
                        RunStatus::Fault(f) => vec![
                            1,
                            f.address,
                            if f.access == AccessKind::Read { 1 } else { 2 },
                            f.width.bytes() as u64,
                            0,
                        ],
                        _ => panic!("bounded native fixture"),
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
            let output = nirvana::readable::emit_middle_c_with_options(
                &middle,
                nirvana::readable::ReadableOptions {
                    stack_register: Some(Reg(nirvana::x86::RSP)),
                    coalesce_locals: true,
                    recover_objects: true,
                    compact_memory: true,
                },
            )
            .unwrap();
            let path = scratch.0.join(format!("{name}-{opt}-middle.c"));
            std::fs::write(
                &path,
                checked_c::source_with_size(&output, low.register_count(), 4, 65536),
            )
            .unwrap();
            for c_opt in ["-O0", "-O2"] {
                let binary = path.with_extension(format!("{c_opt}.bin"));
                native::compile_c(
                    &path,
                    &binary,
                    &[
                        c_opt,
                        "-fsanitize=undefined",
                        "-fno-sanitize-recover=undefined",
                    ],
                );
                assert_eq!(
                    native::run_fields(&binary, &c_input, 8197),
                    expected,
                    "{name}/{opt}/{c_opt}"
                );
                c_observations += expected.len();
            }
        }
    }
    assert_eq!(observations, 1296);
    assert_eq!(c_observations, 288);
    println!(
        "{observations} GCC saved-value full-state prefixes, {recovered}/12 inputs have checked MIR identities, {c_observations} sanitized C full-RAM/fault observations"
    );
}

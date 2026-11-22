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
    for object in objects {
        let source = nirvana::frontend::lift_elf_auto(&std::fs::read(&object).unwrap(), "fixture")
            .unwrap()
            .program;
        let middle = Function::from_low(&source).unwrap();
        source_values += middle.source_value_count();
        canonical_values += middle.value_count();
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
        "16 frozen M0 objects; {observations} direct MIR/lowered full-state prefix observations; {source_values} source values -> {canonical_values} canonical values"
    );
}

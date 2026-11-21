use crate::support::memory_trace;
use crate::support::native;
use nirvana::{module_ir, module_values};
use std::process::Command;

#[test]
fn optimized_algorithm_replays_keep_every_observed_writer_with_stack_aliases() {
    let scratch = native::Scratch::new();
    let driver = scratch.0.join("driver.c");
    std::fs::write(&driver,"#include <stdint.h>\nuint64_t fixture(uint64_t*);\nint main(void){uint64_t state[4]={0};return (int)fixture(state);}\n").unwrap();
    let mut totals = memory_trace::Stats::default();
    let mut optimized = memory_trace::Stats::default();
    for name in ["bfs", "dfs", "ring-queue", "linked-list", "bst-lookup"] {
        for opt in ["-O0", "-O2"] {
            let binary = scratch.0.join(format!("{name}{opt}"));
            native::compile(
                Command::new("cc")
                    .args([opt, "-fno-stack-protector", "-fno-pie", "-no-pie"])
                    .arg(
                        native::fixture_root()
                            .join("algorithms")
                            .join(format!("{name}.c")),
                    )
                    .arg(&driver)
                    .arg("-o")
                    .arg(&binary),
            );
            let module = module_ir::lift_elf(
                &std::fs::read(binary).unwrap(),
                "fixture",
                nirvana::linked_elf::LinkedOptions {
                    load_bias: 0,
                    stack_size: 8192,
                },
            )
            .unwrap();
            let analysis = module_values::analyze(&module.program).unwrap();
            let values = analysis
                .functions
                .iter()
                .find(|f| f.function.name == "fixture")
                .unwrap()
                .result
                .as_ref()
                .unwrap();
            for displacement in [2048, 16, 48, 128] {
                for input in [
                    [0; 4],
                    [u64::MAX, 7, 0x55, 15],
                    [0x0080402010080402, 63, 0x112233, 4],
                ] {
                    let mut registers = module.initial_registers();
                    registers[nirvana::x86::RDI] = registers[nirvana::x86::RSP] - displacement;
                    let mut memory = module.image.memory.clone();
                    let offset = module
                        .image
                        .memory_offset(registers[nirvana::x86::RDI], 32)
                        .unwrap();
                    for (i, word) in input.iter().enumerate() {
                        memory[offset + i * 8..offset + i * 8 + 8]
                            .copy_from_slice(&word.to_le_bytes());
                    }
                    let stats = memory_trace::check(&module, values, registers, memory, 1000);
                    totals.instructions += stats.instructions;
                    totals.read_bytes += stats.read_bytes;
                    totals.written_bytes += stats.written_bytes;
                    if opt == "-O2" {
                        optimized.instructions += stats.instructions;
                        optimized.read_bytes += stats.read_bytes;
                        optimized.written_bytes += stats.written_bytes;
                    }
                }
            }
        }
    }
    assert!(totals.instructions > 1000 && totals.read_bytes > 1000 && totals.written_bytes > 1000);
    eprintln!("120 module entry replays: {totals:?}");
    assert!(optimized.read_bytes > 1000);
    eprintln!("60 O2 entry replays: {optimized:?}");
}

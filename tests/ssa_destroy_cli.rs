#[path = "support/native.rs"]
#[allow(dead_code)]
mod native;
use std::process::Command;

fn compile(command: &mut Command) {
    let result = command.output().unwrap();
    assert!(
        result.status.success(),
        "{command:?}: {}",
        String::from_utf8_lossy(&result.stderr)
    );
}

#[test]
fn native_optimized_machine_code_and_ssa_c_match_for_swaps_diamonds_and_nested_loops() {
    let scratch = native::Scratch::new();
    let root = native::fixture_root();
    let mut inputs = String::new();
    for x in [0, 1, 9, 10, u64::MAX] {
        for y in [0, 7, u64::MAX] {
            for count in [0, 1, 2, 7] {
                inputs.push_str(&format!("{x} {y} {count} 13\n"));
            }
        }
    }
    let mut comparisons = 0;
    for fixture in ["cases/diamond.c", "cases/nested-loops.c", "value-swap.c"] {
        for optimization in ["-O0", "-O2"] {
            let stem = std::path::Path::new(fixture)
                .file_stem()
                .unwrap()
                .to_str()
                .unwrap();
            let id = format!("{stem}{optimization}");
            let object = scratch.0.join(format!("{id}.o"));
            native::object(&root.join(fixture), &object, optimization, "fixture");
            let original = scratch.0.join(format!("{id}-original"));
            compile(
                Command::new("cc")
                    .arg(&object)
                    .arg(root.join("harness.c"))
                    .arg("-o")
                    .arg(&original),
            );
            let expected = native::run(&original, &inputs);
            let emitted = Command::new(env!("CARGO_BIN_EXE_nirvana"))
                .arg(&object)
                .args(["--emit", "ssa-c"])
                .output()
                .unwrap();
            assert!(
                emitted.status.success(),
                "{id}: {}",
                String::from_utf8_lossy(&emitted.stderr)
            );
            let code = String::from_utf8(emitted.stdout).unwrap();
            assert!(code.contains("uint64_t v_"));
            let source = scratch.0.join(format!("{id}.c"));
            std::fs::write(&source, &code).unwrap();
            let bridge = scratch.0.join("bridge.c");
            std::fs::write(&bridge, BRIDGE).unwrap();
            for copt in ["-O0", "-O2"] {
                let binary = scratch.0.join(format!("{id}-generated{copt}"));
                compile(
                    Command::new("cc")
                        .args(["-std=c11", "-Wall", "-Wextra", "-Werror", "-pedantic", copt])
                        .arg(&source)
                        .arg(&bridge)
                        .arg(root.join("harness.c"))
                        .arg("-o")
                        .arg(&binary),
                );
                let actual = native::run(&binary, &inputs);
                assert_eq!(actual, expected, "{id} {copt}");
                comparisons += actual.len();
            }
            if let Ok(directory) = std::env::var("NIRVANA_SSA_ARTIFACTS") {
                let directory = std::path::Path::new(&directory);
                std::fs::create_dir_all(directory).unwrap();
                std::fs::copy(&object, directory.join(format!("{id}.o"))).unwrap();
                std::fs::write(directory.join(format!("{id}.c")), code).unwrap();
                std::fs::write(directory.join(format!("{id}.txt")), emitted.stderr).unwrap();
                std::fs::write(directory.join("inputs.txt"), &inputs).unwrap();
            }
        }
    }
    println!("{comparisons} native C -> object -> SSA C -> native comparisons");
}

const BRIDGE: &str = r#"
#include <stdint.h>
uint64_t nirvana_fn(uint64_t *,uint8_t *,uint64_t,uint64_t);
uint64_t fixture(uint64_t state[4]) {
    uint8_t memory[65536]={0};
    uint64_t registers[32]={0};
    registers[7]=UINT64_C(4096);
    registers[4]=UINT64_C(4096)+sizeof(memory)-16;
    for(unsigned word=0;word<4;++word)
        for(unsigned byte=0;byte<8;++byte)memory[word*8+byte]=(uint8_t)(state[word]>>(byte*8));
    uint64_t result=nirvana_fn(registers,memory,UINT64_C(4096),sizeof(memory));
    for(unsigned word=0;word<4;++word) {
        state[word]=0;
        for(unsigned byte=0;byte<8;++byte)state[word]|=(uint64_t)memory[word*8+byte]<<(byte*8);
    }
    return result;
}
"#;

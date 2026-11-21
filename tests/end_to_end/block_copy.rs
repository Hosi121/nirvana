use crate::support::{
    module_fixture::{self, Case},
    native,
};
use nirvana::{
    linked_elf::LinkedOptions,
    module_ir::{self, Instruction, Limits, RejectImports, Status},
    x86,
};
use std::fmt::Write as _;

fn expected(input: [u64; 4]) -> Vec<u64> {
    let mut value = input[0];
    let mut hash = 0u64;
    let mut first = 0;
    for i in 0..64u64 {
        value = value
            .wrapping_mul(6364136223846793005)
            .wrapping_add(i)
            .wrapping_add(input[1]);
        if i == 0 {
            first = value;
        }
        hash = hash.rotate_left(7) ^ value;
    }
    let edge = first ^ value;
    vec![edge.wrapping_add(hash), input[0], input[1], edge, hash]
}

#[test]
fn ordinary_gcc_struct_assignment_matches_native_ir_and_three_sanitized_c_backends() {
    let scratch = native::Scratch::new();
    let source = native::fixture_root().join("block-copy.c");
    let inputs = [
        [0, 0, 17, 19],
        [1, 3, 17, 19],
        [u64::MAX, 1, 17, 19],
        [1 << 63, u64::MAX, 17, 19],
        [0x123456789abcdef0, 0xfedcba9876543210, 17, 19],
        [u64::MAX, u64::MAX, 17, 19],
    ];
    let expected: Vec<_> = inputs.into_iter().map(expected).collect();
    let mut text = String::new();
    for input in inputs {
        writeln!(text, "{} {} {} {}", input[0], input[1], input[2], input[3]).unwrap();
    }
    let mut compared = 0;
    for opt in ["-O0", "-O2"] {
        for pie in [false, true] {
            let directory = scratch.0.join(format!("{opt}-{pie}"));
            std::fs::create_dir(&directory).unwrap();
            let binary = directory.join("original");
            module_fixture::build("cc", &source, &binary, opt, pie);
            assert_eq!(native::run(&binary, &text), expected);
            let module = module_ir::lift_elf(
                &std::fs::read(&binary).unwrap(),
                "fixture",
                LinkedOptions {
                    load_bias: if pie { 0x4000_0000 } else { 0 },
                    stack_size: 8192,
                },
            )
            .unwrap();
            assert!(
                module.program.instructions().iter().any(|i| matches!(
                    i,
                    Instruction::MoveString {
                        width: nirvana::ir::Width::U64,
                        repeat: true,
                        ..
                    }
                )),
                "compiler output should exercise REP MOVSQ"
            );
            let initial = module.initial_registers();
            let mut rows = Vec::new();
            let mut memories = Vec::new();
            let mut cases = Vec::new();
            for (input, oracle) in inputs.into_iter().zip(&expected) {
                for budget in [0, 1, 2, 8, 64, 512, 4096, 100000] {
                    let case = Case {
                        input,
                        pc: module.program.entry(),
                        budget,
                        patch: None,
                    };
                    let (regs, memory) =
                        module_fixture::prepare_with_state(&module, &case, Some(&initial));
                    assert_eq!(regs[x86::RDI], module_fixture::state_address(&module));
                    let run = module
                        .program
                        .run(
                            &regs,
                            module.image.memory_base,
                            &memory,
                            Limits {
                                instructions: budget,
                                imports: 0,
                            },
                            &mut RejectImports,
                        )
                        .unwrap();
                    let row = module_fixture::expected_with_state(&module, &case, Some(&initial)).0;
                    if budget == 100000 {
                        assert!(
                            matches!(run.status, Status::Returned(_)),
                            "{opt}/{pie}: {:?}",
                            run.status
                        );
                        assert_eq!(&row[..5], oracle);
                    }
                    cases.push(case);
                    rows.push(row);
                    memories.push(run.state.memory);
                }
            }
            compared += module_fixture::check_generated_with_memory(
                &module, &cases, &rows, &memories, &directory, &initial,
            );
        }
    }
    println!(
        "4 GCC struct-copy binaries; {} native/oracle/IR results; {compared} generated C full-state/full-RAM comparisons",
        inputs.len() * 4
    );
}

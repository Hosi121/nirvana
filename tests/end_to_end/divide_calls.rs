use crate::support::{
    module_fixture::{self, Case},
    native,
};
use nirvana::{
    ir::Reg,
    linked_elf::LinkedOptions,
    module_ir::{self, Limits, RejectImports, Status},
    module_values::{self, BoundaryKind, CallContract},
    x86,
};
use std::fmt::Write as _;

#[test]
fn divide_calls_retain_preserved_values_and_full_c_state_on_success_fault_and_de() {
    let scratch = native::Scratch::new();
    let source = native::fixture_root().join("division-call.c");
    let inputs = [
        [0, 1, 17, 19],
        [1, 3, 17, 19],
        [u64::MAX, 3, 17, 19],
        [1 << 63, 10, 17, 19],
        [u64::MAX, u64::MAX, 17, 19],
        [10, 0, 17, 19],
    ];
    let expected: Vec<_> = inputs
        .into_iter()
        .map(|a| {
            if let Some(quotient) = a[0].checked_div(a[1]) {
                let q = quotient ^ (a[0] % a[1]);
                let sum = a[0].wrapping_add(q);
                vec![q ^ sum, a[0], a[1], q, sum]
            } else {
                vec![0, a[0], a[1], a[2], 1]
            }
        })
        .collect();
    let mut text = String::new();
    for a in inputs {
        writeln!(text, "{} {} {} {}", a[0], a[1], a[2], a[3]).unwrap();
    }
    let mut comparisons = 0;
    for opt in ["-O0", "-O2"] {
        let directory = scratch.0.join(opt);
        std::fs::create_dir(&directory).unwrap();
        let binary = directory.join("original");
        module_fixture::build("cc", &source, &binary, opt, false);
        assert_eq!(native::run(&binary, &text), expected);
        let module = module_ir::lift_elf(
            &std::fs::read(&binary).unwrap(),
            "fixture",
            LinkedOptions {
                load_bias: 0,
                stack_size: 4096,
            },
        )
        .unwrap();
        let analysis = module_values::analyze(&module.program).unwrap();
        let helper = module
            .program
            .functions()
            .iter()
            .find(|f| f.name == "divide_pair")
            .unwrap();
        let summary = analysis.call_summaries.at(helper.address).unwrap();
        assert!(summary.closed, "{:?}", summary.reason);
        for register in [x86::RDI, x86::RSI, 8, x86::RSP] {
            assert!(summary.preserved.contains(&Reg(register)));
        }
        let caller = analysis
            .functions
            .iter()
            .find(|f| f.function.address == module.program.entry())
            .unwrap()
            .result
            .as_ref()
            .unwrap();
        let call = caller
            .boundaries()
            .iter()
            .find(|b| matches!(b.kind, BoundaryKind::Call { .. }))
            .unwrap();
        assert_eq!(
            call.call_contract,
            Some(CallContract::Closed {
                callee: helper.address
            })
        );
        assert!(call.inputs.len() < 80 && call.outputs.len() < 80);
        if opt == "-O2" {
            assert!(call.preserved.iter().any(|v| v.register == Reg(8)));
        }
        assert!(caller.memory().unwrap().as_ref().unwrap().definitions().iter().any(|d|matches!(d,nirvana::memory_ssa::Definition::Opaque { effect,.. } if effect.kind==nirvana::memory_ssa::EffectKind::Call)));
        println!(
            "{opt}: DIV helper clobbers {} of 80 register slots; call outputs {}",
            summary.clobbers.len(),
            call.outputs.len()
        );
        let state = module_fixture::state_address(&module);
        let mut initial = module.initial_registers();
        for (i, r) in initial.iter_mut().enumerate() {
            if i != x86::RSP {
                *r = 0x123456789abcdef0u64.wrapping_mul(i as u64 + 1);
            }
        }
        initial[x86::RSI] = 0;
        initial[x86::RDX] = 0;
        initial[x86::RBP] = state + 64;
        initial[8] = state + 80;
        let mut cases = Vec::new();
        for input in inputs {
            for budget in [0, 1, 2, 4, 8, 16, 32, 128, 4096] {
                cases.push(Case {
                    input,
                    pc: module.program.entry(),
                    budget,
                    patch: None,
                });
            }
        }
        for instruction in module.program.instructions() {
            for budget in [0, 1, 2, 64] {
                cases.push(Case {
                    input: [17, 3, 19, 23],
                    pc: instruction.address(),
                    budget,
                    patch: None,
                });
            }
        }
        let mut rows = Vec::new();
        let mut memories = Vec::new();
        let mut errors = 0;
        let mut faults = 0;
        for case in &cases {
            let row = module_fixture::expected_with_state(&module, case, Some(&initial)).0;
            let (regs, memory) = module_fixture::prepare_with_state(&module, case, Some(&initial));
            let report = module
                .program
                .run_from(
                    case.pc,
                    &regs,
                    module.image.memory_base,
                    &memory,
                    Limits {
                        instructions: case.budget,
                        imports: 0,
                    },
                    &mut RejectImports,
                )
                .unwrap();
            errors += usize::from(report.status == Status::DivideError);
            faults += usize::from(matches!(report.status, Status::Fault(_)));
            if case.pc == module.program.entry() && case.budget == 4096 {
                let i = inputs.iter().position(|a| *a == case.input).unwrap();
                assert_eq!(&row[..5], &expected[i]);
            }
            rows.push(row);
            memories.push(report.state.memory);
        }
        assert!(
            errors > 0 && faults > 0,
            "{opt}: #DE={errors}, faults={faults}"
        );
        comparisons += module_fixture::check_generated_with_memory(
            &module, &cases, &rows, &memories, &directory, &initial,
        );
        // Place the real stack frame inside the state object's surrounding
        // RAM. Callee stack Stores may alias data despite preserved registers.
        let mut alias_initial = initial.clone();
        alias_initial[x86::RSP] = state + 64;
        let mut alias_cases = Vec::new();
        let mut alias_rows = Vec::new();
        let mut alias_memory = Vec::new();
        let mut changed = 0;
        for (input, ordinary) in inputs[..3].iter().zip(&expected) {
            for budget in [0, 1, 2, 8, 64, 4096] {
                let case = Case {
                    input: *input,
                    pc: module.program.entry(),
                    budget,
                    patch: Some((state + 64, module_ir::ROOT_RETURN, 8)),
                };
                let (regs, memory) =
                    module_fixture::prepare_with_state(&module, &case, Some(&alias_initial));
                let report = module
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
                let row =
                    module_fixture::expected_with_state(&module, &case, Some(&alias_initial)).0;
                if budget == 4096 {
                    assert!(matches!(report.status, Status::Returned(_)));
                    changed += usize::from(&row[..5] != ordinary);
                }
                alias_cases.push(case);
                alias_rows.push(row);
                alias_memory.push(report.state.memory);
            }
        }
        if opt == "-O0" {
            assert!(
                changed > 0,
                "the callee's stack stores should visibly alias state"
            );
        }
        let alias_directory = directory.join("stack-alias");
        std::fs::create_dir(&alias_directory).unwrap();
        comparisons += module_fixture::check_generated_with_memory(
            &module,
            &alias_cases,
            &alias_rows,
            &alias_memory,
            &alias_directory,
            &alias_initial,
        );
    }
    println!("{comparisons} divide-call generated C full-state/full-RAM comparisons");
}

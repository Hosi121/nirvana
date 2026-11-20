#[path = "support/module_fixture.rs"]
#[allow(dead_code)]
mod module_fixture;
#[path = "support/native.rs"]
#[allow(dead_code)]
mod native;
use module_fixture::{Case, build, check_generated_at_depths, expected, state_address};
use nirvana::ir::Control;
use nirvana::linked_elf::LinkedOptions;
use nirvana::module_ir::{self, Instruction, Module, Status};
use nirvana::{module_outline, module_tail_dispatch as tails};

fn module(scratch: &native::Scratch, pie: bool) -> Module {
    module_variant(scratch, pie, false)
}

fn module_variant(scratch: &native::Scratch, pie: bool, all_reachable: bool) -> Module {
    let source = scratch.0.join("tail.S");
    let binary = scratch.0.join("original");
    let assembly = r#"
.text
.globl fixture
.type fixture,@function
fixture:
    mov (%rdi),%rax
    and $1,%eax
    testq $2,(%rdi)
    jne bridge
    lea table(%rip),%rdx
    notrack jmp *(%rdx,%rax,8)
case0:
    addq $1,8(%rdi)
    .rept 80
    nop
    .endr
    mov 8(%rdi),%rax
    ret
case1:
    addq $2,8(%rdi)
    mov 8(%rdi),%rax
    ret
bridge:
    addq $9,8(%rdi)
    mov 8(%rdi),%rax
    ret
.size fixture,.-fixture
.globl tail_foreign
.type tail_foreign,@function
tail_foreign:
    addq $77,8(%rdi)
    mov 8(%rdi),%rax
    ret
.size tail_foreign,.-tail_foreign
.data
.align 8
table:
    .quad case0,case1
.section .note.GNU-stack,"",@progbits
"#;
    let assembly = if all_reachable {
        assembly.replace(
            "    and $1,%eax",
            "    cmp $2,%rax\n    je case0\n    cmp $3,%rax\n    je case1\n    and $1,%eax",
        )
    } else {
        assembly.to_owned()
    };
    std::fs::write(&source, assembly).unwrap();
    build("cc", &source, &binary, "-O2", pie);
    module_ir::lift_elf(
        &std::fs::read(&binary).unwrap(),
        "fixture",
        LinkedOptions {
            load_bias: if pie { 0x20000 } else { 0 },
            stack_size: 4096,
        },
    )
    .unwrap()
}

#[test]
fn tail_guards_are_checked_against_original_pcs_and_first_reentry_labels() {
    let scratch = native::Scratch::new();
    let m = module(&scratch, false);
    let outline = module_outline::recover(&m.program).unwrap();
    let plan = tails::recover(&m, &outline).unwrap();
    let evidence = tails::validate(&m.program, &outline, &plan).unwrap();
    assert_eq!((evidence.transfers, evidence.cases), (1, 2));
    let (&branch, transfer) = plan.transfers.iter().next().unwrap();
    let (&target, &label) = transfer.cases.iter().next().unwrap();
    let foreign = m
        .program
        .functions()
        .iter()
        .find(|f| f.name == "tail_foreign")
        .unwrap()
        .address;
    let mut invalid = plan.clone();
    invalid
        .transfers
        .get_mut(&branch)
        .unwrap()
        .cases
        .insert(target, label + 1);
    assert!(tails::validate(&m.program, &outline, &invalid).is_err());
    for bad in [target + 1, foreign, 0] {
        let mut invalid = plan.clone();
        let t = invalid.transfers.get_mut(&branch).unwrap();
        t.cases.clear();
        t.cases.insert(bad, label);
        assert!(tails::validate(&m.program, &outline, &invalid).is_err());
    }
    let mut invalid = plan.clone();
    invalid.transfers.get_mut(&branch).unwrap().function = foreign;
    assert!(tails::validate(&m.program, &outline, &invalid).is_err());
    let mut invalid = plan.clone();
    let transfer = invalid.transfers.remove(&branch).unwrap();
    invalid.transfers.insert(m.program.entry(), transfer);
    assert!(tails::validate(&m.program, &outline, &invalid).is_err());
    let mut invalid = plan.clone();
    invalid.transfers.get_mut(&branch).unwrap().cases.clear();
    assert!(tails::validate(&m.program, &outline, &invalid).is_err());
    let mut bad_outline = outline.clone();
    let f = bad_outline
        .functions
        .iter_mut()
        .find(|f| f.function.address == m.program.entry())
        .unwrap();
    f.resumes.insert(target, label + 1);
    assert!(tails::validate(&m.program, &bad_outline, &plan).is_err());

    // Advisory metadata may be stale or forged. Only safe decoded PCs can be
    // selected; mutable table bytes are still evaluated at execution time.
    let mut hints = m.clone();
    hints.jump_tables[0].entries[0].target = foreign;
    let filtered = tails::recover(&hints, &outline).unwrap();
    assert!(
        filtered
            .transfers
            .values()
            .all(|t| !t.cases.contains_key(&foreign))
    );
    let mut hints = m.clone();
    let table = &mut hints.jump_tables[0];
    for i in m
        .program
        .instructions()
        .iter()
        .filter(|i| (m.program.entry()..m.program.entry() + 200).contains(&i.address()))
    {
        table.entries.push(nirvana::jump_tables::Entry {
            address: table.table,
            target: i.address(),
        });
    }
    let capped = tails::recover(&hints, &outline).unwrap();
    assert_eq!(
        capped.transfers[&branch].cases.len(),
        tails::MAX_CASES_PER_TRANSFER
    );
    let mut invalid = capped.clone();
    invalid
        .transfers
        .get_mut(&branch)
        .unwrap()
        .cases
        .insert(foreign, 0);
    assert!(tails::validate(&m.program, &outline, &invalid).is_err());
    let mut hints = m.clone();
    hints.jump_tables = vec![hints.jump_tables[0].clone(); 8193];
    assert!(
        tails::recover(&hints, &outline)
            .unwrap()
            .transfers
            .is_empty()
    );
}

#[test]
fn guarded_and_residual_tail_paths_match_full_state_at_host_depth_boundaries() {
    for pie in [false, true] {
        let scratch = native::Scratch::new();
        let mut m = module(&scratch, pie);
        let start = m.program.entry();
        let root = m
            .program
            .functions()
            .iter()
            .find(|f| f.address == start)
            .unwrap();
        let end = start + root.size;
        let bridge = m
            .program
            .instructions()
            .iter()
            .find_map(|i| match i {
                Instruction::Core(i) if (start..end).contains(&i.address) => {
                    if let Control::Branch { target, .. } = i.control {
                        Some(target)
                    } else {
                        None
                    }
                }
                _ => None,
            })
            .unwrap();
        let foreign = m
            .program
            .functions()
            .iter()
            .find(|f| f.name == "tail_foreign")
            .unwrap()
            .address;
        let table = &m.jump_tables[0];
        let (slot, case0, case1, branch) = (
            table.entries[0].address,
            table.entries[0].target,
            table.entries[1].target,
            table.branch,
        );
        assert!(!table.targets().contains(&bridge));
        let mut cases = Vec::new();
        for input in [
            [0, 17, 23, 0],
            [1, 17, 23, 0],
            [2, 17, 23, 0],
            [3, u64::MAX, 0, 0],
        ] {
            let case = Case {
                input,
                pc: start,
                budget: 1000,
                patch: None,
            };
            let (row, status) = expected(&m, &case);
            assert!(matches!(status, Status::Returned(_)));
            let want = input[1].wrapping_add(if input[0] & 2 != 0 {
                9
            } else {
                (input[0] & 1) + 1
            });
            assert_eq!(row[0], want);
            assert_eq!(row[2], want);
            cases.push(case);
        }
        for budget in 0..100 {
            cases.push(Case {
                input: [0, 17, 23, 0],
                pc: start,
                budget,
                patch: None,
            });
        }
        for instruction in m
            .program
            .instructions()
            .iter()
            .filter(|i| (start..end).contains(&i.address()))
        {
            cases.push(Case {
                input: [0, 17, 23, 0],
                pc: instruction.address(),
                budget: 4,
                patch: None,
            });
        }
        for target in [
            case0,
            case1,
            bridge,
            foreign,
            start,
            state_address(&m),
            case0 + 1,
            0,
        ] {
            let case = Case {
                input: [0, 17, 23, 0],
                pc: start,
                budget: 250,
                patch: Some((slot, target, 8)),
            };
            let (row, status) = expected(&m, &case);
            if [case0, case1, bridge, foreign].contains(&target) {
                assert!(matches!(status, Status::Returned(_)));
            }
            if target == bridge {
                assert_eq!(row[2], 26);
            }
            if target == foreign {
                assert_eq!(row[2], 94);
            }
            if [state_address(&m), case0 + 1, 0].contains(&target) {
                assert!(matches!(status,Status::UnknownTarget(pc) if pc==target));
            }
            if target == start {
                assert!(matches!(
                    status,
                    Status::Suspended(module_ir::Limit::Instructions)
                ));
            }
            cases.push(case);
        }
        // A valid extra hint can turn an actual internal cycle into a local
        // branch. Its meaning is still determined by the guest table bytes.
        m.jump_tables[0].entries.push(nirvana::jump_tables::Entry {
            address: slot + 16,
            target: start,
        });
        let readable = nirvana::module_readable::emit_c(&m).unwrap();
        let locals = nirvana::module_readable::emit_c_with_locals(&m).unwrap();
        for output in [&readable, &locals] {
            assert_eq!(output.report.guarded_tail_transfers, 1);
            assert_eq!(output.report.guarded_tail_cases, 3);
            assert!(output.code.contains("switch (nv_target)"));
        }
        let rows: Vec<_> = cases.iter().map(|c| expected(&m, c).0).collect();
        let count = check_generated_at_depths(&m, &cases, &rows, &scratch.0, true, &[1, 2, 64]);
        println!(
            "guarded tails PIE={pie}:{} state inputs, {count} generated depth/optimization comparisons",
            cases.len()
        );
        // Removing all hints only changes the chosen fast paths.
        m.jump_tables.clear();
        assert_eq!(
            nirvana::module_readable::emit_c(&m)
                .unwrap()
                .report
                .guarded_tail_transfers,
            0
        );
        let directory = scratch.0.join("no-hints");
        std::fs::create_dir(&directory).unwrap();
        check_generated_at_depths(&m, &cases, &rows, &directory, true, &[1]);
        assert!(cases.iter().any(|c| c.pc == branch));
    }
}

#[test]
fn recovered_local_bindings_retain_the_original_dispatch_path() {
    let scratch = native::Scratch::new();
    let m = module_variant(&scratch, false, true);
    let values = nirvana::module_values::analyze(&m.program).unwrap();
    let locals = nirvana::module_local_plan::recover(&m.program, &values).unwrap();
    let function = locals
        .functions
        .iter()
        .find(|f| f.address == m.program.entry())
        .unwrap();
    assert!(function.result.is_ok(), "{:?}", function.result);
    assert_eq!(
        nirvana::module_readable::emit_c(&m)
            .unwrap()
            .report
            .guarded_tail_transfers,
        1
    );
    assert_eq!(
        nirvana::module_readable::emit_c_with_locals(&m)
            .unwrap()
            .report
            .guarded_tail_transfers,
        0
    );
    let mut cases = Vec::new();
    for key in 0..5 {
        for budget in [4, 7, 90, 200] {
            cases.push(Case {
                input: [key, 17, 23, 0],
                pc: m.program.entry(),
                budget,
                patch: None,
            });
        }
    }
    let rows: Vec<_> = cases.iter().map(|c| expected(&m, c).0).collect();
    check_generated_at_depths(&m, &cases, &rows, &scratch.0, true, &[1, 2, 64]);
}

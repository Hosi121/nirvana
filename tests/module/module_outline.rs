//! Outline plans preserve all source steps, including arbitrary resume sites.
use crate::support::native;

use nirvana::ir::{Assignment, Control, Expr, IrInstruction, Program, Reg};
use nirvana::linked_elf::LinkedOptions;
use nirvana::module_ir::{self, Instruction, Module};
use nirvana::module_outline::{self, Plan};
use nirvana::structure::{Node, StructuredFunction};
use nirvana::structure_verify::{self, ValidationError};
use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;
use std::process::Command;

fn module(scratch: &native::Scratch, assembly: &str) -> Module {
    let source = scratch.0.join("module.S");
    let executable = scratch.0.join("original");
    std::fs::write(
        &source,
        format!("{assembly}\n.section .note.GNU-stack,\"\",@progbits\n"),
    )
    .unwrap();
    let output = native::compile_output(
        Command::new("cc")
            .args(["-no-pie", "-Wl,--build-id=none"])
            .arg(&source)
            .arg("-o")
            .arg(&executable),
    );
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    lift(&executable, false)
}

fn lift(path: &Path, pie: bool) -> Module {
    module_ir::lift_elf(
        &std::fs::read(path).unwrap(),
        "main",
        LinkedOptions {
            load_bias: if pie { 0x200000 } else { 0 },
            ..Default::default()
        },
    )
    .unwrap()
}

fn check_plan(module: &Module, plan: &Plan) {
    assert_eq!(plan.functions.len(), module.program.functions().len());
    assert_eq!(plan.imports.len(), module.program.imports().len());
    let mut all_addresses = BTreeSet::new();
    let mut names = BTreeSet::new();
    for (original, function) in module.program.functions().iter().zip(&plan.functions) {
        assert_eq!(original, &function.function);
        assert!(function.c_name.starts_with("nv_fn_"));
        assert!(names.insert(function.c_name.clone()));
        let source: BTreeMap<_, _> = module
            .program
            .instructions()
            .iter()
            .filter(|i| (original.address..original.address + original.size).contains(&i.address()))
            .map(|i| (i.address(), i))
            .collect();
        assert_eq!(source.len(), function.shape.instructions().len());
        for instruction in function.shape.instructions() {
            assert!(all_addresses.insert(instruction.address));
            match source[&instruction.address] {
                Instruction::Core(original) => assert_eq!(instruction, original),
                Instruction::Divide { size, .. } | Instruction::StoreString { size, .. } => {
                    assert_eq!(instruction.size, *size);
                    assert!(instruction.assignments.is_empty());
                    assert_eq!(instruction.control, Control::Next);
                }
                Instruction::Vector(original) => {
                    assert_eq!(instruction.size, original.size);
                    assert_eq!(instruction.assignments, original.assignments);
                    assert_eq!(instruction.control, Control::Next);
                }
                Instruction::Transfer { link, size, .. } => {
                    assert_eq!(instruction.size, *size);
                    assert!(instruction.assignments.is_empty());
                    assert_eq!(
                        instruction.control,
                        if link.is_some() {
                            Control::Next
                        } else {
                            Control::Return(Expr::Const(0))
                        }
                    );
                }
                Instruction::Return { size, .. } => {
                    assert_eq!(instruction.size, *size);
                    assert!(instruction.assignments.is_empty());
                    assert_eq!(instruction.control, Control::Return(Expr::Const(0)));
                }
            }
        }
        assert!(function.sites.len() <= 2 * source.len());
        let mut first = BTreeMap::new();
        for (ordinal, site) in function.sites.iter().enumerate() {
            assert_eq!(site.label, ordinal);
            assert!(source.contains_key(&site.address));
            first.entry(site.address).or_insert(site.label);
        }
        assert_eq!(first, function.resumes);
        assert_eq!(
            first.keys().copied().collect::<BTreeSet<_>>(),
            source.keys().copied().collect()
        );
        if let Some(structured) = &function.structured {
            assert!(function.fallback_reason.is_none());
            let evidence =
                structure_verify::validate_reentries(&function.shape, structured.body()).unwrap();
            assert_eq!(function.reentry_evidence, Some(evidence));
            assert_eq!(evidence.original_steps, source.len());
            assert_eq!(evidence.compared_copies, function.sites.len());
            assert!(nirvana::loop_labels::LoopLabels::analyze(structured.body()).is_some());
        } else {
            assert!(function.reentry_evidence.is_none());
            assert!(
                function
                    .fallback_reason
                    .as_ref()
                    .is_some_and(|s| !s.is_empty())
            );
            assert_eq!(
                function.sites.iter().map(|s| s.address).collect::<Vec<_>>(),
                source.keys().copied().collect::<Vec<_>>()
            );
        }
    }
    assert_eq!(all_addresses.len(), module.program.instructions().len());
    for (original, import) in module.program.imports().iter().zip(&plan.imports) {
        assert_eq!(original, &import.import);
        assert!(import.c_name.starts_with("nv_import_"));
        assert!(names.insert(import.c_name.clone()));
    }
    for name in names {
        assert!(name.len() <= module_outline::MAX_C_NAME_LENGTH);
        assert!(name.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'_'));
    }
}

#[test]
fn source_effects_calls_vectors_imports_names_and_split_provenance_are_preserved() {
    let scratch = native::Scratch::new();
    let module = module(
        &scratch,
        r#"
.text
.globl main
.type main,@function
main:
    pxor %xmm0,%xmm0
    call callee
    call puts@PLT
    ret
.size main,.-main
.type callee,@function
callee:
    test %edi,%edi
    jz .Lalt
    mov $1,%eax
    ret
.Lalt:
    mov $2,%eax
    ret
.size callee,.-callee
.type tail,@function
tail:
    jmp callee
.size tail,.-tail
.type irreducible,@function
irreducible:
    test %edi,%edi
    jz .Ltwo
.Lone:
    sub $1,%edi
.Ltwo:
    cmp $2,%edi
    jb .Lone
    ret
.size irreducible,.-irreducible
.type retry,@function
retry:
    endbr64
    push %rbp
    mov %rsp,%rbp
    mov %edi,-4(%rbp)
    cmpl $96,-4(%rbp)
    jbe .Lretry_upper
    cmpl $122,-4(%rbp)
    jbe .Lretry_yes
.Lretry_upper:
    cmpl $64,-4(%rbp)
    jbe .Lretry_digit
    cmpl $90,-4(%rbp)
    jbe .Lretry_yes
.Lretry_digit:
    cmpl $47,-4(%rbp)
    jbe .Lretry_dash
    cmpl $57,-4(%rbp)
    jbe .Lretry_yes
.Lretry_dash:
    cmpl $45,-4(%rbp)
    jne .Lretry_no
.Lretry_yes:
    mov $1,%eax
    jmp .Lretry_done
.Lretry_no:
    mov $0,%eax
.Lretry_done:
    pop %rbp
    ret
.size retry,.-retry
.type growth,@function
growth:
    endbr64
    push %rbp
    mov %rsp,%rbp
    mov %edi,-4(%rbp)
    cmpl $96,-4(%rbp)
    jbe .Lgrowth_upper
    cmpl $122,-4(%rbp)
    jbe .Lgrowth_yes
.Lgrowth_upper:
    cmpl $64,-4(%rbp)
    jbe .Lgrowth_digit
    cmpl $90,-4(%rbp)
    jbe .Lgrowth_yes
.Lgrowth_digit:
    cmpl $47,-4(%rbp)
    jbe .Lgrowth_dash
    cmpl $57,-4(%rbp)
    jbe .Lgrowth_yes
.Lgrowth_dash:
    cmpl $45,-4(%rbp)
    jne .Lgrowth_no
.Lgrowth_yes:
    .rept 64
    nop
    .endr
    mov $1,%eax
    jmp .Lgrowth_done
.Lgrowth_no:
    mov $0,%eax
.Lgrowth_done:
    pop %rbp
    ret
.size growth,.-growth
.type "bad*/name",@function
"bad*/name":
    ret
.size "bad*/name",.-"bad*/name"
"#,
    );
    let before = module.program.instructions().to_vec();
    let plan = module_outline::recover(&module.program).unwrap();
    check_plan(&module, &plan);
    assert_eq!(module.program.instructions(), before);
    assert!(
        plan.functions
            .iter()
            .any(|f| f.function.name == "bad*/name")
    );
    let split = plan
        .functions
        .iter()
        .find(|f| f.function.name == "irreducible")
        .unwrap();
    assert!(
        split
            .structured
            .as_ref()
            .unwrap()
            .split_evidence()
            .is_some()
    );
    assert!(split.fallback_reason.is_none());
    assert!(
        plan.functions
            .iter()
            .find(|f| f.function.name == "main")
            .unwrap()
            .structured
            .is_some()
    );
    assert!(plan.imports.iter().any(|i| i.import.name == "puts"));
    let retry = plan
        .functions
        .iter()
        .find(|f| f.function.name == "retry")
        .unwrap();
    assert!(matches!(
        StructuredFunction::recover(&retry.shape),
        Err(nirvana::structure::StructureError::CopyLimit { limit: 2, .. })
    ));
    assert!(retry.structured.is_some());
    assert!(retry.sites.len() > retry.resumes.len());
    let growth = plan
        .functions
        .iter()
        .find(|f| f.function.name == "growth")
        .unwrap();
    assert!(growth.structured.is_none());
    assert!(
        growth
            .fallback_reason
            .as_deref()
            .unwrap()
            .contains("total copy budget")
    );
    assert_eq!(growth.sites.len(), growth.shape.instructions().len());
}

fn i(address: u64, assignments: Vec<Assignment>, control: Control) -> IrInstruction {
    IrInstruction {
        address,
        size: 1,
        assignments,
        control,
    }
}
fn step(address: u64) -> Node {
    Node::Step {
        address,
        assignments: vec![],
    }
}
use crate::support::ir::c;

#[test]
fn all_syntactic_copies_are_checked_even_after_an_unconditional_return() {
    let source = Program::new(0, 1, vec![i(0, vec![], Control::Return(c(7)))]).unwrap();
    let correct = vec![step(0), Node::Return(c(7)), step(0), Node::Return(c(7))];
    assert_eq!(
        structure_verify::validate(&source, &correct)
            .unwrap()
            .compared_copies,
        1
    );
    assert_eq!(
        structure_verify::validate_reentries(&source, &correct)
            .unwrap()
            .compared_copies,
        2
    );
    let mutants = [
        vec![step(0), Node::Return(c(7)), step(0), Node::Return(c(8))],
        vec![
            step(0),
            Node::Return(c(7)),
            Node::Step {
                address: 0,
                assignments: vec![Assignment {
                    destination: Reg(0).into(),
                    value: c(1),
                }],
            },
            Node::Return(c(7)),
        ],
        vec![step(0), Node::Return(c(7)), step(99), Node::Return(c(7))],
        vec![step(0), Node::Return(c(7)), step(0)],
    ];
    for mutant in mutants {
        assert!(structure_verify::validate(&source, &mutant).is_ok());
        assert!(structure_verify::validate_reentries(&source, &mutant).is_err());
    }
}

#[test]
fn copied_next_step_and_branch_condition_must_match_source_exactly() {
    let source = Program::new(
        0,
        1,
        vec![
            i(0, vec![], Control::Next),
            i(1, vec![], Control::Return(c(7))),
        ],
    )
    .unwrap();
    let body = vec![
        step(0),
        step(1),
        Node::Return(c(7)),
        step(0),
        step(0),
        step(1),
        Node::Return(c(7)),
    ];
    assert!(structure_verify::validate(&source, &body).is_ok());
    assert!(matches!(
        structure_verify::validate_reentries(&source, &body),
        Err(ValidationError::Address { .. })
    ));
    let source = Program::new(
        0,
        1,
        vec![
            i(
                0,
                vec![],
                Control::Branch {
                    condition: Expr::Register(Reg(0)),
                    target: 2,
                },
            ),
            i(1, vec![], Control::Return(c(7))),
            i(2, vec![], Control::Return(c(9))),
        ],
    )
    .unwrap();
    let mut body = StructuredFunction::recover(&source)
        .unwrap()
        .body()
        .to_vec();
    body.extend([
        step(0),
        Node::If {
            condition: c(1),
            taken: vec![step(2), Node::Return(c(9))],
            not_taken: vec![step(1), Node::Return(c(7))],
        },
    ]);
    assert!(structure_verify::validate(&source, &body).is_ok());
    assert!(matches!(
        structure_verify::validate_reentries(&source, &body),
        Err(ValidationError::Control { .. })
    ));
}

#[test]
fn reentry_coverage_includes_unreachable_source_instructions() {
    let source = Program::new(
        0,
        0,
        vec![
            i(0, vec![], Control::Return(c(7))),
            i(1, vec![], Control::Return(c(9))),
        ],
    )
    .unwrap();
    let mut body = vec![step(0), Node::Return(c(7))];
    assert!(structure_verify::validate(&source, &body).is_ok());
    assert_eq!(
        structure_verify::validate_reentries(&source, &body),
        Err(ValidationError::MissingInstruction(1))
    );
    body.extend([step(1), Node::Return(c(9))]);
    let evidence = structure_verify::validate_reentries(&source, &body).unwrap();
    assert_eq!(evidence.original_steps, 2);
    assert_eq!(evidence.compared_copies, 2);
}

#[test]
fn reentry_proof_is_bounded_for_syntax_and_expressions() {
    let source = Program::new(0, 0, vec![i(0, vec![], Control::Return(c(7)))]).unwrap();
    let mut expression = c(0);
    for _ in 0..257 {
        expression = Expr::load(expression, nirvana::ir::Width::U8);
    }
    assert_eq!(
        structure_verify::validate_reentries(&source, &[step(0), Node::Return(expression)]),
        Err(ValidationError::ResourceLimit)
    );
    let mut deep = vec![step(0)];
    for _ in 0..257 {
        deep = vec![Node::Loop(deep)];
    }
    assert_eq!(
        structure_verify::validate_reentries(&source, &deep),
        Err(ValidationError::ResourceLimit)
    );
    let oversized = vec![step(0); 100_000];
    assert_eq!(
        structure_verify::validate_reentries(&source, &oversized),
        Err(ValidationError::ResourceLimit)
    );
    let assignments = vec![
        Assignment {
            destination: Reg(0).into(),
            value: c(0)
        };
        100_001
    ];
    assert_eq!(
        structure_verify::validate_reentries(
            &source,
            &[
                Node::Step {
                    address: 0,
                    assignments
                },
                Node::Return(c(7)),
            ]
        ),
        Err(ValidationError::ResourceLimit)
    );
}

#[test]
fn structuring_global_step_budget_refuses_before_growing_the_body() {
    let source = Program::new(
        0,
        0,
        vec![
            i(0, vec![], Control::Next),
            i(1, vec![], Control::Return(c(0))),
        ],
    )
    .unwrap();
    for limit in [0, 1] {
        assert!(
            matches!(StructuredFunction::recover_with_step_limit(&source, 32, limit),
            Err(nirvana::structure::StructureError::StepLimit { limit: actual }) if actual == limit)
        );
    }
    let legacy = StructuredFunction::recover_with_copy_limit(&source, 2).unwrap();
    let bounded = StructuredFunction::recover_with_step_limit(&source, 2, 2).unwrap();
    assert_eq!(bounded.body(), legacy.body());
    assert_eq!(bounded.evidence(), legacy.evidence());
    structure_verify::validate_reentries(&source, bounded.body()).unwrap();
}

#[test]
fn reentry_proof_distinguishes_real_infinite_loops_from_silent_routing_cycles() {
    let source = Program::new(0, 0, vec![i(0, vec![], Control::Jump(0))]).unwrap();
    assert!(structure_verify::validate_reentries(&source, &[Node::Loop(vec![step(0)])]).is_ok());
    assert!(matches!(
        structure_verify::validate_reentries(&source, &[step(0), Node::Loop(vec![])]),
        Err(ValidationError::SilentCycle { .. })
    ));
}

#[test]
fn whole_http_server_modules_have_checked_function_bodies() {
    let scratch = native::Scratch::new();
    let fixtures = native::fixture_root().join("http-server");
    for id in ["exec-O0", "exec-O2", "pie-O0", "pie-O2"] {
        let pie = id.starts_with("pie");
        let binary = scratch.0.join(id);
        let mut cc = Command::new("cc");
        cc.args([
            "-std=c11",
            "-Wall",
            "-Wextra",
            "-Werror",
            "-pedantic",
            "-fno-lto",
            "-fno-stack-protector",
        ])
        .arg(if id.ends_with("O0") { "-O0" } else { "-O2" })
        .args(if pie {
            ["-fPIE", "-pie"]
        } else {
            ["-fno-pie", "-no-pie"]
        });
        for name in [
            "main.c",
            "parser.c",
            "response.c",
            "routes.c",
            "routes_table.c",
            "transport.c",
        ] {
            cc.arg(fixtures.join(name));
        }
        let output = native::compile_output(cc.arg("-o").arg(&binary));
        assert!(
            output.status.success(),
            "{cc:?}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        let module = lift(&binary, pie);
        let plan = module_outline::recover(&module.program).unwrap();
        check_plan(&module, &plan);
        let structured = plan
            .functions
            .iter()
            .filter(|f| f.structured.is_some())
            .count();
        println!(
            "{id}: functions={} structured={structured} goto={} instructions={} copies={}",
            plan.functions.len(),
            plan.functions.len() - structured,
            module.program.instructions().len(),
            plan.functions.iter().map(|f| f.sites.len()).sum::<usize>()
        );
        for function in &plan.functions {
            if let Some(reason) = &function.fallback_reason {
                println!("  fallback {}: {reason}", function.function.name);
            }
            if function.sites.len() > function.resumes.len() {
                println!(
                    "  duplicated {}: {} sites / {} originals",
                    function.function.name,
                    function.sites.len(),
                    function.resumes.len()
                );
            }
        }
        assert!(structured > 0);
    }
}

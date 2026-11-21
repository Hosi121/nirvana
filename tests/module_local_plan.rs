#[path = "support/native.rs"]
#[allow(dead_code)]
mod native;

use std::collections::BTreeSet;
use std::process::Command;

use nirvana::ir::{self, Assignment, Control, Expr, IrInstruction, Place, Reg};
use nirvana::module_ir::{self, Instruction};
use nirvana::module_local_plan::{self, Locals, Plan};
use nirvana::module_values::{self, PointRole};

fn fixture(body: &str) -> (module_ir::Module, module_values::Analysis, Plan) {
    let scratch = native::Scratch::new();
    let source = scratch.0.join("plan.S");
    let binary = scratch.0.join("plan");
    std::fs::write(
        &source,
        format!(".text\n{body}\n.section .note.GNU-stack,\"\",@progbits\n"),
    )
    .unwrap();
    let output = Command::new("cc")
        .arg("-no-pie")
        .arg(&source)
        .arg("-o")
        .arg(&binary)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let module = module_ir::lift_elf(
        &std::fs::read(binary).unwrap(),
        "main",
        nirvana::linked_elf::LinkedOptions {
            load_bias: 0,
            ..Default::default()
        },
    )
    .unwrap();
    let values = module_values::analyze(&module.program).unwrap();
    let original_source = module.program.instructions().to_vec();
    let original_values = format!("{values:?}");
    let plan = module_local_plan::recover(&module.program, &values).unwrap();
    assert_eq!(original_source, module.program.instructions());
    assert_eq!(original_values, format!("{values:?}"));
    for function in &plan.functions {
        if let Ok(local) = &function.result {
            assert_eq!(
                local
                    .used_locals
                    .iter()
                    .copied()
                    .filter(|&id| id < local.local_count)
                    .collect::<Vec<_>>(),
                (0..local.local_count).collect::<Vec<_>>()
            );
        }
    }
    (module, values, plan)
}

fn function<'a>(module: &module_ir::Module, plan: &'a Plan, name: &str) -> &'a Locals {
    let address = module
        .program
        .functions()
        .iter()
        .find(|f| f.name == name)
        .unwrap()
        .address;
    plan.functions
        .iter()
        .find(|f| f.address == address)
        .unwrap()
        .result
        .as_ref()
        .unwrap()
}

fn run_assignment_step(
    address: u64,
    source: &[Assignment],
    state: &[u64],
    memory: &[u8],
) -> ir::RunReport {
    let program = ir::Program::new(
        address,
        state.len(),
        vec![IrInstruction {
            address,
            size: 1,
            assignments: source.to_vec(),
            control: Control::Return(Expr::Const(0)),
        }],
    )
    .unwrap();
    program.run_with_memory(state, 0x1000, memory, 1).unwrap()
}

fn canonical_mirrors(source: &[Assignment], planned: &[Assignment]) {
    let writes = |assignments: &[Assignment]| {
        assignments
            .iter()
            .filter_map(|a| match a.destination {
                Place::Register(r) if r.0 < 80 => Some(r),
                _ => None,
            })
            .collect::<Vec<_>>()
    };
    assert_eq!(writes(source), writes(planned));
    assert_eq!(
        source
            .iter()
            .filter(|a| matches!(a.destination, Place::Memory { .. }))
            .count(),
        planned
            .iter()
            .filter(|a| matches!(a.destination, Place::Memory { .. }))
            .count()
    );
    for (index, assignment) in planned.iter().enumerate() {
        if let Place::Register(local) = assignment.destination
            && local.0 >= 80
        {
            let mirror = &planned[index + 1];
            assert!(matches!(mirror.destination, Place::Register(r) if r.0 < 80));
            assert_eq!(mirror.value, Expr::Register(local));
            assert_ne!(assignment.value, Expr::Register(local));
        }
    }
}

#[test]
fn resumes_seed_original_instruction_live_values_and_assignment_mirrors_are_immediate() {
    let (module, values, plan) = fixture(
        r#"
.globl main
.type main,@function
main:
    mov %rdi,%rax
    nop
    add $7,%rax
    mov %rax,(%rsi)
    ret
.size main,.-main
"#,
    );
    let local = function(&module, &plan, "main");
    let source: Vec<_> = module
        .program
        .instructions()
        .iter()
        .filter(|i| local.steps.contains_key(&i.address()))
        .collect();
    assert_eq!(local.steps.len(), 5);
    let nop = &local.steps[&source[1].address()];
    assert!(nop.assignments.is_empty());
    assert!(
        nop.resume
            .iter()
            .any(|b| b.register == Reg(nirvana::x86::RAX))
    );
    let graph = values
        .functions
        .iter()
        .find(|f| f.function.name == "main")
        .unwrap()
        .result
        .as_ref()
        .unwrap();
    let expected: usize = graph
        .roles()
        .values()
        .filter(|r| matches!(r, PointRole::Assignment { .. }))
        .count();
    assert!(expected > 0);
    for instruction in source {
        let step = &local.steps[&instruction.address()];
        if let Instruction::Core(core) = instruction {
            canonical_mirrors(&core.assignments, &step.assignments);
            // Arbitrary-PC execution starts from fresh canonical state; local
            // garbage must be irrelevant after this instruction's resume map.
            for seed in 0..5 {
                let mut raw: Vec<_> = (0..80).map(|n| (n * 131 + seed) as u64).collect();
                raw[nirvana::x86::RSI] = if seed == 4 {
                    0x0fff
                } else {
                    0x1000 + seed as u64
                };
                let memory = vec![0x5a; 32];
                let baseline = run_assignment_step(core.address, &core.assignments, &raw, &memory);
                let mut named = raw.clone();
                named.resize(80 + local.local_count + 2, 0xdead_beef);
                for b in &step.resume {
                    named[80 + b.local] = raw[b.register.0];
                }
                let mut actual =
                    run_assignment_step(core.address, &step.assignments, &named, &memory);
                actual.state.registers.truncate(80);
                assert_eq!(baseline, actual);
            }
        } else {
            assert!(step.assignments.is_empty());
        }
    }
}

#[test]
fn successful_calls_reload_preserved_and_clobbered_values_without_executing_events() {
    let (module, values, plan) = fixture(
        r#"
.globl main
.type main,@function
main:
    mov %rdi,%rbx
    call leaf
    add %rbx,%rax
    ret
.size main,.-main
.type leaf,@function
leaf:
    mov $13,%rax
    ret
.size leaf,.-leaf
"#,
    );
    let local = function(&module, &plan, "main");
    let call = module
        .program
        .instructions()
        .iter()
        .find(|i| {
            matches!(i, Instruction::Transfer { link: Some(_), .. })
                && local.steps.contains_key(&i.address())
        })
        .unwrap();
    let step = &local.steps[&call.address()];
    assert!(step.assignments.is_empty());
    let reloaded: BTreeSet<_> = step
        .after
        .iter()
        .filter_map(|a| match &a.value {
            Expr::Register(r) if r.0 < 80 => Some(r.0),
            _ => None,
        })
        .collect();
    assert!(reloaded.contains(&nirvana::x86::RAX));
    assert!(reloaded.contains(&nirvana::x86::RBX));
    assert!(!step.after.iter().any(|a| matches!(a.value, Expr::Const(_))));
    let analysis = values
        .functions
        .iter()
        .find(|f| f.function.name == "main")
        .unwrap()
        .result
        .as_ref()
        .unwrap();
    assert!(
        analysis
            .boundaries()
            .iter()
            .find(|b| b.address == call.address())
            .unwrap()
            .preserved
            .iter()
            .any(|v| v.register == Reg(nirvana::x86::RBX))
    );
    for instruction in module
        .program
        .instructions()
        .iter()
        .filter(|i| local.steps.contains_key(&i.address()))
    {
        if matches!(instruction, Instruction::Return { .. }) {
            assert!(local.steps[&instruction.address()].assignments.is_empty());
            assert!(local.steps[&instruction.address()].after.is_empty());
        }
    }
}

#[test]
fn observation_only_values_and_dead_phi_webs_do_not_declare_locals() {
    let (module, _, plan) = fixture(
        r#"
.globl main
.type main,@function
main:
    call empty
    ret
.size main,.-main
.type empty,@function
empty:
    nop
    ret
.size empty,.-empty
"#,
    );
    for name in ["main", "empty"] {
        let local = function(&module, &plan, name);
        assert!(local.used_locals.is_empty());
        assert!(
            local
                .steps
                .values()
                .all(|s| s.resume.is_empty() && s.assignments.is_empty() && s.after.is_empty())
        );
    }
}

#[test]
fn division_boundaries_keep_saved_values_and_reload_fresh_results() {
    use nirvana::ir::Width;
    use nirvana::module_values::BoundaryKind;
    for (width, suffix, divisor) in [
        (Width::U8, "b", "%dl"),
        (Width::U16, "w", "%dx"),
        (Width::U32, "l", "%edx"),
        (Width::U64, "q", "%rdx"),
    ] {
        for signed in [false, true] {
            for memory in [false, true] {
                let operand = if memory { "(%rax)" } else { divisor };
                let (module, values, plan) = fixture(&format!(
                    ".globl main\n.type main,@function\nmain:\n\
                     mov %rax,%rbx\n{}div{suffix} {operand}\n\
                     add %rbx,%rax\nadd %rdx,%rax\nret\n.size main,.-main\n",
                    if signed { "i" } else { "" }
                ));
                let local = function(&module, &plan, "main");
                let values = values
                    .functions
                    .iter()
                    .find(|f| f.function.name == "main")
                    .unwrap()
                    .result
                    .as_ref()
                    .unwrap();
                let boundary = values
                    .boundaries()
                    .iter()
                    .find(|b| matches!(b.kind, BoundaryKind::Divide { .. }))
                    .unwrap();
                let divide = module
                    .program
                    .instructions()
                    .iter()
                    .find(|i| i.address() == boundary.address)
                    .unwrap();
                assert_eq!(
                    boundary.kind,
                    BoundaryKind::Divide {
                        continuation: divide.address() + u64::from(divide.size()),
                        width,
                        signed,
                    }
                );
                assert!(boundary.target_reads.is_empty());
                assert!(boundary.call_contract.is_none());
                assert_eq!(boundary.operand_reads.len(), 1);
                assert_eq!(
                    boundary.operand_reads[0].register,
                    Reg(if memory { 0 } else { 2 })
                );
                let affected: &[usize] = if width == Width::U8 { &[0] } else { &[0, 2] };
                assert_eq!(
                    boundary
                        .inputs
                        .iter()
                        .map(|v| v.register.0)
                        .collect::<Vec<_>>(),
                    affected
                );
                assert_eq!(
                    boundary
                        .outputs
                        .iter()
                        .map(|v| v.register.0)
                        .collect::<Vec<_>>(),
                    affected
                );
                for (input, output) in boundary.inputs.iter().zip(&boundary.outputs) {
                    assert_ne!(input.value, output.value);
                    let nirvana::ssa::Definition::Assignment { site, register } =
                        values.graph().values[output.value.0]
                    else {
                        panic!()
                    };
                    assert_eq!(register, output.register);
                    assert_eq!(values.roles()[&site], PointRole::OpaqueOutput { register });
                }
                assert!(boundary.preserved.iter().any(|v| v.register == Reg(3)));
                assert_eq!(
                    boundary.preserved.iter().any(|v| v.register == Reg(2)),
                    width == Width::U8
                );
                let step = &local.steps[&boundary.address];
                assert!(step.assignments.is_empty(), "events must stay metadata");
                for register in [Reg(0), Reg(2), Reg(3)] {
                    assert!(
                        step.after
                            .iter()
                            .any(|a| a.value == Expr::Register(register))
                    );
                }
                assert!(
                    step.after
                        .iter()
                        .all(|a| matches!(a.destination, Place::Register(r) if r.0 >= 80))
                );
                assert!(
                    !step
                        .after
                        .iter()
                        .any(|a| matches!(a.value, Expr::Const(_) | Expr::Load { .. }))
                );
                let output = nirvana::module_readable::emit_c_with_locals(&module).unwrap();
                assert_eq!(output.report.local_fallback_functions, 0);
            }
        }
    }
}

#[test]
fn stale_byte_division_events_cannot_justify_wider_division_locals() {
    // Both opcodes occupy two bytes, so addresses, function extents, source
    // assignment counts and CFG all agree. The missing RDX input/result must
    // still invalidate the plan, even when only RAX is used afterwards.
    let source = |divide: &str| {
        format!(
            ".globl main\n.type main,@function\nmain:\n{divide}\n\
         add $1,%rax\nret\n.size main,.-main\n"
        )
    };
    let (byte_module, byte_values, _) = fixture(&source("divb %bl"));
    let (wide_module, wide_values, _) = fixture(&source("divl %ebx"));
    assert_eq!(
        byte_module.program.functions(),
        wide_module.program.functions()
    );
    for (module, values) in [(&wide_module, &byte_values), (&byte_module, &wide_values)] {
        let plan = module_local_plan::recover(&module.program, values).unwrap();
        let address = module
            .program
            .functions()
            .iter()
            .find(|f| f.name == "main")
            .unwrap()
            .address;
        let error = plan
            .functions
            .iter()
            .find(|f| f.address == address)
            .unwrap()
            .result
            .as_ref()
            .unwrap_err();
        assert!(
            error.contains("division event coverage mismatch"),
            "{error}"
        );
    }
}

#[test]
fn loop_phi_transfers_are_pure_and_branch_conditions_stay_canonical() {
    let (module, _, plan) = fixture(
        r#"
.globl main
.type main,@function
main:
    mov %rdi,%rax
    mov %rsi,%rbx
    mov $3,%rcx
.Lloop:
    mov %rax,%rdx
    mov %rbx,%rax
    mov %rdx,%rbx
    sub $1,%rcx
    jnz .Lloop
    add %rbx,%rax
    ret
.size main,.-main
"#,
    );
    let local = function(&module, &plan, "main");
    let mut saw_branch = false;
    for instruction in module
        .program
        .instructions()
        .iter()
        .filter(|i| local.steps.contains_key(&i.address()))
    {
        let step = &local.steps[&instruction.address()];
        if let Instruction::Core(i) = instruction
            && let Control::Branch { condition, .. } = &i.control
            && !step.after.is_empty()
        {
            saw_branch = true;
            assert_eq!(
                step.after[0],
                Assignment {
                    destination: Reg(80 + local.local_count + 1).into(),
                    value: condition.clone()
                }
            );
            assert!(
                step.after[1..]
                    .iter()
                    .all(|a| matches!(a.value, Expr::Select { .. }))
            );
        }
        assert!(
            step.after
                .iter()
                .all(|a| matches!(a.destination, Place::Register(r) if r.0 >= 80))
        );
    }
    assert!(saw_branch);
    // Execute the original scalar effects and planned effects with the same
    // controls. This checks normal-flow phi copies independently of resumes.
    let scalar: Vec<_> = module
        .program
        .instructions()
        .iter()
        .filter(|i| local.steps.contains_key(&i.address()))
        .map(|i| match i {
            Instruction::Core(i) => i.clone(),
            Instruction::Return { address, size, .. } => IrInstruction {
                address: *address,
                size: *size,
                assignments: vec![],
                control: Control::Return(Expr::Register(Reg(nirvana::x86::RAX))),
            },
            _ => panic!("scalar fixture"),
        })
        .collect();
    for entry in scalar.iter().map(|i| i.address) {
        let baseline = ir::Program::new(entry, 80, scalar.clone()).unwrap();
        let named = ir::Program::new(
            entry,
            80 + local.local_count + 2,
            scalar
                .iter()
                .map(|i| {
                    let step = &local.steps[&i.address];
                    let mut assignments = step.assignments.clone();
                    assignments.extend_from_slice(&step.after);
                    IrInstruction {
                        address: i.address,
                        size: i.size,
                        assignments,
                        control: i.control.clone(),
                    }
                })
                .collect(),
        )
        .unwrap();
        for seed in 0..4 {
            let mut raw: Vec<_> = (0..80).map(|r| r as u64 * 11 + seed).collect();
            raw[nirvana::x86::RCX] = seed;
            for limit in [0, 1, 2, 7, 30, 60] {
                let expected = baseline.run_with_memory(&raw, 0x1000, &[], limit).unwrap();
                let mut initialized = raw.clone();
                initialized.resize(80 + local.local_count + 2, 0xdead_beef);
                for b in &local.steps[&entry].resume {
                    initialized[80 + b.local] = raw[b.register.0];
                }
                let mut actual = named
                    .run_with_memory(&initialized, 0x1000, &[], limit)
                    .unwrap();
                actual.state.registers.truncate(80);
                assert_eq!(
                    expected, actual,
                    "entry={entry:#x} seed={seed} limit={limit}"
                );
            }
        }
    }
}

#[test]
fn vector_guard_offsets_do_not_execute_as_assignments() {
    let (module, values, plan) = fixture(
        r#"
.globl main
.type main,@function
main:
    movdqa (%rdi),%xmm0
    movdqa %xmm0,(%rsi)
    ret
.size main,.-main
"#,
    );
    let local = function(&module, &plan, "main");
    let analysis = values
        .functions
        .iter()
        .find(|f| f.function.name == "main")
        .unwrap()
        .result
        .as_ref()
        .unwrap();
    for instruction in module.program.instructions() {
        if let Instruction::Vector(v) = instruction {
            let step = &local.steps[&v.address];
            canonical_mirrors(&v.assignments, &step.assignments);
            assert_eq!(
                analysis.roles()[&nirvana::ssa::Site {
                    instruction: v.address,
                    assignment: Some(1)
                }],
                PointRole::VectorAssignment { original: 0 }
            );
        }
    }
}

#[test]
fn analysis_resource_and_source_mismatches_fall_back_per_function() {
    let (module, values, plan) = fixture(
        r#"
.globl main
.type main,@function
main:
    jmp .Ldone
    mov $1,%rax
.Ldone:
    ret
.size main,.-main
.type oversized,@function
oversized:
    .rept 104
    call *%rdi
    .endr
    ret
.size oversized,.-oversized
.type empty,@function
empty:
    ret
.size empty,.-empty
"#,
    );
    // The module lifter already omits the unreachable machine bytes in main.
    assert_eq!(function(&module, &plan, "main").steps.len(), 2);
    {
        let name = "oversized";
        let address = module
            .program
            .functions()
            .iter()
            .find(|f| f.name == name)
            .unwrap()
            .address;
        let error = plan
            .functions
            .iter()
            .find(|f| f.address == address)
            .unwrap()
            .result
            .as_ref()
            .unwrap_err();
        assert!(error.contains("assignment limit"), "{name}: {error}");
    }
    let mut stale = values.clone();
    stale.functions[0].function.size += 1;
    let stale_plan = module_local_plan::recover(&module.program, &stale).unwrap();
    assert!(
        stale_plan.functions[0]
            .result
            .as_ref()
            .unwrap_err()
            .contains("source function mismatch")
    );
    assert!(function(&module, &plan, "empty").used_locals.is_empty());
}

#[test]
fn string_store_contract_rejects_stale_width_and_repeat_analysis() {
    for (old, new) in [
        ("0xf3,0xaa", "0x40,0xaa"),
        ("0x66,0xf3,0xab", "0xf3,0x48,0xab"),
    ] {
        let body = |bytes| {
            format!(
                ".globl main\n.type main,@function\nmain:\n.byte {bytes}\nret\n.size main,.-main"
            )
        };
        let (before, values, original) = fixture(&body(old));
        assert!(original.functions.iter().all(|f| f.result.is_ok()));
        let (after, _, fresh) = fixture(&body(new));
        assert!(fresh.functions.iter().all(|f| f.result.is_ok()));
        assert_eq!(before.program.entry(), after.program.entry());
        let stale = module_local_plan::recover(&after.program, &values).unwrap();
        let changed = stale
            .functions
            .iter()
            .find(|f| f.address == after.program.entry())
            .unwrap();
        assert!(
            changed
                .result
                .as_ref()
                .is_err_and(|e| e.contains("string boundary contract mismatch")),
            "{stale:?}"
        );
    }
}

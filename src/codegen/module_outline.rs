//! Immutable per-function control plans for the checked module renderer.
//!
//! Shapes are control metadata, never executable replacements for the module:
//! vector guards, calls, actual return slots and all guest effects remain in the
//! original instruction stream. Recovery performs no SSA or expression rewrite.

use std::collections::{BTreeMap, BTreeSet};

use crate::codegen::loop_labels::LoopLabels;
use crate::control_flow::structure::{Node, StructuredFunction};
use crate::control_flow::structure_verify::{self, StructureEvidence};
use crate::model::ir::{Control, Expr, IrInstruction};
use crate::model::module_ir::{self, Instruction};

pub const MAX_C_NAME_LENGTH: usize = 63;
const MAX_FUNCTIONS: usize = 512;
const MAX_INSTRUCTIONS: usize = 65_536;

#[derive(Clone, Debug)]
pub struct Plan {
    pub functions: Vec<FunctionPlan>,
    pub imports: Vec<ImportPlan>,
}

#[derive(Clone, Debug)]
pub struct FunctionPlan {
    pub function: module_ir::Function,
    pub c_name: String,
    pub shape: crate::model::ir::Program,
    pub structured: Option<StructuredFunction>,
    pub fallback_reason: Option<String>,
    /// Step occurrences in AST preorder, or original address order on fallback.
    pub sites: Vec<StepSite>,
    /// Each original address resumes at its first checked syntactic occurrence.
    pub resumes: BTreeMap<u64, usize>,
    pub reentry_evidence: Option<StructureEvidence>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct StepSite {
    pub address: u64,
    pub label: usize,
}

#[derive(Clone, Debug)]
pub struct ImportPlan {
    pub import: module_ir::Import,
    pub c_name: String,
}

/// Recover independently checked bodies. A recovery, reentry-proof, or lexical
/// loop-label failure falls back atomically for that function and records why.
/// Invalid source layouts fail the entire plan rather than losing instructions.
pub fn recover(program: &module_ir::Program) -> Result<Plan, String> {
    validate_layout(program)?;
    let mut functions = Vec::with_capacity(program.functions().len());
    for function in program.functions() {
        let end = function.address + function.size; // checked by validate_layout
        let instructions = program
            .instructions()
            .iter()
            .filter(|i| (function.address..end).contains(&i.address()))
            .map(|i| shape_instruction(i, end))
            .collect();
        let shape = crate::model::ir::Program::new(
            function.address,
            program.register_count(),
            instructions,
        )
        .map_err(|error| format!("function {:#x} shape: {error}", function.address))?;
        let checked = recover_structured(&shape);
        let (structured, reentry_evidence, fallback_reason, sites) = match checked {
            Ok((structured, evidence)) => {
                let sites = step_sites(structured.body());
                (Some(structured), Some(evidence), None, sites)
            }
            Err(reason) => {
                let sites = shape
                    .instructions()
                    .iter()
                    .enumerate()
                    .map(|(label, i)| StepSite {
                        address: i.address,
                        label,
                    })
                    .collect();
                (None, None, Some(reason), sites)
            }
        };
        let mut resumes = BTreeMap::new();
        for site in &sites {
            resumes.entry(site.address).or_insert(site.label);
        }
        functions.push(FunctionPlan {
            function: function.clone(),
            c_name: c_name("nv_fn_", &function.name, function.address),
            shape,
            structured,
            fallback_reason,
            sites,
            resumes,
            reentry_evidence,
        });
    }
    let imports = program
        .imports()
        .iter()
        .map(|import| ImportPlan {
            c_name: c_name("nv_import_", &import.name, import.address),
            import: import.clone(),
        })
        .collect();
    Ok(Plan { functions, imports })
}

fn recover_structured(
    shape: &crate::model::ir::Program,
) -> Result<(StructuredFunction, StructureEvidence), String> {
    // Increase the per-block allowance only within the same global source-step
    // budget. The builder checks that budget before cloning assignments; the
    // independent proof rechecks every copy before any candidate is accepted.
    let step_limit = shape.instructions().len() * 2;
    let mut reason = String::new();
    for copy_limit in [2, 4, 8, 16, 32] {
        let checked = StructuredFunction::recover_with_step_limit(shape, copy_limit, step_limit)
            .map_err(|error| error.to_string())
            .and_then(|structured| {
                let evidence = structure_verify::validate_reentries(shape, structured.body())
                    .map_err(|error| format!("reentry validation failed: {error}"))?;
                if evidence.compared_copies > step_limit {
                    return Err(format!(
                        "checked Step copies exceed the global limit of {step_limit}"
                    ));
                }
                if LoopLabels::analyze(structured.body()).is_none() {
                    return Err("loop transfer label planning unavailable".to_string());
                }
                Ok((structured, evidence))
            });
        match checked {
            Ok(candidate) => return Ok(candidate),
            Err(error) => reason = error,
        }
    }
    Err(reason)
}

fn shape_instruction(instruction: &Instruction, end: u64) -> IrInstruction {
    match instruction {
        Instruction::StoreString { address, size, .. }
        | Instruction::MoveString { address, size, .. } => IrInstruction {
            address: *address,
            size: *size,
            assignments: vec![],
            control: Control::Next,
        },
        Instruction::Divide { address, size, .. } => IrInstruction {
            address: *address,
            size: *size,
            assignments: vec![],
            control: Control::Next,
        },
        Instruction::Core(instruction) => instruction.clone(),
        Instruction::Vector(instruction) => IrInstruction {
            address: instruction.address,
            size: instruction.size,
            assignments: instruction.assignments.clone(),
            control: Control::Next,
        },
        Instruction::Transfer {
            address,
            size,
            link,
            ..
        } => IrInstruction {
            address: *address,
            size: *size,
            assignments: vec![],
            control: if link.is_some_and(|next| next != end) {
                Control::Next
            } else {
                Control::Return(Expr::Const(0))
            },
        },
        Instruction::Return { address, size, .. } => IrInstruction {
            address: *address,
            size: *size,
            assignments: vec![],
            control: Control::Return(Expr::Const(0)),
        },
    }
}

fn step_sites(body: &[Node]) -> Vec<StepSite> {
    // The proof and LoopLabels have already bounded this immutable tree.
    let mut sites = Vec::new();
    let mut pending: Vec<_> = body.iter().rev().collect();
    while let Some(node) = pending.pop() {
        match node {
            Node::Step { address, .. } => sites.push(StepSite {
                address: *address,
                label: sites.len(),
            }),
            Node::If {
                taken, not_taken, ..
            } => {
                pending.extend(not_taken.iter().rev());
                pending.extend(taken.iter().rev());
            }
            Node::Loop(body) => pending.extend(body.iter().rev()),
            _ => {}
        }
    }
    sites
}

fn c_name(prefix: &str, source: &str, address: u64) -> String {
    let suffix = format!("_{address:x}");
    let available = MAX_C_NAME_LENGTH - prefix.len() - suffix.len();
    let mut name = String::with_capacity(MAX_C_NAME_LENGTH);
    name.push_str(prefix);
    // Inspect only a bounded prefix, including for names made entirely of
    // non-ASCII bytes. Never insert source text into C identifiers verbatim.
    for byte in source.bytes().take(available) {
        name.push(if byte.is_ascii_alphanumeric() || byte == b'_' {
            byte as char
        } else {
            '_'
        });
    }
    if name.len() == prefix.len() {
        name.push('f');
    }
    name.push_str(&suffix);
    name
}

fn validate_layout(program: &module_ir::Program) -> Result<(), String> {
    if program.functions().is_empty() || program.functions().len() > MAX_FUNCTIONS {
        return Err("module outline function count exceeds bounds".into());
    }
    if program.instructions().len() > MAX_INSTRUCTIONS {
        return Err("module outline instruction count exceeds bounds".into());
    }
    let mut functions: Vec<_> = program.functions().iter().collect();
    functions.sort_by_key(|f| f.address);
    let mut previous_end = None;
    for function in &functions {
        let end = function
            .address
            .checked_add(function.size)
            .filter(|end| *end > function.address)
            .ok_or_else(|| format!("invalid function range at {:#x}", function.address))?;
        if previous_end.is_some_and(|previous| previous > function.address) {
            return Err(format!(
                "overlapping function range at {:#x}",
                function.address
            ));
        }
        previous_end = Some(end);
    }
    let mut addresses = BTreeSet::new();
    let mut owner = 0usize;
    let mut instructions: Vec<_> = program.instructions().iter().collect();
    instructions.sort_by_key(|i| i.address());
    let mut previous_end = None;
    for instruction in instructions {
        let address = instruction.address();
        let end = address
            .checked_add(u64::from(instruction.size()))
            .filter(|end| *end > address)
            .ok_or_else(|| format!("invalid instruction range at {address:#x}"))?;
        if !addresses.insert(address) || previous_end.is_some_and(|previous| previous > address) {
            return Err(format!("overlapping module instruction at {address:#x}"));
        }
        previous_end = Some(end);
        while owner < functions.len() && functions[owner].address + functions[owner].size <= address
        {
            owner += 1;
        }
        if owner == functions.len()
            || address < functions[owner].address
            || end > functions[owner].address + functions[owner].size
        {
            return Err(format!(
                "instruction {address:#x} is outside its function range"
            ));
        }
    }
    for function in functions {
        if !addresses.contains(&function.address) {
            return Err(format!(
                "function {:#x} lacks an entry instruction",
                function.address
            ));
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn c_identifiers_are_bounded_ascii_and_address_disambiguated() {
        for source in [
            "",
            "1 foo; /* */\n#bad",
            "日本語",
            "__asm__",
            &"x".repeat(100_000),
        ] {
            for prefix in ["nv_fn_", "nv_import_"] {
                let name = c_name(prefix, source, u64::MAX);
                assert!(name.starts_with(prefix));
                assert!(name.ends_with("_ffffffffffffffff"));
                assert!(name.len() <= MAX_C_NAME_LENGTH);
                assert!(name.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'_'));
                assert_ne!(name, c_name(prefix, source, u64::MAX - 1));
            }
        }
    }

    #[test]
    fn sites_are_preorder_and_include_every_duplicate_copy() {
        let step = |address| Node::Step {
            address,
            assignments: vec![],
        };
        let body = [
            step(0),
            Node::If {
                condition: Expr::Const(1),
                taken: vec![Node::Loop(vec![step(1), step(2)]), step(3)],
                not_taken: vec![step(2), step(4)],
            },
            step(5),
        ];
        let sites = step_sites(&body);
        assert_eq!(
            sites.iter().map(|s| s.address).collect::<Vec<_>>(),
            [0, 1, 2, 3, 2, 4, 5]
        );
        assert_eq!(
            sites.iter().map(|s| s.label).collect::<Vec<_>>(),
            (0..7).collect::<Vec<_>>()
        );
    }
}

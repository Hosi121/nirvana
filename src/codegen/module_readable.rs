//! Checked whole-module C with named guest functions and structured control.
//!
//! Guest state remains authoritative across every call. Host calls are a bounded
//! fast path: an exhausted host depth unwinds without executing a guest step and
//! the outer dispatcher resumes the same guest PC. Labels at every original
//! step also permit entry in either arm of a branch or in the middle of a loop.

use std::collections::BTreeMap;
use std::fmt::Write;

use crate::codegen::emit::{Expressions, integer, validate_program};
use crate::codegen::loop_labels::LoopLabels;
use crate::codegen::module_emit::{
    c_string, comment, image_initialization, posix_header, runtime_header,
};
use crate::codegen::module_outline::{FunctionPlan, Plan};
use crate::control_flow::structure::Node;
use crate::dataflow::module_local_plan::{self, Locals};
use crate::model::ir::{AccessKind, Control, Expr};
use crate::model::module_ir::{Instruction, Module, REGISTER_COUNT, ROOT_RETURN, Target};

#[derive(Clone, Debug)]
pub struct COutput {
    pub code: String,
    pub report: Report,
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct Report {
    pub functions: usize,
    pub structured_functions: usize,
    pub goto_functions: usize,
    /// Statically known guest-function transfers, including tail transfers.
    pub direct_calls: usize,
    pub indirect_calls: usize,
    /// Transfers specialized to an import, guarded for mutable PLT slots.
    pub import_calls: usize,
    pub local_functions: usize,
    pub local_fallback_functions: usize,
    pub local_variables: usize,
    pub resume_bindings: usize,
    pub call_reloads: usize,
    /// Runtime-guarded same-function tail transfers; residual dispatch remains.
    pub guarded_tail_transfers: usize,
    pub guarded_tail_cases: usize,
    pub selector_snapshots: usize,
    pub selector_switches: usize,
}

/// Lower the original ordered guest effects; metadata and shape assignments
/// never execute. The flat `module_emit` backend remains an independent oracle.
pub fn emit_c(module: &Module) -> Result<COutput, String> {
    render(module, None)
}

/// Execute original module effects with local storage reconstructed from the
/// authoritative guest registers at every function entry, reentry and call.
pub fn emit_c_with_locals(module: &Module) -> Result<COutput, String> {
    let locals = crate::dataflow::module_values::analyze_for_locals(&module.program)
        .and_then(|values| module_local_plan::recover(&module.program, &values))
        .unwrap_or_else(|reason| module_local_plan::Plan {
            functions: module
                .program
                .functions()
                .iter()
                .map(|function| module_local_plan::FunctionLocals {
                    address: function.address,
                    result: Err(reason.clone()),
                })
                .collect(),
        });
    render(module, Some(&locals))
}

fn render(module: &Module, locals: Option<&module_local_plan::Plan>) -> Result<COutput, String> {
    if module.program.register_count() != REGISTER_COUNT || REGISTER_COUNT != 80 {
        return Err("module readable C requires exactly 80 guest registers".to_owned());
    }
    validate_program(module.program.shape()).map_err(|error| error.to_string())?;
    let plan = crate::codegen::module_outline::recover(&module.program)?;
    let tails = crate::codegen::module_tail_dispatch::recover(module, &plan)?;
    let keys = crate::codegen::module_switch_keys::recover(module, &plan, &tails)?;
    let instructions = module
        .program
        .instructions()
        .iter()
        .map(|instruction| (instruction.address(), instruction))
        .collect();
    let mut renderer = Renderer {
        module,
        plan: &plan,
        instructions,
        helpers: String::new(),
        next_helper: 0,
        locals,
        tails: &tails,
        keys: &keys,
    };
    let mut bodies = String::new();
    let mut report = Report {
        functions: plan.functions.len(),
        ..Report::default()
    };
    for function in &plan.functions {
        renderer.function(function, &mut bodies)?;
        let active_locals = locals
            .and_then(|p| {
                p.functions
                    .iter()
                    .find(|f| f.address == function.function.address)
            })
            .is_some_and(|f| f.result.is_ok());
        if !active_locals {
            report.selector_snapshots += keys
                .snapshots
                .iter()
                .filter(|s| s.function == function.function.address)
                .count();
            report.selector_switches += keys
                .branches
                .iter()
                .filter(|(pc, _)| tails.transfers[*pc].function == function.function.address)
                .map(|(_, uses)| uses.len())
                .sum::<usize>();
            for transfer in tails
                .transfers
                .values()
                .filter(|t| t.function == function.function.address)
            {
                report.guarded_tail_transfers += 1;
                report.guarded_tail_cases += transfer.cases.len();
            }
        }
        if locals.is_some() && bodies.len() > 64 * 1024 * 1024 {
            return Err("module local C body limit".into());
        }
        if let Some(locals) = locals {
            match locals
                .functions
                .iter()
                .find(|f| f.address == function.function.address)
                .map(|f| &f.result)
            {
                Some(Ok(local)) => {
                    report.local_functions += 1;
                    report.local_variables += local.used_locals.len();
                    report.resume_bindings +=
                        local.steps.values().map(|s| s.resume.len()).sum::<usize>();
                    for (address, step) in &local.steps {
                        if matches!(
                            renderer.instructions[address],
                            Instruction::Transfer { link: Some(_), .. }
                        ) {
                            report.call_reloads += step.after.iter().filter(|a| {
                                matches!(a.value, Expr::Register(r) if r.0 < REGISTER_COUNT)
                            }).count();
                        }
                    }
                }
                _ => report.local_fallback_functions += 1,
            }
        }
        if function.structured.is_some() {
            report.structured_functions += 1;
        } else {
            report.goto_functions += 1;
        }
    }
    for instruction in module.program.instructions() {
        if let Instruction::Transfer { target, .. } = instruction {
            match target {
                Target::Value(Expr::Const(address))
                    if plan
                        .functions
                        .iter()
                        .any(|f| f.function.address == *address) =>
                {
                    report.direct_calls += 1;
                }
                Target::Value(Expr::Const(address))
                    if plan.imports.iter().any(|i| i.import.address == *address) =>
                {
                    report.import_calls += 1;
                }
                Target::Plt(slot) if renderer.plt_import(*slot).is_some() => {
                    report.import_calls += 1;
                }
                _ => report.indirect_calls += 1,
            }
        }
    }
    let mut code = String::from("#define _POSIX_C_SOURCE 200809L\n");
    code.push_str(&runtime_header(module));
    integer::append_module_helpers(&mut code);
    if module
        .program
        .instructions()
        .iter()
        .any(|i| matches!(i, Instruction::Divide { .. }))
    {
        code.push_str(crate::binary::x86::divide::C_HELPER);
    }
    code.push_str(&posix_header(module));
    code.push_str(
        "\n#ifndef NV_HOST_DEPTH_LIMIT\n#define NV_HOST_DEPTH_LIMIT 64\n#endif\n#if NV_HOST_DEPTH_LIMIT < 1 || NV_HOST_DEPTH_LIMIT > 256\n#error NV_HOST_DEPTH_LIMIT_must_be_between_1_and_256\n#endif\n\n\
         struct nv_frame { struct nv_module *state; unsigned depth,yielded; };\n\
         static void nv_dispatch(struct nv_frame *f);\n",
    );
    for function in &plan.functions {
        writeln!(code, "static void {}(struct nv_frame *f);", function.c_name).unwrap();
    }
    for import in &plan.imports {
        writeln!(code, "static void {}(struct nv_frame *f);", import.c_name).unwrap();
    }
    if let Some(locals) = locals {
        let largest = locals
            .functions
            .iter()
            .filter_map(|f| f.result.as_ref().ok())
            .map(|l| l.used_locals.len())
            .max()
            .unwrap_or(0);
        // Bound the additional named storage in a host call chain. Yielding
        // earlier leaves the guest state untouched and uses the same reentry.
        let cap = 32_768usize
            .checked_div(largest)
            .unwrap_or(256)
            .clamp(1, 256);
        writeln!(code, "\n#define NV_LOCAL_FRAME_DEPTH_CAP {cap}\n#define NV_EFFECTIVE_HOST_DEPTH ((NV_HOST_DEPTH_LIMIT < NV_LOCAL_FRAME_DEPTH_CAP) ? NV_HOST_DEPTH_LIMIT : NV_LOCAL_FRAME_DEPTH_CAP)").unwrap();
    }
    code.push_str(&renderer.helpers);
    code.push_str(&bodies);
    for import in &plan.imports {
        writeln!(
            code,
            "\nstatic void {}(struct nv_frame *f) {{\n    struct nv_module *s=f->state;\n    if(s->imports_left==0) {{ s->status=5; return; }}\n    --s->imports_left;\n    if(!nv_posix_call(s,{})) {{ s->status=3; return; }}\n    s->pc=nv_read(s,s->r[4],8);\n    s->r[4]+=UINT64_C(8);\n}}",
            import.c_name,
            c_string(&import.import.name)
        )
        .unwrap();
    }
    code.push_str(
        "\nstatic void nv_dispatch(struct nv_frame *f) {\n    struct nv_module *s=f->state;\n",
    );
    line(
        &mut code,
        1,
        &format!("if(s->pc==UINT64_C({ROOT_RETURN})) return;"),
    );
    // Imports are exact identities. Ranges only choose the owning function;
    // its local footer rejects addresses that are not original step sites.
    for import in &plan.imports {
        line(
            &mut code,
            1,
            &format!(
                "if(s->pc==UINT64_C({})) {{ {}(f); return; }}",
                import.import.address, import.c_name
            ),
        );
    }
    for function in &plan.functions {
        let end = function
            .function
            .address
            .checked_add(function.function.size)
            .ok_or("function end address overflows")?;
        line(
            &mut code,
            1,
            &format!(
                "if(s->pc>=UINT64_C({}) && s->pc<UINT64_C({end})) {{ {}(f); return; }}",
                function.function.address, function.c_name
            ),
        );
    }
    code.push_str("    s->status=2;\n}\n\nstatic unsigned nv_run(struct nv_module *s) {\n    struct nv_frame frame={s,0,0};\n    s->status=0;\n    if(setjmp(s->jump)!=0) return s->status;\n    for(;;) {\n");
    line(
        &mut code,
        2,
        &format!("if(s->pc==UINT64_C({ROOT_RETURN})) return s->status=0;"),
    );
    code.push_str("        frame.yielded=0;\n        nv_dispatch(&frame);\n        if(s->status) return s->status;\n    }\n}\n");
    code.push_str(&image_initialization(module)?);
    if locals.is_some() && code.len() > 64 * 1024 * 1024 {
        return Err("module local C output limit".into());
    }
    Ok(COutput { code, report })
}

struct Renderer<'a> {
    module: &'a Module,
    plan: &'a Plan,
    instructions: BTreeMap<u64, &'a Instruction>,
    helpers: String,
    next_helper: usize,
    locals: Option<&'a module_local_plan::Plan>,
    tails: &'a crate::codegen::module_tail_dispatch::Plan,
    keys: &'a crate::codegen::module_switch_keys::Plan,
}

impl Renderer<'_> {
    fn function(&mut self, function: &FunctionPlan, code: &mut String) -> Result<(), String> {
        let expressions = Expressions::new(&function.shape);
        let local_result = self
            .locals
            .and_then(|plan| {
                plan.functions
                    .iter()
                    .find(|f| f.address == function.function.address)
            })
            .map(|f| &f.result);
        let local = local_result.and_then(|result| result.as_ref().ok());
        let mut declarations = String::new();
        if local.is_none() {
            for (id, _) in self
                .keys
                .snapshots
                .iter()
                .enumerate()
                .filter(|(_, s)| s.function == function.function.address)
            {
                writeln!(declarations,"    uint64_t nv_key_{id}=UINT64_C(0); unsigned nv_key_valid_{id}=0; (void)nv_key_{id}; (void)nv_key_valid_{id};").unwrap();
            }
        }
        let depth_limit = if self.locals.is_some() {
            "NV_EFFECTIVE_HOST_DEPTH"
        } else {
            "NV_HOST_DEPTH_LIMIT"
        };
        if let Some(local) = local {
            for &index in &local.used_locals {
                let name = local_name(index, local.local_count);
                writeln!(
                    declarations,
                    "    uint64_t {name} = UINT64_C(0); (void){name};"
                )
                .unwrap();
            }
        }
        writeln!(
            code,
            "\n/* function {} at {:#x}, size {} */\nstatic void {}(struct nv_frame *f) {{\n    struct nv_module *s=f->state;\n    uint64_t *r=s->r;\n    struct nirvana_memory m={{s}};\n    (void)r; (void)m;\n{declarations}    if(f->depth>={depth_limit}) {{ f->yielded=1; return; }}\n    ++f->depth;",
            comment(&function.function.name),
            function.function.address,
            function.function.size,
            function.c_name
        )
        .unwrap();
        if local.is_some() {
            line(code, 1, "goto nv_resume;");
        } else {
            line(
                code,
                1,
                &format!(
                    "if(s->pc!=UINT64_C({})) goto nv_resume;",
                    function.function.address
                ),
            );
        }
        if let Some(Err(reason)) = local_result {
            line(
                code,
                1,
                &format!("/* locals fallback: {} */", comment(reason)),
            );
        }
        // Structured recovery may duplicate a tail. All occurrences need a
        // source label, even though the resume map intentionally picks one.
        for site in &function.sites {
            if !function.resumes.values().any(|label| *label == site.label) {
                line(code, 1, &format!("if(0) goto nv_step_{};", site.label));
            }
        }
        if let Some(structured) = &function.structured {
            let labels = LoopLabels::analyze(structured.body())
                .ok_or("module outline supplied unavailable loop labels")?;
            let mut site = 0;
            self.nodes(
                structured.body(),
                function,
                local,
                &expressions,
                &labels,
                &mut site,
                1,
                code,
            )?;
            if site != function.sites.len() {
                return Err("module outline step count differs from structured tree".to_owned());
            }
        } else {
            if let Some(reason) = &function.fallback_reason {
                line(
                    code,
                    1,
                    &format!("/* goto fallback: {} */", comment(reason)),
                );
            }
            for site in &function.sites {
                self.step(site.address, site.label, &expressions, local, 1, code)?;
                self.goto_control(site.address, function, &expressions, 1, code)?;
            }
        }
        code.push_str("    goto nv_exit;\n\nnv_resume: ;\n    switch(s->pc) {\n");
        for (address, label) in &function.resumes {
            if let Some(local) = local {
                let step = local
                    .steps
                    .get(address)
                    .ok_or("missing local resume site")?;
                writeln!(code, "    case UINT64_C({address}):").unwrap();
                for binding in &step.resume {
                    line(
                        code,
                        2,
                        &format!(
                            "{} = r[{}];",
                            local_name(binding.local, local.local_count),
                            binding.register.0
                        ),
                    );
                }
                line(code, 2, &format!("goto nv_step_{label};"));
            } else {
                writeln!(code, "    case UINT64_C({address}): goto nv_step_{label};").unwrap();
            }
        }
        code.push_str(
            "    default: s->status=2; goto nv_exit;\n    }\n\nnv_exit: ;\n    --f->depth;\n}\n",
        );
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn nodes(
        &mut self,
        nodes: &[Node],
        function: &FunctionPlan,
        local: Option<&Locals>,
        expressions: &Expressions,
        labels: &LoopLabels<'_>,
        site: &mut usize,
        indent: usize,
        code: &mut String,
    ) -> Result<(), String> {
        for node in nodes {
            match node {
                Node::Evaluate(value) => expressions
                    .statement(code, indent, value, "(void)(", ");")
                    .map_err(|error| error.to_string())?,
                Node::Step { address, .. } => {
                    let planned = function
                        .sites
                        .get(*site)
                        .ok_or("missing module step site")?;
                    if planned.address != *address {
                        return Err(
                            "module outline step order differs from structured tree".to_owned()
                        );
                    }
                    *site += 1;
                    self.step(*address, planned.label, expressions, local, indent, code)?;
                }
                Node::If {
                    condition,
                    taken,
                    not_taken,
                } => {
                    let condition = self.condition(condition, expressions)?;
                    line(code, indent, &format!("if ({condition}) {{"));
                    self.nodes(
                        taken,
                        function,
                        local,
                        expressions,
                        labels,
                        site,
                        indent + 1,
                        code,
                    )?;
                    if !not_taken.is_empty() {
                        line(code, indent, "} else {");
                        self.nodes(
                            not_taken,
                            function,
                            local,
                            expressions,
                            labels,
                            site,
                            indent + 1,
                            code,
                        )?;
                    }
                    line(code, indent, "}");
                }
                Node::Loop(body) => {
                    labels.loop_id(node).ok_or("missing module loop label")?;
                    if let Some(label) = labels.continue_label(node) {
                        line(code, indent, &format!("{label}: ;"));
                    }
                    line(code, indent, "while (1) {");
                    self.nodes(
                        body,
                        function,
                        local,
                        expressions,
                        labels,
                        site,
                        indent + 1,
                        code,
                    )?;
                    line(code, indent, "}");
                    if let Some(label) = labels.break_label(node) {
                        line(code, indent, &format!("{label}: ;"));
                    }
                }
                Node::Break => line(code, indent, "break;"),
                Node::Continue => line(code, indent, "continue;"),
                Node::BreakOuter { .. } | Node::ContinueOuter { .. } => {
                    let target = labels
                        .target(node)
                        .ok_or("missing outer module loop label")?;
                    line(code, indent, &format!("goto {target};"));
                }
                // These expressions are metadata: actual RET reads the guest
                // slot at its Step, and a tail transfer already set guest PC.
                Node::Return(_) => line(code, indent, "goto nv_exit;"),
            }
        }
        Ok(())
    }

    /// Sequence complex conditions entirely inside an expression helper. A
    /// goto into a branch never crosses a live or uninitialized C temporary.
    fn condition(&mut self, condition: &Expr, expressions: &Expressions) -> Result<String, String> {
        let mut setup = String::new();
        let (_, value) = expressions
            .begin(&mut setup, 0, condition)
            .map_err(|e| e.to_string())?;
        if setup.is_empty() {
            return Ok(value);
        }
        let name = format!("nv_condition_{}", self.next_helper);
        self.next_helper += 1;
        writeln!(
            self.helpers,
            "\nstatic uint64_t {name}(struct nv_frame *f) {{\n    struct nv_module *s=f->state;\n    uint64_t *r=s->r;\n    struct nirvana_memory m={{s}};\n    (void)r; (void)m;"
        )
        .unwrap();
        expressions
            .statement(&mut self.helpers, 1, condition, "return ", ";")
            .map_err(|e| e.to_string())?;
        self.helpers.push_str("}\n");
        Ok(format!("{name}(f)"))
    }

    fn step(
        &self,
        address: u64,
        label: usize,
        expressions: &Expressions,
        local: Option<&Locals>,
        indent: usize,
        code: &mut String,
    ) -> Result<(), String> {
        let instruction = self
            .instructions
            .get(&address)
            .ok_or("module step lacks original instruction")?;
        line(
            code,
            indent,
            &format!("nv_step_{label}: ; /* {address:#x} */"),
        );
        line(code, indent, &format!("s->pc=UINT64_C({address});"));
        line(code, indent, "if(!nv_step(s)) goto nv_exit;");
        line(code, indent, "{");
        let inner = indent + 1;
        let local_step = local
            .map(|local| local.steps.get(&address).ok_or("missing local step"))
            .transpose()?;
        let named_expressions =
            local.map(|local| Expressions::with_locals(REGISTER_COUNT, local.local_count));
        let body_expressions = named_expressions.as_ref().unwrap_or(expressions);
        if local.is_none() {
            for (id, snapshot) in self.keys.at(address) {
                line(code, inner, "{");
                line(code, inner + 1, &format!("uint64_t nv_key_delta_{id};"));
                let delta = Expr::binary(
                    crate::model::ir::BinaryOp::Sub,
                    snapshot.address.clone(),
                    Expr::Const(snapshot.table),
                );
                expressions
                    .statement(
                        code,
                        inner + 1,
                        &delta,
                        &format!("nv_key_delta_{id} = "),
                        ";",
                    )
                    .map_err(|e| e.to_string())?;
                line(
                    code,
                    inner + 1,
                    &format!(
                        "nv_key_{id}=nv_key_delta_{id}>>{};",
                        snapshot.width.bytes().trailing_zeros()
                    ),
                );
                line(
                    code,
                    inner + 1,
                    &format!(
                        "nv_key_valid_{id}=((nv_key_delta_{id}&UINT64_C({}))==0);",
                        snapshot.width.bytes() - 1
                    ),
                );
                line(code, inner, "}");
            }
        }
        match instruction {
            Instruction::StoreString { width, repeat, .. } => line(
                code,
                inner,
                &format!("nv_stos(s,{},{});", width.bytes(), u8::from(*repeat)),
            ),
            Instruction::MoveString { width, repeat, .. } => line(
                code,
                inner,
                &format!("nv_movs(s,{},{});", width.bytes(), u8::from(*repeat)),
            ),
            Instruction::Divide { .. } => crate::codegen::module_emit::divide_statement(
                code,
                expressions,
                instruction,
                inner,
                "goto nv_exit;",
            )?,
            Instruction::Core(instruction) => body_expressions
                .assignments(
                    code,
                    inner,
                    local_step.map_or(&instruction.assignments, |step| &step.assignments),
                )
                .map_err(|error| error.to_string())?,
            Instruction::Transfer { target, link, .. } => {
                line(code, inner, "uint64_t nv_target;");
                if let Target::Value(value) = target {
                    expressions
                        .statement(code, inner, value, "nv_target = ", ";")
                        .map_err(|e| e.to_string())?;
                }
                if let Some(link) = link {
                    line(code, inner, "r[4]-=UINT64_C(8);");
                    line(
                        code,
                        inner,
                        &format!("nv_write(s,r[4],8,UINT64_C({link}));"),
                    );
                }
                if let Target::Plt(slot) = target {
                    line(
                        code,
                        inner,
                        &format!("nv_target=nv_read(s,UINT64_C({slot}),8);"),
                    );
                }
                line(code, inner, "s->pc=nv_target;");
                // Case labels are the same independently checked reentries as
                // the PC footer. Bindings with recovered locals retain the
                // existing dispatch path until their repair is planned here.
                let guarded = if local.is_none() && link.is_none() {
                    self.tails.transfers.get(&address)
                } else {
                    None
                };
                if local.is_none() {
                    self.selector_cases(address, guarded, inner, code)?;
                }
                if let Some(guarded) = guarded {
                    line(code, inner, "switch (nv_target) {");
                    for (target, label) in &guarded.cases {
                        line(
                            code,
                            inner + 1,
                            &format!("case UINT64_C({target}): goto nv_step_{label};"),
                        );
                    }
                    line(code, inner + 1, "default:");
                }
                let dispatch_indent = inner + usize::from(guarded.is_some());
                match target {
                    Target::Value(Expr::Const(address)) => {
                        if let Some(function) = self
                            .plan
                            .functions
                            .iter()
                            .find(|f| f.function.address == *address)
                        {
                            line(code, dispatch_indent, &format!("{}(f);", function.c_name));
                        } else if let Some(import) = self
                            .plan
                            .imports
                            .iter()
                            .find(|i| i.import.address == *address)
                        {
                            line(code, dispatch_indent, &format!("{}(f);", import.c_name));
                        } else {
                            line(code, dispatch_indent, "nv_dispatch(f);");
                        }
                    }
                    Target::Plt(slot) if self.plt_import(*slot).is_some() => {
                        let import = self.plt_import(*slot).unwrap();
                        line(
                            code,
                            dispatch_indent,
                            &format!(
                                "if(nv_target==UINT64_C({})) {}(f);",
                                import.import.address, import.c_name
                            ),
                        );
                        line(code, dispatch_indent, "else nv_dispatch(f);");
                    }
                    _ => line(code, dispatch_indent, "nv_dispatch(f);"),
                }
                if guarded.is_some() {
                    line(code, dispatch_indent, "break;");
                    line(code, inner, "}");
                }
                if let Some(link) = link {
                    line(
                        code,
                        inner,
                        &format!(
                            "if(s->status || f->yielded || s->pc!=UINT64_C({link})) goto nv_exit;"
                        ),
                    );
                }
            }
            Instruction::Return { extra_pop, .. } => {
                line(code, inner, "s->pc=nv_read(s,r[4],8);");
                line(
                    code,
                    inner,
                    &format!("r[4]+=UINT64_C({});", 8u32 + u32::from(*extra_pop)),
                );
            }
            Instruction::Vector(instruction) => {
                if let Some(memory) = &instruction.memory {
                    line(code, inner, "uint64_t nv_vector_address;");
                    expressions
                        .statement(code, inner, &memory.address, "nv_vector_address = ", ";")
                        .map_err(|e| e.to_string())?;
                    let access = match memory.access {
                        AccessKind::Read => 1,
                        AccessKind::Write => 2,
                    };
                    line(
                        code,
                        inner,
                        &format!(
                            "(void)nv_check(s,nv_vector_address,UINT64_C({}),{access});",
                            memory.width
                        ),
                    );
                    if memory.alignment != 1 {
                        let condition = if memory.alignment == 0 {
                            "1".to_owned()
                        } else {
                            format!("nv_vector_address%UINT64_C({})!=0", memory.alignment)
                        };
                        line(code, inner, &format!("if({condition}) {{"));
                        line(
                            code,
                            inner + 1,
                            &format!(
                                "s->status=9; s->fault_address=nv_vector_address; s->fault_width=UINT64_C({}); s->fault_access={access};",
                                memory.width
                            ),
                        );
                        line(code, inner + 1, "goto nv_exit;");
                        line(code, inner, "}");
                    }
                }
                body_expressions
                    .assignments(
                        code,
                        inner,
                        local_step.map_or(&instruction.assignments, |step| &step.assignments),
                    )
                    .map_err(|e| e.to_string())?;
            }
        }
        if let Some(step) = local_step {
            body_expressions
                .assignments(code, inner, &step.after)
                .map_err(|e| e.to_string())?;
        }
        line(code, indent, "}");
        Ok(())
    }

    fn selector_cases(
        &self,
        address: u64,
        guarded: Option<&crate::codegen::module_tail_dispatch::Transfer>,
        indent: usize,
        code: &mut String,
    ) -> Result<(), String> {
        let function = self
            .plan
            .functions
            .iter()
            .find(|f| f.resumes.contains_key(&address))
            .ok_or("selector transfer owner missing")?;
        let uses = guarded.and_then(|_| self.keys.branches.get(&address));
        for (id, _) in self
            .keys
            .snapshots
            .iter()
            .enumerate()
            .filter(|(_, s)| s.function == function.function.address)
        {
            if uses.is_some_and(|uses| uses.iter().any(|u| u.snapshot == id)) {
                line(
                    code,
                    indent,
                    &format!("unsigned nv_had_key_{id}=nv_key_valid_{id};"),
                );
            }
            line(code, indent, &format!("nv_key_valid_{id}=0;"));
        }
        for use_ in uses.into_iter().flatten() {
            let id = use_.snapshot;
            line(code, indent, &format!("if(nv_had_key_{id}) {{"));
            line(code, indent + 1, &format!("switch (nv_key_{id}) {{"));
            let mut groups = BTreeMap::<u64, Vec<(u64, usize)>>::new();
            for (&(value, target), &label) in &use_.cases {
                groups.entry(value).or_default().push((target, label));
            }
            for (value, targets) in groups {
                line(code, indent + 2, &format!("case UINT64_C({value}):"));
                for (target, label) in targets {
                    line(
                        code,
                        indent + 3,
                        &format!("if(nv_target==UINT64_C({target})) goto nv_step_{label};"),
                    );
                }
                line(code, indent + 3, "break;");
            }
            line(code, indent + 2, "default: break;");
            line(code, indent + 1, "}");
            line(code, indent, "}");
        }
        Ok(())
    }

    fn goto_control(
        &self,
        address: u64,
        function: &FunctionPlan,
        expressions: &Expressions,
        indent: usize,
        code: &mut String,
    ) -> Result<(), String> {
        let instruction = self.instructions[&address];
        let next = address
            .checked_add(u64::from(instruction.size()))
            .ok_or("instruction end address overflows")?;
        let destination = |target: u64| -> String {
            if let Some(label) = function.resumes.get(&target) {
                format!("goto nv_step_{label};")
            } else {
                format!("s->pc=UINT64_C({target}); goto nv_resume;")
            }
        };
        match instruction {
            Instruction::Core(instruction) => match &instruction.control {
                Control::Next => line(code, indent, &destination(next)),
                Control::Jump(target) => line(code, indent, &destination(*target)),
                Control::Branch { condition, target } => {
                    expressions
                        .statement(
                            code,
                            indent,
                            condition,
                            "if (",
                            &format!(") {{ {} }}", destination(*target)),
                        )
                        .map_err(|e| e.to_string())?;
                    line(code, indent, &destination(next));
                }
                Control::Return(_) => return Err("module Core cannot contain Return".to_owned()),
            },
            Instruction::Vector(_)
            | Instruction::StoreString { .. }
            | Instruction::MoveString { .. }
            | Instruction::Divide { .. }
            | Instruction::Transfer { link: Some(_), .. } => line(code, indent, &destination(next)),
            Instruction::Return { .. } | Instruction::Transfer { link: None, .. } => {
                line(code, indent, "goto nv_exit;")
            }
        }
        Ok(())
    }

    fn plt_import(&self, slot: u64) -> Option<&crate::codegen::module_outline::ImportPlan> {
        let offset = self.module.image.memory_offset(slot, 8)?;
        let value = u64::from_le_bytes(
            self.module
                .image
                .memory
                .get(offset..offset.checked_add(8)?)?
                .try_into()
                .ok()?,
        );
        self.plan
            .imports
            .iter()
            .find(|import| import.import.address == value)
    }
}

fn line(code: &mut String, indent: usize, text: &str) {
    writeln!(code, "{}{text}", "    ".repeat(indent)).unwrap();
}

fn local_name(index: usize, count: usize) -> String {
    if index < count {
        format!("v_{index}")
    } else if index == count {
        "phi_tmp".into()
    } else {
        "phi_condition".into()
    }
}

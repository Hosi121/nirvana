//! Preparation, evidence and render assembly for readable C.
use super::*;

/// Compare the existing render with checked MIR memory-result refinements.
/// Preserve the input ABI and choose fewer locals, then shorter function text.
pub fn emit_middle_c_with_options(
    function: &crate::model::middle_ir::Function,
    options: ReadableOptions,
) -> Result<ReadableC, ReadableError> {
    use crate::model::middle_ir::Error;
    let source = function.lower().map_err(ReadableError::Middle)?;
    let mut best = emit_readable_c_with_options(&source, options)?;
    let constants = match function.recover_memory_constants() {
        Ok(result) => Some(result),
        Err(
            Error::Limit(_)
            | Error::Ssa(crate::dataflow::ssa::SsaError::Unavailable(_))
            | Error::Memory(_),
        ) => None,
        Err(error) => return Err(ReadableError::Middle(error)),
    };
    if let Some((refined, evidence)) = constants
        && evidence.refined_loads > 0
    {
        let source = refined.lower().map_err(ReadableError::Middle)?;
        if let Ok(mut candidate) = emit_readable_c_with_options(&source, options)
            && candidate.parameters == best.parameters
            && render_cost(&candidate) < render_cost(&best)
        {
            candidate.middle_memory = Some(evidence);
            best = candidate;
        }
    }
    let saved = match function.recover_saved_values() {
        Ok(result) => result,
        Err(
            Error::Limit(_)
            | Error::Ssa(crate::dataflow::ssa::SsaError::Unavailable(_))
            | Error::Memory(_),
        ) => None,
        Err(error) => return Err(ReadableError::Middle(error)),
    };
    if let Some((refined, evidence)) = saved {
        let lowered = refined
            .lower_saved_values()
            .map_err(ReadableError::Middle)?
            .ok_or(ReadableError::Middle(Error::Invalid(
                "missing saved lowering",
            )))?;
        if let Ok(mut candidate) = emit_readable_c_with_options(lowered.program(), options)
            && candidate.parameters == best.parameters
            && render_cost(&candidate) < render_cost(&best)
        {
            candidate.middle_saved = Some(evidence);
            best = candidate;
        }
    }
    Ok(best)
}

pub fn emit_readable_c(program: &Program) -> Result<ReadableC, ReadableError> {
    emit_readable_c_with_options(program, ReadableOptions::default())
}

pub fn emit_readable_c_with_options(
    program: &Program,
    options: ReadableOptions,
) -> Result<ReadableC, ReadableError> {
    let mut best = emit_readable_base(program, options)?;
    if let Some(plan) = crate::dataflow::predicates::PredicatePlan::analyze(program)
        && let Some((lowered, evidence)) = plan.lower(program)
        && let Ok(mut candidate) = emit_readable_base(&lowered, options)
        && candidate.parameters == best.parameters
        && render_cost(&candidate) < render_cost(&best)
    {
        candidate.predicates = Some(evidence);
        best = candidate;
    }
    Ok(best)
}

fn emit_readable_base(
    program: &Program,
    options: ReadableOptions,
) -> Result<ReadableC, ReadableError> {
    let reduced = reduce(program)?;
    let parameters = reduced.parameters().to_vec();
    let mut best = emit_reduced_c(reduced, options);
    if !program.uses_memory() {
        return best;
    }
    // A checked source rewrite can expose copies that the first local-value
    // reduction would otherwise fold into larger expressions. Keep both orders.
    if let Some(plan) = crate::dataflow::memory_values::MemoryValuePlan::analyze(program)
        && let Some(lowered) = plan.lower(program)
        && let Ok(reduced) = reduce(&lowered)
        && reduced.parameters() == parameters
        && let Ok(mut candidate) = emit_reduced_c(reduced, options)
    {
        candidate.memory_value_rounds.insert(0, plan.evidence());
        candidate.memory_values = candidate.memory_value_rounds.first().copied();
        candidate.pre_reduction_memory_rounds = 1;
        if best
            .as_ref()
            .map_or(true, |old| render_cost(&candidate) < render_cost(old))
        {
            best = Ok(candidate);
        }
    }
    best
}

/// Validate only the IR reduction. Structuring and C emission have their own
/// testing boundary and are not certified by this block model.
pub fn emit_readable_c_with_checked_reduction(
    program: &Program,
    solver: &Solver,
) -> Result<(ReadableC, Validation), ReadableError> {
    emit_readable_c_with_checked_reduction_and_options(program, solver, ReadableOptions::default())
}

pub fn emit_readable_c_with_checked_reduction_and_options(
    program: &Program,
    solver: &Solver,
    options: ReadableOptions,
) -> Result<(ReadableC, Validation), ReadableError> {
    let checked = reduce_checked(program, solver)?;
    Ok((
        emit_reduced_c(checked.function, options)?,
        checked.validation,
    ))
}

fn emit_reduced_c(
    reduced: ReducedFunction,
    options: ReadableOptions,
) -> Result<ReadableC, ReadableError> {
    use prepare::MemoryRecovery;
    let mut best = emit_reduced_choice(&reduced, options, MemoryRecovery::Disabled);
    // Stored-value recovery requires checked memory expressions.
    if !reduced.program().uses_memory() {
        return best;
    }
    // Compare complete renders: more proved loads can require more C storage.
    // Keep the baseline on ties and preserve the previous register-only choice.
    for recovery in [
        MemoryRecovery::Registers,
        MemoryRecovery::StoredExpressions,
        MemoryRecovery::InvariantExpressions(1),
        MemoryRecovery::InvariantExpressions(2),
        MemoryRecovery::InvariantExpressions(3),
    ] {
        if let Ok(candidate) = emit_reduced_choice(&reduced, options, recovery) {
            let exhausted = matches!(recovery, MemoryRecovery::InvariantExpressions(_))
                && candidate.memory_value_rounds.len() < recovery.rounds()
                && !matches!(candidate.web_recovery, WebRecovery::RenderingFallback(_));
            if best
                .as_ref()
                .map_or(true, |old| render_cost(&candidate) < render_cost(old))
            {
                best = Ok(candidate);
            }
            if exhausted {
                break;
            }
        }
    }
    best
}
fn render_cost(output: &ReadableC) -> (usize, usize, usize) {
    (
        output.locals.len(),
        output
            .code
            .split_once("uint64_t nirvana_readable(")
            .map_or(output.code.len(), |(_, body)| body.len()),
        output.code.len(),
    )
}

fn emit_reduced_choice(
    reduced: &ReducedFunction,
    options: ReadableOptions,
    memory_recovery: prepare::MemoryRecovery,
) -> Result<ReadableC, ReadableError> {
    let prepared = prepare::prepare(reduced.program(), reduced.parameters(), memory_recovery)?;
    let renamed = matches!(prepared.web_recovery, WebRecovery::Applied { .. });
    match emit_prepared_c(reduced, options, prepared) {
        Ok(output) => Ok(output),
        Err(error) if renamed => {
            let fallback = prepare::prepare_original(
                reduced.program(),
                reduced.parameters(),
                WebRecovery::RenderingFallback(error),
                memory_recovery,
            )?;
            emit_prepared_c(reduced, options, fallback)
        }
        Err(error) => Err(error),
    }
}

fn emit_prepared_c(
    reduced: &ReducedFunction,
    options: ReadableOptions,
    prepared: PreparedFunction,
) -> Result<ReadableC, ReadableError> {
    let try_continuations = prepared
        .nodes
        .as_deref()
        .is_some_and(super::continuations::possible);
    if !try_continuations {
        return emit_prepared_layout(reduced, options, prepared, false);
    }
    let baseline = emit_prepared_layout(reduced, options, prepared.clone(), false)?;
    if try_continuations
        && let Ok(candidate) = emit_prepared_layout(reduced, options, prepared, true)
        && candidate.continuations.is_some()
        && candidate.parameters == baseline.parameters
        && render_cost(&candidate) < render_cost(&baseline)
    {
        return Ok(candidate);
    }
    Ok(baseline)
}

fn emit_prepared_layout(
    reduced: &ReducedFunction,
    options: ReadableOptions,
    prepared: PreparedFunction,
    share_continuations: bool,
) -> Result<ReadableC, ReadableError> {
    let PreparedFunction {
        program: presented,
        widths: value_widths,
        structure: structured,
        nodes,
        shared_nodes,
        source_evidence: structure_evidence,
        source_stats: structure_stats,
        web_recovery,
        load_mask_evidence,
        expression_evidence,
        semantic_evidence,
        ssa_constants,
        known_bits,
        memory_values,
        memory_value_rounds,
    } = prepared;
    let program = &presented;
    let context_remainders = expression_evidence
        .is_none()
        .then(|| crate::transform::context_remainder::ContextRemainders::analyze(program))
        .flatten();
    let graph_remainders = expression_evidence
        .is_none()
        .then(|| crate::transform::remainder_graph::GraphRemainders::analyze(program))
        .flatten();
    let display_nodes = nodes.as_deref();
    let mut views = MemoryViews::recover(program, reduced.parameters(), options);
    let read = rendered_reads(program, views.as_ref());
    let address_uses = if options.recover_objects {
        address_registers(program)
    } else {
        BTreeSet::new()
    };
    let mut names = BTreeMap::new();
    let mut arguments = Vec::new();
    let mut code = String::from("#include <stdint.h>\n");
    for (index, reg) in reduced.parameters().iter().enumerate() {
        let name = if options.compact_memory && options.stack_register == Some(*reg) {
            "stack_base".into()
        } else if options.compact_memory
            && let Some(object) = views
                .as_ref()
                .and_then(|v| v.objects.iter().find(|o| o.register == *reg))
        {
            format!("{}_address", object.name)
        } else {
            format!("arg{index}")
        };
        names.insert(reg.0, name.clone());
        arguments.push(format!("uint64_t {name}"));
        writeln!(code, "/* {name}: input machine register {} */", reg.0).unwrap();
    }
    if program.uses_memory() {
        code.push_str(MEMORY_HELPERS);
        if views.is_some() || options.compact_memory || options.recover_objects {
            code.push_str(VIEW_HELPERS);
        }
        if options.compact_memory {
            code.push_str(syntax::COMPACT_MEMORY);
        }
        arguments.extend(["uint8_t *memory", "uint64_t base", "uint64_t size"].map(String::from));
    }
    let LocalPlan {
        names,
        widths,
        slots: printer_slots,
        initial_slots,
        mut locals,
        value_count: local_value_count,
        stats: local_plan,
        stack_roles,
        stack_cells,
    } = LocalPlan::build(
        program,
        reduced.parameters(),
        &read,
        names,
        &value_widths,
        display_nodes.unwrap_or(&[]),
        options,
    );
    let hints = if options.recover_objects && program.uses_memory() {
        crate::codegen::address_types::register_hints(program)
    } else {
        BTreeMap::new()
    };
    let mut address_types = BTreeMap::new();
    let mut typedefs = BTreeSet::new();
    for local in &mut locals {
        if local.width != Width::U64 {
            continue;
        }
        let Some(&width) = hints.get(&local.register.0) else {
            continue;
        };
        // Coalescing can put several unrelated SSA lifetimes in one C local.
        // Give the whole local a hint only when every member agrees.
        if local
            .registers
            .iter()
            .all(|r| hints.get(&r.0) == Some(&width))
        {
            local.address_width = Some(width);
            typedefs.insert(width.bits());
            for reg in &local.registers {
                address_types.insert(reg.0, width);
            }
        }
    }
    if !typedefs.is_empty() {
        code.push_str("\n/* Guest addresses, grouped by observed access width. */\n");
        for bits in typedefs {
            writeln!(code, "typedef uint64_t nirvana_u{bits}_address;").unwrap();
        }
    }
    if options.compact_memory
        && let (Some(views), Some(roles)) = (&mut views, &stack_roles)
    {
        views.name_stack_roles(roles);
    }
    let arguments = if arguments.is_empty() {
        "void".into()
    } else {
        arguments.join(", ")
    };
    writeln!(code, "\nuint64_t nirvana_readable({arguments}) {{").unwrap();
    for reg in reduced.parameters() {
        if !read.contains(&reg.0) {
            line(&mut code, 1, &format!("(void){};", names[&reg.0]));
        }
    }
    if program.uses_memory() {
        line(
            &mut code,
            1,
            "struct nirvana_memory m = {memory, base, size};",
        );
    }
    if let Some(views) = &views {
        let printer = Printer {
            source_program: program,
            context_remainders: None,
            graph_remainders: None,
            names: names.clone(),
            read: read.clone(),
            views: None,
            first_temporary: program.register_count(),
            widths: widths.clone(),
            address_types: BTreeMap::new(),
            address_uses: address_uses.clone(),
            recover_objects: false,
            compact_memory: options.compact_memory,
            slots: printer_slots.clone(),
            initial_slots: initial_slots.clone(),
            declarations: Rc::new(DeclarationPlan::default()),
        };
        for view in views.stack_views() {
            let base = Expr::Register(options.stack_register.expect("stack view base"));
            let base = if view.offset < 0 {
                Expr::binary(BinaryOp::Sub, base, Expr::Const(view.offset.unsigned_abs()))
            } else if view.offset > 0 {
                Expr::binary(BinaryOp::Add, base, Expr::Const(view.offset as u64))
            } else {
                base
            };
            let path = ViewPath::Object {
                name: view.name.clone(),
                base,
            };
            line(
                &mut code,
                1,
                &format!(
                    "const struct nirvana_view {} = {{{}}}; /* entry stack {:+}, up to {} bytes{} */",
                    view.name,
                    printer.expression(&path.address()).text,
                    view.offset,
                    view.byte_size,
                    if view.overlaps.is_empty() {
                        ""
                    } else {
                        ", overlapping views"
                    }
                ),
            );
        }
    }
    if let Some(views) = &views {
        let printer = Printer {
            source_program: program,
            context_remainders: None,
            graph_remainders: None,
            names: names.clone(),
            read: read.clone(),
            views: None,
            first_temporary: program.register_count(),
            widths: widths.clone(),
            address_types: BTreeMap::new(),
            address_uses: address_uses.clone(),
            recover_objects: false,
            compact_memory: options.compact_memory,
            slots: printer_slots.clone(),
            initial_slots: initial_slots.clone(),
            declarations: Rc::new(DeclarationPlan::default()),
        };
        for object in &views.objects {
            line(
                &mut code,
                1,
                &format!(
                    "/* input register {}: address views, potentially aliased */",
                    object.register.0
                ),
            );
            line(&mut code, 1, "const struct {");
            if !object.indexed.is_empty() {
                line(&mut code, 2, "struct nirvana_view base;");
            }
            for field in &object.fields {
                line(
                    &mut code,
                    2,
                    &format!("struct nirvana_view {};", field.name),
                );
            }
            line(&mut code, 1, &format!("}} {} = {{", object.name));
            if !object.indexed.is_empty() {
                line(
                    &mut code,
                    2,
                    &format!(
                        "{{{}}},",
                        printer.expression(&Expr::Register(object.register)).text
                    ),
                );
            }
            for field in &object.fields {
                let base = ViewPath::Object {
                    name: object.name.clone(),
                    base: Expr::Register(object.register),
                };
                let address = if field.offset < 0 {
                    Expr::binary(
                        BinaryOp::Sub,
                        base.address(),
                        Expr::Const(field.offset.unsigned_abs()),
                    )
                } else {
                    crate::transform::simplify::simplify(
                        &ViewPath::Field {
                            base: Box::new(base),
                            offset: field.offset as u64,
                        }
                        .address(),
                    )
                };
                line(
                    &mut code,
                    2,
                    &format!("{{{}}},", printer.expression(&address).text),
                );
            }
            line(&mut code, 1, "};");
        }
    }
    let mut printer = Printer {
        source_program: program,
        context_remainders: context_remainders.as_ref(),
        graph_remainders: graph_remainders.as_ref(),
        names,
        read,
        views,
        first_temporary: program.register_count(),
        widths,
        address_types,
        address_uses,
        recover_objects: options.recover_objects,
        compact_memory: options.compact_memory,
        slots: printer_slots,
        initial_slots,
        declarations: Rc::new(DeclarationPlan::default()),
    };
    let recovered = if share_continuations {
        display_nodes.and_then(|nodes| super::continuations::recover(&printer, nodes))
    } else {
        None
    };
    let effective_nodes = recovered
        .as_ref()
        .map(|(nodes, _)| nodes.as_slice())
        .or(display_nodes);
    let eligible = locals.iter().map(|local| local.name.clone()).collect();
    printer.declarations = Rc::new(DeclarationPlan::build(
        effective_nodes,
        if recovered.is_some() {
            None
        } else {
            shared_nodes.as_deref()
        },
        &printer.names,
        &printer.read,
        &eligible,
    ));
    for local in &locals {
        if printer.declarations.inline(&local.name) {
            continue;
        }
        line(
            &mut code,
            1,
            &format!(
                "{} {};",
                local_type(local.width, local.address_width),
                local.name
            ),
        );
    }
    let stack_views = printer
        .views
        .as_ref()
        .map(|v| v.stack_views().to_vec())
        .unwrap_or_default();
    let object_views = printer
        .views
        .as_ref()
        .map(|v| v.objects.clone())
        .unwrap_or_default();
    let mut finite_regions = Vec::new();
    let mut affine_regions = Vec::new();
    let continuation_evidence = recovered.as_ref().map(|(_, evidence)| *evidence);
    let (fallback_reason, display_structure_evidence) = match structured {
        Ok(function) => {
            let nonlocal = LoopLabels::analyze(function.body())
                .ok_or(ReadableError::LoopLabelsUnavailable)?
                .has_transfers();
            let nodes = effective_nodes.expect("recovered nodes");
            let mut selected = nodes;
            let mut body = String::new();
            printer.nodes(&mut body, nodes, 1, nonlocal)?;
            if continuation_evidence.is_none()
                && let Some(shared) = &shared_nodes
                && shared != nodes
            {
                let mut candidate = String::new();
                // Compare the same C body using the same names, storage,
                // widths, views and checks. Sharing a lone break/return can
                // otherwise replace flat exits by deep else chains.
                if printer.nodes(&mut candidate, shared, 1, nonlocal).is_ok()
                    && candidate.len() < body.len()
                    && max_indent(&candidate) <= max_indent(&body)
                {
                    body = candidate;
                    selected = shared;
                }
            }
            if continuation_evidence.is_none()
                && !nonlocal
                && let Some(recovered) = loops::recover(&printer, selected, &locals)
            {
                let mut candidate = String::new();
                if printer
                    .nodes(&mut candidate, &recovered.nodes, 1, false)
                    .is_ok()
                    && candidate.len() < body.len()
                    && max_indent(&candidate) <= max_indent(&body)
                {
                    body = candidate;
                    match recovered.evidence {
                        loops::RegionEvidence::Finite(evidence) => finite_regions.push(evidence),
                        loops::RegionEvidence::Affine(evidence) => affine_regions.push(evidence),
                    }
                }
            }
            code.push_str(&body);
            (None, Some(function.evidence()))
        }
        Err(reason) => {
            printer.gotos(&mut code, program)?;
            (Some(reason), None)
        }
    };
    code.push_str("}\n");
    if program.uses_memory() && options.compact_memory {
        code.push_str(syntax::COMPACT_END);
    }
    // Emit only helpers referenced by the final selected layout. Discarded
    // candidates and metadata rendering must not add unused definitions.
    let bit_helpers = idioms::definitions(&code);
    if !bit_helpers.is_empty() {
        let start = code
            .find("uint64_t nirvana_readable(")
            .expect("function declaration");
        code.insert_str(start, &bit_helpers);
    }
    Ok(ReadableC {
        continuations: continuation_evidence,
        predicates: None,
        code,
        middle_memory: None,
        middle_saved: None,
        parameters: reduced.parameters().to_vec(),
        uses_memory: program.uses_memory(),
        reduction_stats: reduced.stats(),
        fallback_reason,
        structure_stats,
        structure_evidence,
        display_structure_evidence,
        load_mask_evidence,
        expression_evidence,
        semantic_evidence,
        ssa_constants,
        known_bits,
        memory_values,
        memory_value_rounds,
        pre_reduction_memory_rounds: 0,
        web_recovery,
        stack_views,
        object_views,
        locals,
        local_value_count,
        local_plan,
        stack_roles,
        stack_cells,
        finite_regions,
        affine_regions,
    })
}

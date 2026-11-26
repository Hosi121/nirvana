//! Readable fallback rendering with checked natural-loop scopes and local gotos.
use super::*;
use crate::codegen::goto_layout::loops::{Event, LoopLayout, Transfer};

fn statement(transfer: Transfer) -> Option<String> {
    match transfer {
        Transfer::Fallthrough => None,
        Transfer::Continue => Some("continue;".into()),
        Transfer::Break => Some("break;".into()),
        Transfer::Goto(target) => Some(format!("goto {target};")),
    }
}

impl Printer<'_> {
    pub(super) fn gotos(&self, code: &mut String, program: &Program) -> Result<(), SequenceError> {
        let cfg = program.cfg();
        let layout = GotoLayout::compute(program);
        let original_order = layout
            .as_ref()
            .map(|l| l.blocks().to_vec())
            .unwrap_or_else(|| cfg.reachable_blocks().into_iter().collect());
        let resolve = |id| layout.as_ref().map_or(id, |l| l.resolve(id));
        let block_at = |address| resolve(cfg.block_at(address).expect("validated destination"));
        let entry = layout.as_ref().map_or(cfg.entry(), |l| l.entry());
        let flat_next: BTreeMap<_, _> = original_order
            .iter()
            .enumerate()
            .map(|(index, &id)| (id, original_order.get(index + 1).copied()))
            .collect();
        let targets = |id| {
            let block = cfg.block(id);
            let i = &program.instructions()[block.instructions.end - 1];
            match &i.control {
                Control::Next => vec![block_at(i.address + u64::from(i.size))],
                Control::Jump(target) => vec![block_at(*target)],
                Control::Branch { target, .. } => {
                    vec![block_at(*target), block_at(i.address + u64::from(i.size))]
                }
                Control::Return(_) => vec![],
            }
        };
        let flat_gotos: usize = original_order
            .iter()
            .map(|&id| {
                targets(id)
                    .into_iter()
                    .collect::<BTreeSet<_>>()
                    .iter()
                    .filter(|&&target| Some(target) != flat_next[&id])
                    .count()
            })
            .sum();
        let loops = layout
            .as_ref()
            .and_then(|flat| LoopLayout::compute(program, flat))
            .filter(|plan| plan.goto_count() < flat_gotos);
        let events = loops
            .as_ref()
            .map(|plan| plan.events().to_vec())
            .unwrap_or_else(|| original_order.iter().copied().map(Event::Block).collect());
        let transfer = |from, target| {
            if let Some(plan) = &loops {
                plan.transfer(from, target).expect("checked source edge")
            } else if flat_next[&from] == Some(target) {
                Transfer::Fallthrough
            } else {
                Transfer::Goto(target)
            }
        };
        let first = events.iter().find_map(|event| match event {
            Event::Block(id) => Some(*id),
            _ => None,
        });
        let mut labels = BTreeSet::new();
        if first != Some(entry) {
            labels.insert(entry);
        }
        for &id in &original_order {
            for target in targets(id) {
                if let Transfer::Goto(target) = transfer(id, target) {
                    labels.insert(target);
                }
            }
        }
        if first != Some(entry) {
            line(code, 1, &format!("goto {entry};"));
        }
        let mut indent = 1;
        for event in events {
            let id = match event {
                Event::Open(_) => {
                    line(code, indent, "for (;;) {");
                    indent += 1;
                    continue;
                }
                Event::Close(_) => {
                    indent -= 1;
                    line(code, indent, "}");
                    continue;
                }
                Event::Block(id) => id,
            };
            let block = cfg.block(id);
            if labels.contains(&id) {
                // A header can have no emitted assignment or transfer. The null
                // statement also makes a label before a closing brace valid C11.
                if loops.is_some() {
                    writeln!(code, "{id}:;").unwrap();
                } else {
                    writeln!(code, "{id}:").unwrap();
                }
            }
            for instruction in &program.instructions()[block.instructions.clone()] {
                self.assignments(code, indent, instruction.address, &instruction.assignments)?;
            }
            let i = &program.instructions()[block.instructions.end - 1];
            match &i.control {
                Control::Next | Control::Jump(_) => {
                    let target = match i.control {
                        Control::Jump(address) => block_at(address),
                        _ => block_at(i.address + u64::from(i.size)),
                    };
                    if let Some(text) = statement(transfer(id, target)) {
                        line(code, indent, &text);
                    }
                }
                Control::Branch { condition, target } => {
                    let taken = block_at(*target);
                    let not_taken = block_at(i.address + u64::from(i.size));
                    if taken == not_taken {
                        self.value_statement(code, indent, condition, None, "(void)(", ");")?;
                        if let Some(text) = statement(transfer(id, taken)) {
                            line(code, indent, &text);
                        }
                        continue;
                    }
                    let scoped = needs_sequence(condition);
                    if scoped {
                        line(code, indent, "{");
                    }
                    let inner = indent + usize::from(scoped);
                    let mut temporary = self.first_temporary;
                    let value =
                        self.ordered_expression(code, inner, condition, None, &mut temporary)?;
                    let taken_transfer = transfer(id, taken);
                    if taken_transfer == Transfer::Fallthrough {
                        let text = statement(transfer(id, not_taken)).expect("distinct successor");
                        line(code, inner, &format!("if (!({})) {text}", value.text));
                    } else {
                        let text = statement(taken_transfer).expect("non-fallthrough");
                        line(code, inner, &format!("if ({}) {text}", value.text));
                        if let Some(text) = statement(transfer(id, not_taken)) {
                            line(code, inner, &text);
                        }
                    }
                    if scoped {
                        line(code, indent, "}");
                    }
                }
                Control::Return(value) => {
                    self.value_statement(code, indent, value, None, "return ", ";")?
                }
            }
        }
        debug_assert_eq!(indent, 1);
        Ok(())
    }
}

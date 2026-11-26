//! Readable fallback rendering from the original CFG layout.
use super::*;

impl Printer<'_> {
    pub(super) fn gotos(&self, code: &mut String, program: &Program) -> Result<(), SequenceError> {
        let cfg = program.cfg();
        let layout = GotoLayout::compute(program);
        let order = layout
            .as_ref()
            .map(|l| l.blocks().to_vec())
            .unwrap_or_else(|| cfg.reachable_blocks().into_iter().collect());
        let resolve = |id| layout.as_ref().map_or(id, |l| l.resolve(id));
        let block_at = |address| resolve(cfg.block_at(address).expect("validated destination"));
        let entry = layout.as_ref().map_or(cfg.entry(), |l| l.entry());
        // Only destinations of jumps which survive fallthrough need labels.
        let mut labels = BTreeSet::new();
        if order.first() != Some(&entry) {
            labels.insert(entry);
        }
        for (index, &id) in order.iter().enumerate() {
            let next = order.get(index + 1).copied();
            let block = cfg.block(id);
            let instruction = &program.instructions()[block.instructions.end - 1];
            let mut target = |id| {
                if Some(id) != next {
                    labels.insert(id);
                }
            };
            match &instruction.control {
                Control::Next => {
                    target(block_at(instruction.address + u64::from(instruction.size)))
                }
                Control::Jump(address) => target(block_at(*address)),
                Control::Branch {
                    target: address, ..
                } => {
                    target(block_at(*address));
                    target(block_at(instruction.address + u64::from(instruction.size)));
                }
                Control::Return(_) => {}
            }
        }
        if order.first() != Some(&entry) {
            line(code, 1, &format!("goto {entry};"));
        }
        for (index, &id) in order.iter().enumerate() {
            let next = order.get(index + 1).copied();
            let block = cfg.block(id);
            if labels.contains(&id) {
                writeln!(code, "{id}:").unwrap();
            }
            for instruction in &program.instructions()[block.instructions.clone()] {
                self.assignments(code, 1, instruction.address, &instruction.assignments)?;
            }
            let instruction = &program.instructions()[block.instructions.end - 1];
            match &instruction.control {
                Control::Next | Control::Jump(_) => {
                    let target = match instruction.control {
                        Control::Jump(address) => block_at(address),
                        _ => block_at(instruction.address + u64::from(instruction.size)),
                    };
                    if Some(target) != next {
                        line(code, 1, &format!("goto {target};"));
                    }
                }
                Control::Branch { condition, target } => {
                    let taken = block_at(*target);
                    let not_taken = block_at(instruction.address + u64::from(instruction.size));
                    if taken == not_taken {
                        self.value_statement(code, 1, condition, None, "(void)(", ");")?;
                        if Some(taken) != next {
                            line(code, 1, &format!("goto {taken};"));
                        }
                        continue;
                    }
                    let scoped = needs_sequence(condition);
                    if scoped {
                        line(code, 1, "{");
                    }
                    let inner = 1 + usize::from(scoped);
                    let mut temporary = self.first_temporary;
                    let value =
                        self.ordered_expression(code, inner, condition, None, &mut temporary)?;
                    if Some(taken) == next {
                        line(
                            code,
                            inner,
                            &format!("if (!({})) goto {not_taken};", value.text),
                        );
                    } else {
                        line(code, inner, &format!("if ({}) goto {taken};", value.text));
                        if Some(not_taken) != next {
                            line(code, inner, &format!("goto {not_taken};"));
                        }
                    }
                    if scoped {
                        line(code, 1, "}");
                    }
                }
                Control::Return(value) => {
                    self.value_statement(code, 1, value, None, "return ", ";")?
                }
            }
        }
        Ok(())
    }
}

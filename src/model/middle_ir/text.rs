use super::*;
use std::fmt::Write;

struct Text(String);
impl Text {
    fn line(&mut self, indent: usize, args: fmt::Arguments<'_>) -> Result<(), Error> {
        writeln!(self.0, "{:width$}{args}", "", width = indent * 2).unwrap();
        if self.0.len() > 4 * 1024 * 1024 {
            return Err(Error::Limit("text output"));
        }
        Ok(())
    }
    fn region(&mut self, region: &Region, indent: usize) -> Result<(), Error> {
        for binding in &region.bindings {
            let id = binding.id.0;
            match &binding.operation {
                Operation::Pure(Pure::Constant(n)) => {
                    self.line(indent, format_args!("%{id} = const {n:#x}"))?
                }
                Operation::Pure(Pure::Unary(op, input)) => {
                    self.line(indent, format_args!("%{id} = {op:?} %{}", input.0))?
                }
                Operation::Pure(Pure::Binary(op, a, b)) => {
                    self.line(indent, format_args!("%{id} = {op:?} %{}, %{}", a.0, b.0))?
                }
                Operation::ReadStorage { storage, version } => self.line(
                    indent,
                    format_args!("%{id} = read s{} [{}]", storage.0, version_text(*version)),
                )?,
                Operation::ReadSaved {
                    storage,
                    version,
                    slice,
                } => self.line(
                    indent,
                    format_args!(
                        "%{id} = saved #{} bits {}:{} via s{} [{}]",
                        slice.snapshot.0,
                        slice.start,
                        slice.width.bits(),
                        storage.0,
                        version_text(*version)
                    ),
                )?,
                Operation::Load { address, width } => self.line(
                    indent,
                    format_args!("%{id} = load{} %{}", width.bits(), address.0),
                )?,
                Operation::KnownLoad {
                    address,
                    width,
                    value,
                } => self.line(
                    indent,
                    format_args!(
                        "%{id} = checked-load{} %{} => {value:#x}",
                        width.bits(),
                        address.0
                    ),
                )?,
                Operation::Select {
                    condition,
                    taken,
                    not_taken,
                } => {
                    self.line(indent, format_args!("%{id} = select %{} {{", condition.0))?;
                    self.line(indent + 1, format_args!("taken:"))?;
                    self.region(taken, indent + 2)?;
                    self.line(indent + 2, format_args!("yield %{}", taken.result.0))?;
                    self.line(indent + 1, format_args!("not_taken:"))?;
                    self.region(not_taken, indent + 2)?;
                    self.line(indent + 2, format_args!("yield %{}", not_taken.result.0))?;
                    self.line(indent, format_args!("}}"))?;
                }
            }
        }
        Ok(())
    }
}
fn version_text(version: Option<ssa::ValueId>) -> String {
    version.map_or_else(|| "entry-unreachable".into(), |id| format!("ssa v{}", id.0))
}
impl Function {
    /// A bounded diagnostic representation. All scalar values are 64-bit words;
    /// storage/SSA labels describe machine storage, not recovered source names.
    pub fn to_text(&self) -> Result<String, Error> {
        let mut text = Text(String::new());
        text.line(
            0,
            format_args!(
                "middle-ir-v1 entry @{:#x} storages={} values={} source_values={}",
                self.entry,
                self.storages.len(),
                self.value_count,
                self.source_value_count
            ),
        )?;
        if let Some(saved) = self.saved_values() {
            for (n, snapshot) in saved.snapshots.iter().enumerate() {
                let source = match snapshot.origin {
                    crate::dataflow::memory_values::SavedValue::Register(id) => {
                        format!("ssa v{}", id.0)
                    }
                    crate::dataflow::memory_values::SavedValue::Stored(site) => format!(
                        "store-rhs @{:#x}:{}",
                        site.instruction,
                        site.assignment.unwrap()
                    ),
                };
                let point = snapshot
                    .point
                    .after
                    .map_or_else(|| "before".into(), |n| format!("after assignment {n}"));
                text.line(
                    0,
                    format_args!(
                        "snapshot #{n} = {source} @{:#x} {point}",
                        snapshot.point.instruction
                    ),
                )?;
            }
            for load in &saved.loads {
                text.line(
                    0,
                    format_args!(
                        "saved-load @{:#x}:{} [ssa v{}] => #{} bits {}:{}",
                        load.site.instruction,
                        load.site.assignment.unwrap(),
                        load.definition.0,
                        load.slice.snapshot.0,
                        load.slice.start,
                        load.slice.width.bits()
                    ),
                )?;
            }
        }
        for block in &self.blocks {
            text.line(0, format_args!("block @{:#x}:", block.address))?;
            if let Some(ssa_block) = self.ssa.blocks.iter().find(|b| b.start == block.address) {
                for phi in &ssa_block.phis {
                    if let ssa::Definition::Phi {
                        register, inputs, ..
                    } = &self.ssa.values[phi.0]
                    {
                        text.line(1, format_args!("ssa v{} = phi s{}:", phi.0, register.0))?;
                        for input in inputs {
                            text.line(
                                2,
                                format_args!(
                                    "{} -> ssa v{}",
                                    input
                                        .predecessor
                                        .map_or_else(|| "entry".into(), |pc| format!("@{pc:#x}")),
                                    input.value.0
                                ),
                            )?;
                        }
                    }
                }
            }
            for step in &block.steps {
                text.line(1, format_args!("step @{:#x} +{}:", step.address, step.size))?;
                for (index, statement) in step.statements.iter().enumerate() {
                    text.line(2, format_args!("assignment {index}:"))?;
                    match statement {
                        Statement::WriteStorage {
                            storage,
                            version,
                            value,
                        } => {
                            text.region(value, 3)?;
                            text.line(
                                3,
                                format_args!(
                                    "write s{} [{}] = %{}",
                                    storage.0,
                                    version_text(*version),
                                    value.result.0
                                ),
                            )?;
                        }
                        Statement::Store {
                            address,
                            width,
                            value,
                        } => {
                            text.region(address, 3)?;
                            text.line(
                                3,
                                format_args!("check-write{} %{}", width.bits(), address.result.0),
                            )?;
                            text.region(value, 3)?;
                            text.line(
                                3,
                                format_args!(
                                    "store{} %{}, %{}",
                                    width.bits(),
                                    address.result.0,
                                    value.result.0
                                ),
                            )?;
                        }
                    }
                }
            }
            match &block.terminator {
                Terminator::Fallthrough(target) => {
                    text.line(1, format_args!("next @{target:#x}"))?
                }
                Terminator::Jump(target) => text.line(1, format_args!("jump @{target:#x}"))?,
                Terminator::Branch {
                    condition,
                    taken,
                    not_taken,
                } => {
                    text.region(condition, 1)?;
                    text.line(
                        1,
                        format_args!(
                            "branch %{} ? @{taken:#x} : @{not_taken:#x}",
                            condition.result.0
                        ),
                    )?;
                }
                Terminator::Return(value) => {
                    text.region(value, 1)?;
                    text.line(1, format_args!("return %{}", value.result.0))?;
                }
            }
        }
        Ok(text.0)
    }
}

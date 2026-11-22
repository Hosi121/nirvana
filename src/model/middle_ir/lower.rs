//! Reconstruct Low IR separately from the source walker. The effect trace of
//! the resulting expression must equal the explicit region's ordered effects.
use super::*;
use crate::model::ir::{Assignment, Control, Expr, IrInstruction, Place};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Debug, Eq, PartialEq)]
enum Effect {
    Load(ValueId),
    Select(ValueId, Vec<Effect>, Vec<Effect>),
}
#[derive(Clone)]
struct Decoded {
    expr: Expr,
    reads: Vec<(Reg, Option<ssa::ValueId>)>,
    effects: Vec<Effect>,
    nodes: usize,
    depth: usize,
}
impl Decoded {
    fn leaf(expr: Expr) -> Self {
        Self {
            expr,
            reads: Vec::new(),
            effects: Vec::new(),
            nodes: 1,
            depth: 1,
        }
    }
}
struct Lower<'a> {
    function: &'a Function,
    points: BTreeMap<ssa::Site, &'a ssa::PointValues>,
    definitions: BTreeSet<ValueId>,
    work: ssa::Budget,
}
impl Lower<'_> {
    fn spend(&mut self, n: usize) -> Result<(), Error> {
        self.work.spend(n).map_err(Error::Ssa)
    }
    fn storage(&self, id: StorageId) -> Result<Reg, Error> {
        self.function
            .storages
            .get(id.0)
            .copied()
            .ok_or(Error::Invalid("storage ID"))
    }
    fn get(&mut self, values: &BTreeMap<ValueId, Decoded>, id: ValueId) -> Result<Decoded, Error> {
        let value = values
            .get(&id)
            .ok_or(Error::Invalid("value scope or forward reference"))?;
        self.spend(value.nodes)?;
        Ok(value.clone())
    }
    fn region(
        &mut self,
        region: &Region,
        origin: Origin,
        nesting: usize,
    ) -> Result<Decoded, Error> {
        if nesting > ssa::MAX_DEPTH {
            return Err(Error::Limit("region depth"));
        }
        if region.origin != origin {
            return Err(Error::Invalid("region origin"));
        }
        let mut values = BTreeMap::new();
        let mut expected_effects = Vec::new();
        for binding in &region.bindings {
            self.spend(1)?;
            if binding.origin != origin
                || binding.id.0 >= self.function.value_count
                || !self.definitions.insert(binding.id)
            {
                return Err(Error::Invalid("binding origin or duplicate value ID"));
            }
            let decoded = match &binding.operation {
                Operation::Pure(Pure::Constant(n)) => Decoded::leaf(Expr::Const(*n)),
                Operation::ReadStorage { storage, version } => {
                    let reg = self.storage(*storage)?;
                    let valid = self
                        .points
                        .get(&origin.site)
                        .map_or(version.is_none(), |p| {
                            p.reads
                                .iter()
                                .any(|r| r.register == reg && Some(r.value) == *version)
                        });
                    if !valid {
                        return Err(Error::Invalid("storage read version"));
                    }
                    let mut value = Decoded::leaf(Expr::Register(reg));
                    value.reads.push((reg, *version));
                    value
                }
                Operation::Pure(Pure::Unary(op, input)) => {
                    let mut value = self.get(&values, *input)?;
                    value.expr = Expr::unary(*op, value.expr);
                    value.nodes += 1;
                    value.depth += 1;
                    value
                }
                Operation::Pure(Pure::Binary(op, a, b)) => {
                    let a = self.get(&values, *a)?;
                    let b = self.get(&values, *b)?;
                    Decoded {
                        expr: Expr::binary(*op, a.expr, b.expr),
                        reads: [a.reads, b.reads].concat(),
                        effects: [a.effects, b.effects].concat(),
                        nodes: 1 + a.nodes + b.nodes,
                        depth: 1 + a.depth.max(b.depth),
                    }
                }
                Operation::Load { address, width } => {
                    let mut value = self.get(&values, *address)?;
                    value.expr = Expr::load(value.expr, *width);
                    value.effects.push(Effect::Load(binding.id));
                    expected_effects.push(Effect::Load(binding.id));
                    value.nodes += 1;
                    value.depth += 1;
                    value
                }
                Operation::Select {
                    condition,
                    taken,
                    not_taken,
                } => {
                    let mut condition = self.get(&values, *condition)?;
                    let taken = self.region(taken, origin, nesting + 1)?;
                    let not_taken = self.region(not_taken, origin, nesting + 1)?;
                    if !taken.effects.is_empty() || !not_taken.effects.is_empty() {
                        let effect = Effect::Select(binding.id, taken.effects, not_taken.effects);
                        condition.effects.push(effect.clone());
                        expected_effects.push(effect);
                    }
                    Decoded {
                        expr: Expr::select(condition.expr, taken.expr, not_taken.expr),
                        reads: [condition.reads, taken.reads, not_taken.reads].concat(),
                        effects: condition.effects,
                        nodes: 1 + condition.nodes + taken.nodes + not_taken.nodes,
                        depth: 1 + condition.depth.max(taken.depth).max(not_taken.depth),
                    }
                }
            };
            if decoded.depth > ssa::MAX_DEPTH {
                return Err(Error::Limit("expression depth"));
            }
            values.insert(binding.id, decoded);
        }
        let result = self.get(&values, region.result)?;
        if result.effects != expected_effects {
            return Err(Error::Invalid(
                "dropped, duplicated or reordered memory effect",
            ));
        }
        Ok(result)
    }
    fn point(
        &self,
        site: ssa::Site,
        reads: &[(Reg, Option<ssa::ValueId>)],
        version: Option<ssa::ValueId>,
    ) -> Result<(), Error> {
        if let Some(point) = self.points.get(&site) {
            if version != point.definition
                || reads.len() != point.reads.len()
                || reads.iter().zip(&point.reads).any(|((reg, id), expected)| {
                    *reg != expected.register || *id != Some(expected.value)
                })
            {
                return Err(Error::Invalid("SSA definition or read version"));
            }
        } else if version.is_some() || reads.iter().any(|(_, id)| id.is_some()) {
            return Err(Error::Invalid("SSA version on an unreachable site"));
        }
        Ok(())
    }
    fn statement(&mut self, statement: &Statement, site: ssa::Site) -> Result<Assignment, Error> {
        let origin = Origin {
            site,
            operand: Operand::Value,
        };
        match statement {
            Statement::WriteStorage {
                storage,
                version,
                value,
            } => {
                let value = self.region(value, origin, 0)?;
                self.point(site, &value.reads, *version)?;
                Ok(Assignment {
                    destination: self.storage(*storage)?.into(),
                    value: value.expr,
                })
            }
            Statement::Store {
                address,
                width,
                value,
            } => {
                let address = self.region(
                    address,
                    Origin {
                        site,
                        operand: Operand::Address,
                    },
                    0,
                )?;
                let value = self.region(value, origin, 0)?;
                self.point(site, &[address.reads, value.reads].concat(), None)?;
                Ok(Assignment {
                    destination: Place::Memory {
                        address: address.expr,
                        width: *width,
                    },
                    value: value.expr,
                })
            }
        }
    }
}

pub(super) fn program(function: &Function) -> Result<Program, Error> {
    if function.value_count > ssa::MAX_NODES
        || function.blocks.len() > ssa::MAX_BLOCKS
        || function.storages.len() > ssa::MAX_REGISTERS
    {
        return Err(Error::Limit("function size"));
    }
    if function
        .storages
        .iter()
        .enumerate()
        .any(|(index, reg)| reg.0 != index)
    {
        return Err(Error::Invalid("storage mapping"));
    }
    let mut lower = Lower {
        function,
        points: function
            .ssa
            .blocks
            .iter()
            .flat_map(|b| &b.points)
            .map(|p| (p.site, p))
            .collect(),
        definitions: BTreeSet::new(),
        work: ssa::Budget::new(),
    };
    let mut instructions = Vec::new();
    for block in &function.blocks {
        if block.steps.first().map(|s| s.address) != Some(block.address) {
            return Err(Error::Invalid("empty block or block entry"));
        }
        for (index, step) in block.steps.iter().enumerate() {
            let mut assignments = Vec::new();
            for (assignment, statement) in step.statements.iter().enumerate() {
                assignments.push(lower.statement(
                    statement,
                    ssa::Site {
                        instruction: step.address,
                        assignment: Some(assignment),
                    },
                )?);
            }
            let site = ssa::Site {
                instruction: step.address,
                assignment: None,
            };
            let end = step
                .address
                .checked_add(u64::from(step.size))
                .ok_or(Error::Invalid("step end"))?;
            let control = if index + 1 < block.steps.len() {
                if block.steps[index + 1].address != end {
                    return Err(Error::Invalid("noncontiguous steps"));
                }
                lower.point(site, &[], None)?;
                Control::Next
            } else {
                let origin = Origin {
                    site,
                    operand: Operand::Control,
                };
                match &block.terminator {
                    Terminator::Fallthrough(target) => {
                        if *target != end {
                            return Err(Error::Invalid("fallthrough target"));
                        }
                        lower.point(site, &[], None)?;
                        Control::Next
                    }
                    Terminator::Jump(target) => {
                        lower.point(site, &[], None)?;
                        Control::Jump(*target)
                    }
                    Terminator::Branch {
                        condition,
                        taken,
                        not_taken,
                    } => {
                        if *not_taken != end {
                            return Err(Error::Invalid("branch fallthrough"));
                        }
                        let condition = lower.region(condition, origin, 0)?;
                        lower.point(site, &condition.reads, None)?;
                        Control::Branch {
                            condition: condition.expr,
                            target: *taken,
                        }
                    }
                    Terminator::Return(value) => {
                        let value = lower.region(value, origin, 0)?;
                        lower.point(site, &value.reads, None)?;
                        Control::Return(value.expr)
                    }
                }
            };
            instructions.push(IrInstruction {
                address: step.address,
                size: step.size,
                assignments,
                control,
            });
        }
    }
    if lower.definitions.len() != function.value_count {
        return Err(Error::Invalid("value count"));
    }
    let result = Program::new(function.entry, function.storages.len(), instructions)
        .map_err(Error::Program)?;
    let layout: Vec<_> = result
        .cfg()
        .blocks()
        .iter()
        .map(|b| (b.start, b.instructions.len()))
        .collect();
    if layout
        != function
            .blocks
            .iter()
            .map(|b| (b.address, b.steps.len()))
            .collect::<Vec<_>>()
    {
        return Err(Error::Invalid("CFG block layout"));
    }
    ssa::validate(&result, &function.ssa).map_err(Error::Ssa)?;
    Ok(result)
}

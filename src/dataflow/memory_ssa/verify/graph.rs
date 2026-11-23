use super::*;
use crate::dataflow::address_identity::{Operand, PathEdge};
use crate::dataflow::ssa::{Site, ValueId};
use crate::model::ir::{Control, Expr, Place, Width};

fn bounds(candidate: &Analysis, budget: &mut Budget) -> Result<(), ValidationError> {
    budget.retain(candidate.definitions.len())?;
    budget.retain(candidate.blocks.len())?;
    budget.retain(candidate.accesses.len())?;
    let id = |id: MemoryId| {
        if id.0 < candidate.definitions.len() {
            Ok(())
        } else {
            Err(Invalid("memory ID"))
        }
    };
    for definition in &candidate.definitions {
        match definition {
            Definition::Initial => {}
            Definition::Phi { inputs, .. } => {
                budget.retain(inputs.len())?;
                for input in inputs {
                    id(input.memory)?;
                }
            }
            Definition::Store { access, previous } => {
                id(*previous)?;
                if *access >= candidate.accesses.len() {
                    return Err(Invalid("store access ID"));
                }
            }
            Definition::Opaque { previous, .. } => id(*previous)?,
        }
    }
    for block in &candidate.blocks {
        id(block.entry)?;
        id(block.exit)?;
        budget.retain(block.events.len())?;
        for event in &block.events {
            match event {
                Event::Effect(memory) => id(*memory)?,
                Event::Access(access) if *access >= candidate.accesses.len() => {
                    return Err(Invalid("event access ID"));
                }
                Event::Access(_) => {}
            }
        }
    }
    for access in &candidate.accesses {
        id(access.incoming)?;
        if let Some(definition) = access.definition {
            id(definition)?;
        }
        budget.retain(access.source.path.len())?;
        if let Some(address) = &access.address {
            budget.retain(address.terms.len())?;
        }
    }
    Ok(())
}

struct Checker<'a> {
    candidate: &'a Analysis,
    facts: &'a [MemoryAccess],
    forms: &'a [Option<address_identity::ModularAddress>],
    by_site: BTreeMap<Site, Vec<usize>>,
    definitions: Vec<bool>,
    accesses: Vec<bool>,
    budget: Budget,
}
impl Checker<'_> {
    fn claim(&mut self, id: MemoryId) -> Result<(), ValidationError> {
        self.budget.spend(1)?;
        if std::mem::replace(&mut self.definitions[id.0], true) {
            return Err(Invalid("duplicate definition"));
        }
        Ok(())
    }
}

struct BlockCheck<'a, 'b> {
    check: &'a mut Checker<'b>,
    block: &'b Block,
    cursor: usize,
    current: MemoryId,
    site: Site,
    fact_cursor: usize,
}
impl BlockCheck<'_, '_> {
    fn access(
        &mut self,
        operand: Operand,
        path: &[PathEdge],
        kind: AccessKind,
        width: Width,
        result: Option<ValueId>,
    ) -> Result<(), ValidationError> {
        self.check.budget.spend(path.len() + 1)?;
        let Some(Event::Access(index)) = self.block.events.get(self.cursor) else {
            return Err(Invalid("missing ordered access"));
        };
        let access = &self.check.candidate.accesses[*index];
        let expected = self
            .check
            .by_site
            .get(&self.site)
            .and_then(|list| list.get(self.fact_cursor))
            .ok_or(Invalid("missing address access"))?;
        let fact = &self.check.facts[*expected];
        if access.source.site != self.site
            || access.source.operand != operand
            || access.source.path != path
            || access.source.kind != kind
            || access.source.width != width
            || access.source.result != result
            || access.source != *fact
            || access.address != self.check.forms[*expected]
            || access.incoming != self.current
        {
            return Err(Invalid("ordered source access"));
        }
        if std::mem::replace(&mut self.check.accesses[*index], true) {
            return Err(Invalid("duplicate access"));
        }
        match (kind, access.definition) {
            (AccessKind::Read, None) => {}
            (AccessKind::Write, Some(id)) => {
                if self.check.candidate.definitions[id.0]
                    != (Definition::Store {
                        access: *index,
                        previous: self.current,
                    })
                {
                    return Err(Invalid("store commit generation"));
                }
                self.check.claim(id)?;
                self.current = id;
            }
            _ => return Err(Invalid("access definition kind")),
        }
        self.cursor += 1;
        self.fact_cursor += 1;
        Ok(())
    }
    fn child(
        &mut self,
        expression: &Expr,
        operand: Operand,
        path: &mut Vec<PathEdge>,
        edge: PathEdge,
    ) -> Result<(), ValidationError> {
        path.push(edge);
        self.expression(expression, operand, path, None)?;
        path.pop();
        Ok(())
    }
    fn expression(
        &mut self,
        expression: &Expr,
        operand: Operand,
        path: &mut Vec<PathEdge>,
        result: Option<ValueId>,
    ) -> Result<(), ValidationError> {
        self.check.budget.spend(1)?;
        match expression {
            Expr::Const(_) | Expr::Register(_) => {}
            Expr::Unary(_, value) => self.child(value, operand, path, PathEdge::Unary)?,
            Expr::Binary(_, left, right) => {
                self.child(left, operand, path, PathEdge::Left)?;
                self.child(right, operand, path, PathEdge::Right)?;
            }
            Expr::Load { address, width } => {
                self.child(address, operand, path, PathEdge::Address)?;
                self.access(operand, path, AccessKind::Read, *width, result)?;
            }
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => {
                self.child(condition, operand, path, PathEdge::Condition)?;
                self.child(taken, operand, path, PathEdge::Taken)?;
                self.child(not_taken, operand, path, PathEdge::NotTaken)?;
            }
        }
        Ok(())
    }
    fn finish_point(&self) -> Result<(), ValidationError> {
        if self.fact_cursor != self.check.by_site.get(&self.site).map_or(0, Vec::len) {
            return Err(Invalid("extra address access"));
        }
        Ok(())
    }
    fn effect(&mut self, effect: Option<&Effect>) -> Result<(), ValidationError> {
        if let Some(effect) = effect {
            let Some(Event::Effect(id)) = self.block.events.get(self.cursor) else {
                return Err(Invalid("missing opaque effect"));
            };
            if self.check.candidate.definitions[id.0]
                != (Definition::Opaque {
                    effect: *effect,
                    previous: self.current,
                })
            {
                return Err(Invalid("opaque effect generation"));
            }
            self.check.claim(*id)?;
            self.current = *id;
            self.cursor += 1;
        }
        Ok(())
    }
}

pub(super) fn validate(
    source: &Program,
    registers: &SsaFunction,
    candidate: &Analysis,
    effects: &[Effect],
    facts: &[MemoryAccess],
    forms: &[Option<address_identity::ModularAddress>],
) -> Result<GraphEvidence, ValidationError> {
    let mut budget = Budget::new();
    bounds(candidate, &mut budget)?;
    budget.retain(effects.len())?;
    if facts.len() != forms.len() {
        return Err(Invalid("address fact dimensions"));
    }
    let mut by_site = BTreeMap::<Site, Vec<usize>>::new();
    for (index, fact) in facts.iter().enumerate() {
        budget.spend(fact.path.len() + 1)?;
        by_site.entry(fact.site).or_default().push(index);
    }
    let cfg = source.cfg();
    let reachable = cfg.reachable_blocks();
    if candidate.blocks.len() != reachable.len() {
        return Err(Invalid("reachable block count"));
    }
    let mut by_block = BTreeMap::new();
    for block in &candidate.blocks {
        if by_block.insert(block.start, block).is_some() {
            return Err(Invalid("duplicate block"));
        }
    }
    let mut effect_map = BTreeMap::new();
    for effect in effects {
        if source
            .instructions()
            .binary_search_by_key(&effect.instruction, |i| i.address)
            .is_err()
            || effect_map
                .insert((effect.instruction, effect.phase), effect)
                .is_some()
        {
            return Err(Invalid("effect source"));
        }
    }
    let initial: Vec<_> = candidate
        .definitions
        .iter()
        .enumerate()
        .filter(|(_, d)| matches!(d, Definition::Initial))
        .map(|(n, _)| MemoryId(n))
        .collect();
    if initial.len() != 1 {
        return Err(Invalid("initial definition count"));
    }
    let points: BTreeMap<_, _> = registers
        .blocks
        .iter()
        .flat_map(|b| &b.points)
        .map(|p| (p.site, p))
        .collect();
    let mut check = Checker {
        candidate,
        facts,
        forms,
        by_site,
        definitions: vec![false; candidate.definitions.len()],
        accesses: vec![false; candidate.accesses.len()],
        budget,
    };
    check.claim(initial[0])?;
    let mut phi_inputs = 0;
    for id in &reachable {
        let source_block = cfg.block(*id);
        let block = by_block
            .get(&source_block.start)
            .ok_or(Invalid("block source"))?;
        let Definition::Phi {
            block: owner,
            inputs,
        } = &candidate.definitions[block.entry.0]
        else {
            return Err(Invalid("block entry phi"));
        };
        if *owner != source_block.start {
            return Err(Invalid("phi owner"));
        }
        check.claim(block.entry)?;
        let mut expected = BTreeMap::new();
        if *id == cfg.entry() {
            expected.insert(None, initial[0]);
        }
        for pred in &source_block.predecessors {
            if reachable.contains(pred) {
                let start = cfg.block(*pred).start;
                expected.insert(
                    Some(start),
                    by_block.get(&start).ok_or(Invalid("phi predecessor"))?.exit,
                );
            }
        }
        if inputs.len() != expected.len() {
            return Err(Invalid("phi predecessor coverage"));
        }
        for input in inputs {
            check.budget.spend(1)?;
            if expected.remove(&input.predecessor) != Some(input.memory) {
                return Err(Invalid("phi incoming generation"));
            }
        }
        phi_inputs += inputs.len();
        let mut walk = BlockCheck {
            check: &mut check,
            block,
            cursor: 0,
            current: block.entry,
            site: Site {
                instruction: 0,
                assignment: None,
            },
            fact_cursor: 0,
        };
        for instruction in &source.instructions()[source_block.instructions.clone()] {
            walk.effect(
                effect_map
                    .get(&(instruction.address, Phase::Before))
                    .copied(),
            )?;
            for (index, assignment) in instruction.assignments.iter().enumerate() {
                walk.site = Site {
                    instruction: instruction.address,
                    assignment: Some(index),
                };
                walk.fact_cursor = 0;
                let mut path = Vec::new();
                if let Place::Memory { address, .. } = &assignment.destination {
                    walk.child(address, Operand::Destination, &mut path, PathEdge::Address)?;
                }
                let result = if matches!(assignment.destination, Place::Register(_))
                    && matches!(assignment.value, Expr::Load { .. })
                {
                    points
                        .get(&walk.site)
                        .ok_or(Invalid("register assignment site"))?
                        .definition
                } else {
                    None
                };
                walk.expression(&assignment.value, Operand::Value, &mut path, result)?;
                if let Place::Memory { width, .. } = assignment.destination {
                    walk.access(Operand::Destination, &[], AccessKind::Write, width, None)?;
                }
                walk.finish_point()?;
            }
            if let Control::Branch { condition, .. } | Control::Return(condition) =
                &instruction.control
            {
                walk.site = Site {
                    instruction: instruction.address,
                    assignment: None,
                };
                walk.fact_cursor = 0;
                walk.expression(condition, Operand::Control, &mut Vec::new(), None)?;
                walk.finish_point()?;
            }
            walk.effect(
                effect_map
                    .get(&(instruction.address, Phase::After))
                    .copied(),
            )?;
        }
        if walk.cursor != block.events.len() || walk.current != block.exit {
            return Err(Invalid("block exit or extra events"));
        }
    }
    if check.definitions.contains(&false) || check.accesses.contains(&false) {
        return Err(Invalid("unclaimed graph member"));
    }
    Ok(GraphEvidence {
        blocks: candidate.blocks.len(),
        definitions: candidate.definitions.len(),
        accesses: candidate.accesses.len(),
        phi_inputs,
        opaque_effects: candidate
            .definitions
            .iter()
            .filter(|d| matches!(d, Definition::Opaque { .. }))
            .count(),
    })
}

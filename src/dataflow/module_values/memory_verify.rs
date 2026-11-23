//! Check the module adapter's declarations against original instructions.
//!
//! Closed footprints are contracts supplied by call_footprint; unknown calls
//! clobber every guest register. The core MemorySSA checker checks graph/query
//! evidence. Checked module execution owns faults and partial REP progress.

use std::collections::{BTreeMap, BTreeSet};

use super::{PointRole, call_footprint};
use crate::binary::x86::{DF, RAX, RCX, RDI, RDX, RSI, RSP};
use crate::dataflow::memory_ssa::{
    Analysis, Definition, Effect, EffectKind, Phase, ValidationError,
};
use crate::dataflow::ssa::{self, Site};
use crate::model::ir::{Assignment, Control, Expr, IrInstruction, Place, Program, Reg, Width};
use crate::model::module_ir::{self, Instruction, Target};
use ValidationError::{Invalid, Unavailable};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Evidence {
    pub instructions: usize,
    pub assignments: usize,
    pub opaque_outputs: usize,
    pub declared_effects: usize,
    pub reachable_effects: usize,
}

pub(super) fn validate(
    source: &[Instruction],
    events: &Program,
    roles: &BTreeMap<Site, PointRole>,
    summaries: &call_footprint::Analysis,
    effects: &[Effect],
    opaque: &BTreeSet<Site>,
    candidate: &Analysis,
) -> Result<Evidence, ValidationError> {
    let guests = module_ir::REGISTER_COUNT;
    if source.len() > ssa::MAX_INSTRUCTIONS
        || roles.len() > ssa::MAX_ASSIGNMENTS
        || opaque.len() > ssa::MAX_ASSIGNMENTS
        || effects.len() > ssa::MAX_INSTRUCTIONS * 2
    {
        return Err(Unavailable("module projection size"));
    }
    if events.register_count() != guests + 1
        || source.len() != events.instructions().len()
        || source
            .first()
            .is_none_or(|i| i.address() != events.cfg().block(events.cfg().entry()).start)
    {
        return Err(Invalid("module projection shape"));
    }
    bound_source(source, guests)?;
    let mut declared = BTreeMap::new();
    for effect in effects {
        if declared
            .insert((effect.instruction, effect.phase), effect.kind)
            .is_some()
        {
            return Err(Invalid("duplicate module effect"));
        }
    }
    let all: Vec<_> = (0..guests).map(Reg).collect();
    let mut assignments = 0;
    let mut outputs = 0;
    for (original, projected) in source.iter().zip(events.instructions()) {
        if original.address() != projected.address || original.size() != projected.size {
            return Err(Invalid("module instruction identity"));
        }
        let mut check = Points {
            instruction: projected,
            roles,
            opaque,
            next: 0,
            outputs: 0,
        };
        let control = match original {
            Instruction::Core(i) => {
                check.copies(&i.assignments, false)?;
                &i.control
            }
            Instruction::Vector(i) => {
                if let Some(memory) = &i.memory {
                    check.read(&memory.address, PointRole::VectorGuard)?;
                }
                check.copies(&i.assignments, true)?;
                &Control::Next
            }
            Instruction::Divide { source, width, .. } => {
                check.read(source, PointRole::DivideSource)?;
                let registers: &[Reg] = if *width == Width::U8 {
                    &[Reg(RAX)]
                } else {
                    &[Reg(RAX), Reg(RDX)]
                };
                check.inputs(registers)?;
                check.outputs(registers)?;
                &Control::Jump(continuation(original)?)
            }
            Instruction::StoreString { repeat, .. } | Instruction::MoveString { repeat, .. } => {
                let copy = matches!(original, Instruction::MoveString { .. });
                check.inputs(&[Reg(if copy { RSI } else { RAX }), Reg(RDI), Reg(DF)])?;
                if *repeat {
                    check.inputs(&[Reg(RCX)])?;
                }
                check.outputs(&[Reg(RDI)])?;
                if copy {
                    check.outputs(&[Reg(RSI)])?;
                }
                if *repeat {
                    check.outputs(&[Reg(RCX)])?;
                }
                require_effect(
                    &mut declared,
                    projected.address,
                    Phase::After,
                    if copy {
                        EffectKind::StringMove
                    } else {
                        EffectKind::StringStore
                    },
                )?;
                &Control::Jump(continuation(original)?)
            }
            Instruction::Transfer { target, link, .. } => {
                match target {
                    Target::Value(expression) => check.read(expression, PointRole::Target)?,
                    Target::Plt(slot) => check.read(
                        &Expr::load(Expr::Const(*slot), Width::U64),
                        PointRole::Target,
                    )?,
                }
                if let Some(next) = link {
                    // A PLT load observes RAM after pushing the return address.
                    // An ordinary target expression observes RAM before it.
                    if matches!(target, Target::Plt(_)) {
                        require_effect(
                            &mut declared,
                            projected.address,
                            Phase::Before,
                            EffectKind::CallStack,
                        )?;
                    }
                    require_effect(
                        &mut declared,
                        projected.address,
                        Phase::After,
                        EffectKind::Call,
                    )?;
                    let summary = match target {
                        Target::Value(Expr::Const(callee)) => {
                            summaries.at(*callee).filter(|s| s.closed)
                        }
                        _ => None,
                    };
                    if let Some(summary) = summary {
                        check_footprint(summary, guests)?;
                        check.inputs(&summary.reads)?;
                        check.outputs(&summary.clobbers)?;
                    } else {
                        check.inputs(&all)?;
                        check.outputs(&all)?;
                    }
                    &Control::Jump(*next)
                } else {
                    check.inputs(&all)?;
                    &Control::Return(Expr::Const(0))
                }
            }
            Instruction::Return { .. } => {
                check.read(
                    &Expr::load(Expr::Register(Reg(RSP)), Width::U64),
                    PointRole::Target,
                )?;
                check.inputs(&all)?;
                &Control::Return(Expr::Const(0))
            }
        };
        if &projected.control != control || check.next != projected.assignments.len() {
            return Err(Invalid(
                "module projection continuation or extra assignment",
            ));
        }
        assignments += check.next;
        outputs += check.outputs;
    }
    if assignments != roles.len() || outputs != opaque.len() || !declared.is_empty() {
        return Err(Invalid("extra module role, opaque definition or effect"));
    }
    let reachable_effects = retained_effects(events, effects, candidate)?;
    Ok(Evidence {
        instructions: source.len(),
        assignments,
        opaque_outputs: outputs,
        declared_effects: effects.len(),
        reachable_effects,
    })
}

fn require_effect(
    declared: &mut BTreeMap<(u64, Phase), EffectKind>,
    address: u64,
    phase: Phase,
    kind: EffectKind,
) -> Result<(), ValidationError> {
    if declared.remove(&(address, phase)) != Some(kind) {
        return Err(Invalid("module source effect"));
    }
    Ok(())
}

fn continuation(instruction: &Instruction) -> Result<u64, ValidationError> {
    instruction
        .address()
        .checked_add(u64::from(instruction.size()))
        .ok_or(Invalid("module continuation overflow"))
}

struct Points<'a> {
    instruction: &'a IrInstruction,
    roles: &'a BTreeMap<Site, PointRole>,
    opaque: &'a BTreeSet<Site>,
    next: usize,
    outputs: usize,
}
impl Points<'_> {
    fn take(&mut self, role: PointRole) -> Result<&Assignment, ValidationError> {
        let site = Site {
            instruction: self.instruction.address,
            assignment: Some(self.next),
        };
        let assignment = self
            .instruction
            .assignments
            .get(self.next)
            .ok_or(Invalid("missing module projection assignment"))?;
        if self.roles.get(&site) != Some(&role)
            || self.opaque.contains(&site) != matches!(role, PointRole::OpaqueOutput { .. })
        {
            return Err(Invalid("module projection role or opaque definition"));
        }
        self.next += 1;
        Ok(assignment)
    }
    fn read(&mut self, value: &Expr, role: PointRole) -> Result<(), ValidationError> {
        let assignment = self.take(role)?;
        if assignment.destination != Place::Register(Reg(module_ir::REGISTER_COUNT))
            || &assignment.value != value
        {
            return Err(Invalid("module projection operand"));
        }
        Ok(())
    }
    fn inputs(&mut self, registers: &[Reg]) -> Result<(), ValidationError> {
        for &register in registers {
            self.read(&Expr::Register(register), PointRole::Input { register })?;
        }
        Ok(())
    }
    fn outputs(&mut self, registers: &[Reg]) -> Result<(), ValidationError> {
        for &register in registers {
            let assignment = self.take(PointRole::OpaqueOutput { register })?;
            if assignment.destination != Place::Register(register)
                || assignment.value != Expr::Const(0)
            {
                return Err(Invalid("module opaque register output"));
            }
            self.outputs += 1;
        }
        Ok(())
    }
    fn copies(&mut self, originals: &[Assignment], vector: bool) -> Result<(), ValidationError> {
        for (original, assignment) in originals.iter().enumerate() {
            let role = if vector {
                PointRole::VectorAssignment { original }
            } else {
                PointRole::Assignment { original }
            };
            if self.take(role)? != assignment {
                return Err(Invalid("module source assignment"));
            }
        }
        Ok(())
    }
}

fn check_footprint(
    summary: &call_footprint::FunctionSummary,
    guests: usize,
) -> Result<(), ValidationError> {
    for registers in [&summary.reads, &summary.clobbers, &summary.preserved] {
        if registers.len() > guests
            || registers.iter().any(|r| r.0 >= guests)
            || registers.windows(2).any(|w| w[0].0 >= w[1].0)
        {
            return Err(Invalid("module closed register footprint"));
        }
    }
    if (0..guests).any(|r| {
        summary.clobbers.binary_search_by_key(&r, |r| r.0).is_ok()
            == summary.preserved.binary_search_by_key(&r, |r| r.0).is_ok()
    }) {
        return Err(Invalid("module closed footprint partition"));
    }
    Ok(())
}

fn retained_effects(
    events: &Program,
    effects: &[Effect],
    candidate: &Analysis,
) -> Result<usize, ValidationError> {
    let cfg = events.cfg();
    let mut reachable = BTreeSet::new();
    for id in cfg.reachable_blocks() {
        reachable.extend(
            events.instructions()[cfg.block(id).instructions.clone()]
                .iter()
                .map(|i| i.address),
        );
    }
    let mut remaining: BTreeMap<_, _> = effects
        .iter()
        .filter(|e| reachable.contains(&e.instruction))
        .map(|e| ((e.instruction, e.phase), e.kind))
        .collect();
    let count = remaining.len();
    for definition in candidate.definitions() {
        if let Definition::Opaque { effect, .. } = definition {
            require_effect(
                &mut remaining,
                effect.instruction,
                effect.phase,
                effect.kind,
            )?;
        }
    }
    if !remaining.is_empty() {
        return Err(Invalid("missing reachable module effect"));
    }
    Ok(count)
}

// Bound original syntax before recursive equality comparisons. This pass is
// independent of projection generation and preserves unavailable vs invalid.
fn bound_source(source: &[Instruction], guests: usize) -> Result<(), ValidationError> {
    let mut nodes = 0usize;
    for instruction in source {
        let mut pending = Vec::new();
        let mut assignments: &[Assignment] = &[];
        match instruction {
            Instruction::Core(i) => {
                assignments = &i.assignments;
                if let Control::Branch { condition, .. } | Control::Return(condition) = &i.control {
                    pending.push((condition, 1));
                }
            }
            Instruction::Vector(i) => {
                assignments = &i.assignments;
                if let Some(memory) = &i.memory {
                    pending.push((&memory.address, 1));
                }
            }
            Instruction::Divide { source, .. }
            | Instruction::Transfer {
                target: Target::Value(source),
                ..
            } => pending.push((source, 1)),
            _ => {}
        }
        if assignments.len() > ssa::MAX_ASSIGNMENTS {
            return Err(Unavailable("module source assignments"));
        }
        for assignment in assignments {
            match &assignment.destination {
                Place::Register(r) if r.0 >= guests => {
                    return Err(Invalid("module source register"));
                }
                Place::Memory { address, .. } => pending.push((address, 1)),
                _ => {}
            }
            pending.push((&assignment.value, 1));
        }
        while let Some((expression, depth)) = pending.pop() {
            nodes += 1;
            if nodes > ssa::MAX_NODES || depth > ssa::MAX_DEPTH {
                return Err(Unavailable("module source expression size"));
            }
            match expression {
                Expr::Register(r) if r.0 >= guests => {
                    return Err(Invalid("module source register"));
                }
                Expr::Unary(_, e) | Expr::Load { address: e, .. } => pending.push((e, depth + 1)),
                Expr::Binary(_, a, b) => {
                    pending.push((a, depth + 1));
                    pending.push((b, depth + 1));
                }
                Expr::Select {
                    condition,
                    taken,
                    not_taken,
                } => {
                    pending.push((condition, depth + 1));
                    pending.push((taken, depth + 1));
                    pending.push((not_taken, depth + 1));
                }
                _ => {}
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests;

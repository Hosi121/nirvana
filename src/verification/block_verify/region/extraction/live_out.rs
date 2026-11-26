//! Source-bound continuation interfaces with an independent read-before-write check.
use super::*;
use crate::dataflow::{ssa, value_liveness};
use crate::model::ir::Place;
use crate::verification::block_verify::region::ReturnOutputs;

pub const MODEL_ID: &str = "checked-continuation-live-outputs-v1";
pub const MAX_CONTINUATIONS: usize = 16;
const MAX_CHECK_WORK: usize = 8_000_000;

/// Normal continuation observations for this exact source and terminal mapping.
/// Source registers are retained where a later instruction can read their old
/// value. The captured function result is observed at every normal exit. Full
/// register snapshots at faults, PC and trace retain their separate contracts.
#[derive(Clone, Debug)]
pub struct ContinuationOutputs {
    source: Program,
    stops: Vec<u64>,
    returns: Vec<ReturnOutputs>,
}
impl ContinuationOutputs {
    pub fn returns(&self) -> &[ReturnOutputs] {
        &self.returns
    }
    pub fn matches(&self, region: &Region) -> bool {
        self.stops == region.stops && region.belongs_to(&self.source)
    }
    /// Independently certify that every omitted source value is overwritten
    /// before its first possible use on every continuation path.
    pub fn validate(&self) -> Result<(), ExtractionError> {
        let successors = shape::bounded_successors(&self.source)?;
        let capture = Reg(self.source.register_count());
        if self.stops.len() > MAX_CONTINUATIONS
            || self.returns.len() != self.stops.len() + 1
            || self.stops.windows(2).any(|pair| pair[0] >= pair[1])
        {
            return Err(ExtractionError::LiveOut);
        }
        let mut work = MAX_CHECK_WORK;
        for (tag, &pc) in self.stops.iter().enumerate() {
            let row = &self.returns[tag];
            if self.source.cfg().block_at(pc).is_none()
                || row.value != tag as u64
                || row.registers.len() > MAX_REGISTERS
                || row.registers.windows(2).any(|pair| pair[0].0 >= pair[1].0)
                || row.registers.iter().any(|reg| reg.0 > capture.0)
                || !row.registers.contains(&capture)
            {
                return Err(ExtractionError::LiveOut);
            }
            for register in 0..capture.0 {
                if !row.registers.contains(&Reg(register))
                    && reads_before_write(&self.source, &successors, pc, Reg(register), &mut work)?
                {
                    return Err(ExtractionError::LiveOut);
                }
            }
        }
        let last = &self.returns[self.stops.len()];
        if last.value != self.stops.len() as u64 || last.registers != [capture] {
            return Err(ExtractionError::LiveOut);
        }
        Ok(())
    }
}

/// Build a fresh SSA entry at each continuation, so even source blocks that are
/// unreachable from the original entry receive an arbitrary-input interface.
/// SSA/liveness limits and the separate read-check work bound decline atomically.
pub fn derive(region: &Region) -> Result<ContinuationOutputs, ExtractionError> {
    region.validate()?;
    if region.stops.len() > MAX_CONTINUATIONS {
        return Err(Error::Limit.into());
    }
    let source = &region.source;
    let capture = region.return_register();
    let mut returns = Vec::new();
    for (tag, &pc) in region.stops.iter().enumerate() {
        let reentered = Program::new(pc, source.register_count(), source.instructions().to_vec())
            .map_err(|_| ExtractionError::LiveOut)?;
        let graph = ssa::SsaFunction::build(&reentered).ok_or(ExtractionError::LiveOut)?;
        let liveness =
            value_liveness::analyze(&reentered, &graph).map_err(|_| ExtractionError::LiveOut)?;
        let entry = liveness
            .edges
            .iter()
            .find(|edge| edge.from.is_none() && edge.to == pc)
            .ok_or(ExtractionError::LiveOut)?;
        let mut registers = BTreeSet::new();
        for value in &entry.live {
            let register = match &graph.values[value.0] {
                ssa::Definition::Initial { register }
                | ssa::Definition::Assignment { register, .. }
                | ssa::Definition::Phi { register, .. } => *register,
            };
            registers.insert(register.0);
        }
        registers.insert(capture.0);
        returns.push(ReturnOutputs {
            value: tag as u64,
            registers: registers.into_iter().map(Reg).collect(),
        });
    }
    returns.push(ReturnOutputs {
        value: region.stops.len() as u64,
        registers: vec![capture],
    });
    let result = ContinuationOutputs {
        source: source.clone(),
        stops: region.stops.clone(),
        returns,
    };
    result.validate()?;
    Ok(result)
}

fn spend(work: &mut usize) -> Result<(), ExtractionError> {
    *work = work.checked_sub(1).ok_or(Error::Limit)?;
    Ok(())
}

fn reads(expression: &Expr, register: Reg, work: &mut usize) -> Result<bool, ExtractionError> {
    let mut pending = vec![expression];
    while let Some(expression) = pending.pop() {
        spend(work)?;
        match expression {
            Expr::Register(value) if *value == register => return Ok(true),
            Expr::Unary(_, value) | Expr::Load { address: value, .. } => pending.push(value),
            Expr::Binary(_, left, right) => pending.extend([&**left, &**right]),
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => pending.extend([&**condition, &**taken, &**not_taken]),
            _ => {}
        }
    }
    Ok(false)
}

fn reads_before_write(
    source: &Program,
    successors: &BTreeMap<u64, Vec<u64>>,
    entry: u64,
    register: Reg,
    work: &mut usize,
) -> Result<bool, ExtractionError> {
    let instructions: BTreeMap<_, _> = source
        .instructions()
        .iter()
        .map(|i| (i.address, i))
        .collect();
    let mut pending = vec![entry];
    let mut visited = BTreeSet::new();
    'path: while let Some(pc) = pending.pop() {
        spend(work)?;
        if !visited.insert(pc) {
            continue;
        }
        let instruction = instructions[&pc];
        for assignment in &instruction.assignments {
            spend(work)?;
            if matches!((&assignment.destination, &assignment.value), (Place::Register(d), Expr::Register(s)) if d == s)
            {
                continue;
            }
            if let Place::Memory { address, .. } = &assignment.destination
                && reads(address, register, work)?
            {
                return Ok(true);
            }
            if reads(&assignment.value, register, work)? {
                return Ok(true);
            }
            if assignment.destination == Place::Register(register) {
                continue 'path;
            }
        }
        let expression = match &instruction.control {
            Control::Return(value)
            | Control::Branch {
                condition: value, ..
            } => Some(value),
            _ => None,
        };
        if let Some(expression) = expression
            && reads(expression, register, work)?
        {
            return Ok(true);
        }
        pending.extend(successors[&pc].iter().copied());
    }
    Ok(false)
}

#[cfg(test)]
mod tests;

//! Cut a source CFG at explicit block-entry continuations for DAG validation.
//!
//! The source register namespace and every memory operation are retained. The
//! additional register captures actual function return values; the DAG Return
//! identifies a continuation or function exit. PC, trace and instruction-budget
//! observations remain outside this entry/exit contract.
use super::{Error, MAX_REGISTERS, shape};
use crate::dataflow::value_width::{self, ValueWidths};
use crate::model::ir::{Assignment, BinaryOp, Control, Expr, IrInstruction, Program, Reg};
use std::collections::{BTreeMap, BTreeSet};

mod check;
pub mod repeat;
#[cfg(test)]
mod tests;

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ExtractionError {
    Region(Error),
    Boundary,
    EntryFacts,
    Projection,
}
impl From<Error> for ExtractionError {
    fn from(error: Error) -> Self {
        Self::Region(error)
    }
}
impl std::fmt::Display for ExtractionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "region extraction: {self:?}")
    }
}
impl std::error::Error for ExtractionError {}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Exit {
    ContinueAt(u64),
    FunctionReturn,
}

/// A checked projection bound to its retained immutable source and entry facts.
/// Masks in the prefix expose only source-validated bit caps. Equivalence for
/// the masked DAG applies to source states that satisfy those entry facts.
#[derive(Clone, Debug)]
pub struct Region {
    source: Program,
    program: Program,
    entry: u64,
    stops: Vec<u64>,
    caps: Vec<u8>,
    widths: Option<ValueWidths>,
    body: BTreeMap<u64, u64>,
    terminals: BTreeMap<u64, u64>,
}
impl Region {
    pub fn program(&self) -> &Program {
        &self.program
    }
    pub fn source_entry(&self) -> u64 {
        self.entry
    }
    pub fn continuations(&self) -> &[u64] {
        &self.stops
    }
    pub fn source_to_region(&self) -> &BTreeMap<u64, u64> {
        &self.body
    }
    pub fn input_bit_caps(&self) -> &[u8] {
        &self.caps
    }
    pub fn return_register(&self) -> Reg {
        Reg(self.source.register_count())
    }
    pub fn exit(&self, tag: u64) -> Option<Exit> {
        if tag == self.stops.len() as u64 {
            Some(Exit::FunctionReturn)
        } else {
            self.stops
                .get(usize::try_from(tag).ok()?)
                .copied()
                .map(Exit::ContinueAt)
        }
    }
    /// Independently check projection rules, source-bound facts and closure.
    pub fn validate(&self) -> Result<(), ExtractionError> {
        check::validate(self)
    }
    /// Check identity against the exact original Program, including unreachable
    /// instructions and register count, before reusing this projection elsewhere.
    pub fn belongs_to(&self, source: &Program) -> bool {
        self.source.register_count() == source.register_count()
            && self.source.cfg().block(self.source.cfg().entry()).start
                == source.cfg().block(source.cfg().entry()).start
            && self.source.instructions() == source.instructions()
    }
}

/// Extract execution from `entry` until the first arrival at a stop or Return.
/// Entry and stops must be source basic-block starts. A backedge to entry is cut
/// only when entry is explicitly among the stops. Any remaining cycle refuses.
/// Optional ValueWidths facts are revalidated against this exact source.
pub fn extract(
    source: &Program,
    entry: u64,
    stops: &[u64],
    widths: Option<&ValueWidths>,
) -> Result<Region, ExtractionError> {
    let successors = shape::bounded_successors(source)?;
    if source.register_count() >= MAX_REGISTERS {
        return Err(Error::Limit.into());
    }
    let entry_id = source
        .cfg()
        .block_at(entry)
        .ok_or(ExtractionError::Boundary)?;
    let stops: Vec<_> = stops
        .iter()
        .copied()
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect();
    if stops.iter().any(|&pc| source.cfg().block_at(pc).is_none()) {
        return Err(ExtractionError::Boundary);
    }
    let caps = match widths {
        None => vec![64; source.register_count()],
        Some(facts) => {
            let storage = facts.widths().ok_or(ExtractionError::EntryFacts)?;
            let rows = facts.incoming().ok_or(ExtractionError::EntryFacts)?;
            value_width::validate(source, storage, rows)
                .map_err(|_| ExtractionError::EntryFacts)?;
            rows[entry_id.index()]
                .clone()
                .ok_or(ExtractionError::EntryFacts)?
        }
    };
    let mut selected = BTreeSet::new();
    let mut pending = vec![entry];
    while let Some(pc) = pending.pop() {
        if selected.insert(pc) {
            pending.extend(
                successors[&pc]
                    .iter()
                    .filter(|pc| !stops.contains(pc))
                    .copied(),
            );
        }
    }
    let body: BTreeMap<_, _> = selected
        .iter()
        .enumerate()
        .map(|(n, &pc)| (pc, 2 + n as u64 * 2))
        .collect();
    let terminals: BTreeMap<_, _> = stops
        .iter()
        .enumerate()
        .map(|(n, &pc)| (pc, 2 + (body.len() + n) as u64 * 2))
        .collect();
    let route = |pc: u64| {
        terminals
            .get(&pc)
            .or_else(|| body.get(&pc))
            .copied()
            .ok_or(ExtractionError::Projection)
    };
    let mut prefix = vec![Assignment {
        destination: Reg(source.register_count()).into(),
        value: Expr::Const(0),
    }];
    for (reg, &bits) in caps.iter().enumerate() {
        if bits < 64 {
            prefix.push(Assignment {
                destination: Reg(reg).into(),
                value: Expr::binary(
                    BinaryOp::And,
                    Expr::Register(Reg(reg)),
                    Expr::Const((1u64 << bits) - 1),
                ),
            });
        }
    }
    let mut instructions = vec![IrInstruction {
        address: 0,
        size: 1,
        assignments: prefix,
        control: Control::Jump(body[&entry]),
    }];
    for original in source
        .instructions()
        .iter()
        .filter(|i| selected.contains(&i.address))
    {
        let address = body[&original.address];
        let mut assignments = original.assignments.clone();
        let control = match &original.control {
            Control::Next => Control::Jump(route(original.address + u64::from(original.size))?),
            Control::Jump(to) => Control::Jump(route(*to)?),
            Control::Branch { condition, target } => {
                instructions.push(IrInstruction {
                    address: address + 1,
                    size: 1,
                    assignments: vec![],
                    control: Control::Jump(route(original.address + u64::from(original.size))?),
                });
                Control::Branch {
                    condition: condition.clone(),
                    target: route(*target)?,
                }
            }
            Control::Return(value) => {
                assignments.push(Assignment {
                    destination: Reg(source.register_count()).into(),
                    value: value.clone(),
                });
                Control::Return(Expr::Const(stops.len() as u64))
            }
        };
        instructions.push(IrInstruction {
            address,
            size: 1,
            assignments,
            control,
        });
    }
    for (tag, stop) in stops.iter().enumerate() {
        instructions.push(IrInstruction {
            address: terminals[stop],
            size: 1,
            assignments: vec![],
            control: Control::Return(Expr::Const(tag as u64)),
        });
    }
    let program = Program::new(0, source.register_count() + 1, instructions)
        .map_err(|_| ExtractionError::Projection)?;
    shape::inspect(&program)?;
    let region = Region {
        source: source.clone(),
        program,
        entry,
        stops,
        caps,
        widths: widths.cloned(),
        body,
        terminals,
    };
    region.validate()?;
    Ok(region)
}

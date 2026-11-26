//! Memory-aware translation validation for closed acyclic IR regions.
//!
//! Compare arbitrary shared inputs, all RAM, return values, declared live-out
//! registers and the first fault. Instruction traces and budget stops retain
//! their separate executable contracts. Loop unfolding needs its own completion
//! certificate before a cyclic candidate can use this DAG boundary.
use super::*;
use crate::model::ir::{RunReport, RunStatus};

mod encode;
pub mod extraction;
mod shape;
#[cfg(test)]
mod tests;

pub const MODEL_ID: &str = "checked-memory-dag-region-v1";
pub const MAX_REGISTERS: usize = 128;
pub const MAX_INSTRUCTIONS: usize = 128;
const MAX_EXPRESSIONS: usize = 65_536;
const MAX_DEPTH: usize = 128;
const MAX_SCRIPT: usize = 4 * 1024 * 1024;

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Error {
    Limit,
    OpenEdge,
    Cycle,
    BoundaryMapping,
    Encoding(UnknownReason),
}
impl From<UnknownReason> for Error {
    fn from(reason: UnknownReason) -> Self {
        if reason == UnknownReason::ResourceLimit {
            Self::Limit
        } else {
            Self::Encoding(reason)
        }
    }
}
impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "region validation: {self:?}")
    }
}
impl std::error::Error for Error {}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Counterexample {
    pub before_registers: Vec<u64>,
    pub after_registers: Vec<u64>,
    pub memory_base: u64,
    pub memory: Vec<u8>,
    pub before: RunReport,
    pub after: RunReport,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Verdict {
    EquivalentUnderModel,
    Counterexample(Box<Counterexample>),
    Unknown(UnknownReason),
}

#[derive(Clone, Debug)]
pub struct Query {
    script: String,
    names: Vec<String>,
    samples: Vec<(String, String)>,
    before: Program,
    after: Program,
    outputs: Vec<Reg>,
    input_names: Vec<String>,
    candidate_names: Vec<String>,
}

/// Check both entry-reachable DAGs under the declared shared/live-out mapping.
/// Source bounds and expression depth are checked before recursive clones.
/// Every direct edge is closed within its Program; normal exits are Returns.
/// Unshared initial registers vary independently on the two sides.
pub fn query(
    before: &Program,
    after: &Program,
    shared: &[Reg],
    outputs: &[Reg],
) -> Result<Query, Error> {
    let left_order = shape::inspect(before)?;
    let right_order = shape::inspect(after)?;
    let common = before.register_count().min(after.register_count());
    if shared.len() > MAX_REGISTERS
        || outputs.len() > MAX_REGISTERS
        || shared.iter().chain(outputs).any(|r| r.0 >= common)
    {
        return Err(Error::BoundaryMapping);
    }
    let shared: Registers = shared.iter().map(|r| r.0).collect();
    let mut builder = Builder {
        declarations: BTreeMap::new(),
        definitions: Vec::new(),
        samples: Vec::new(),
        visits: 0,
        interning: Some(BTreeMap::new()),
    };
    builder.declare("initial_memory", ARRAY);
    builder.declare("base", WORD);
    builder.declare("size", WORD);
    builder.declare("memory_witness", WORD);
    let (left, left_complete, input_names) =
        encode::dag(&mut builder, before, &left_order, &shared, "left")?;
    let (right, right_complete, candidate_names) =
        encode::dag(&mut builder, after, &right_order, &shared, "right")?;
    builder.sample("memory_witness".into())?;
    let mut normal = vec![
        format!("(distinct {} {})", left.exit_kind, right.exit_kind),
        format!("(distinct {} {})", left.exit_value, right.exit_value),
    ];
    normal.extend(outputs.iter().map(|r| {
        format!(
            "(distinct {} {})",
            left.registers[r.0], right.registers[r.0]
        )
    }));
    let different = format!(
        "(or (not {left_complete}) (not {right_complete}) (xor {} {}) (and (not {}) (not {}) (or (distinct {} {}) (distinct {} {}) (distinct {} {}))) (distinct (select {} memory_witness) (select {} memory_witness)) (and {} {} (or {})))",
        left.alive,
        right.alive,
        left.alive,
        right.alive,
        left.fault_access,
        right.fault_access,
        left.fault_address,
        right.fault_address,
        left.fault_width,
        right.fault_width,
        left.memory,
        right.memory,
        left.alive,
        right.alive,
        normal.join(" ")
    );
    let mut script = format!(
        "; Nirvana {MODEL_ID}; arbitrary input words, base, size and RAM.\n(set-logic QF_AUFBV)\n"
    );
    for (name, sort) in &builder.declarations {
        script.push_str(&format!("(declare-fun {name} () {sort})\n"));
    }
    for definition in builder.definitions {
        script.push_str(&definition);
    }
    script.push_str(&format!("(assert {different})\n"));
    if script.len() > MAX_SCRIPT {
        return Err(Error::Limit);
    }
    let mut names: BTreeSet<_> = builder
        .declarations
        .iter()
        .filter(|(_, sort)| sort.as_str() == WORD)
        .map(|(name, _)| name.clone())
        .collect();
    for (address, byte) in &builder.samples {
        names.extend([address.clone(), byte.clone()]);
    }
    Ok(Query {
        script,
        names: names.into_iter().collect(),
        samples: builder.samples,
        before: before.clone(),
        after: after.clone(),
        outputs: outputs.to_vec(),
        input_names,
        candidate_names,
    })
}

impl Query {
    pub fn smt2(&self) -> &str {
        &self.script
    }

    fn replay(&self, model: &BTreeMap<String, u64>) -> Result<Counterexample, UnknownReason> {
        let base = model["base"];
        let size = model["size"];
        if size > REPLAY_BYTES || base.checked_add(size).is_none() {
            return Err(UnknownReason::ReplayLimit);
        }
        let mut memory = vec![0; size as usize];
        for (address, byte) in &self.samples {
            if let Some(offset) = model[address]
                .checked_sub(base)
                .filter(|&offset| offset < size)
            {
                memory[offset as usize] = model[byte]
                    .try_into()
                    .map_err(|_| UnknownReason::InvalidCounterexample)?;
            }
        }
        let before_registers: Vec<_> = self.input_names.iter().map(|name| model[name]).collect();
        let after_registers: Vec<_> = self
            .candidate_names
            .iter()
            .map(|name| model[name])
            .collect();
        let before = self
            .before
            .run_with_memory(
                &before_registers,
                base,
                &memory,
                self.before.instructions().len(),
            )
            .map_err(|_| UnknownReason::InvalidCounterexample)?;
        let after = self
            .after
            .run_with_memory(
                &after_registers,
                base,
                &memory,
                self.after.instructions().len(),
            )
            .map_err(|_| UnknownReason::InvalidCounterexample)?;
        if matches!(before.status, RunStatus::Suspended)
            || matches!(after.status, RunStatus::Suspended)
            || !differs(&before, &after, &self.outputs)
        {
            return Err(UnknownReason::InvalidCounterexample);
        }
        Ok(Counterexample {
            before_registers,
            after_registers,
            memory_base: base,
            memory,
            before,
            after,
        })
    }

    pub fn check(&self, solver: &Solver) -> Verdict {
        let result = (|| -> Result<Verdict, UnknownReason> {
            match solver.run_smt(&self.script, &[])?.trim() {
                "unsat" => Ok(Verdict::EquivalentUnderModel),
                "unknown" => Ok(Verdict::Unknown(UnknownReason::SolverUnknown)),
                "sat" => {
                    // Restrict witness extraction only. This bounded query can
                    // never supply an equivalence verdict for the original model.
                    let replay = format!(
                        "{}(assert (bvule size {}))\n(assert (bvule base (bvsub {} size)))\n",
                        self.script,
                        word(REPLAY_BYTES),
                        word(u64::MAX)
                    );
                    match solver.run_smt(&replay, &[])?.trim() {
                        "sat" => {}
                        "unsat" => return Err(UnknownReason::ReplayLimit),
                        "unknown" => return Err(UnknownReason::SolverUnknown),
                        other => {
                            return Err(UnknownReason::InvalidResponse(
                                other.chars().take(256).collect(),
                            ));
                        }
                    }
                    let response = solver.run_smt(&replay, &self.names)?;
                    let model = parse_named_values(&response, &self.names)?;
                    Ok(Verdict::Counterexample(Box::new(self.replay(&model)?)))
                }
                other => Err(UnknownReason::InvalidResponse(
                    other.chars().take(256).collect(),
                )),
            }
        })();
        result.unwrap_or_else(Verdict::Unknown)
    }
}

fn differs(left: &RunReport, right: &RunReport, outputs: &[Reg]) -> bool {
    left.status != right.status
        || left.state.memory != right.state.memory
        || left.state.memory_base != right.state.memory_base
        || (matches!(left.status, RunStatus::Returned(_))
            && outputs
                .iter()
                .any(|r| left.state.registers[r.0] != right.state.registers[r.0]))
}

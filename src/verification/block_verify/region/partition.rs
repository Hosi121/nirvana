//! An exhaustive Boolean partition keeps the original query and observations.
use super::*;
use std::time::{Duration, Instant};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PartitionedVerdict {
    pub verdict: Verdict,
    pub checked: usize,
    pub total: usize,
}

/// Exhaustive low-bit cases over one original left-side input word. Construction
/// retains the full64-bit domain and observes the unchanged original property.
#[derive(Clone, Debug)]
pub struct InputPartitions<'a> {
    query: &'a Query,
    guards: Vec<String>,
}
impl InputPartitions<'_> {
    pub fn smt2(&self) -> impl Iterator<Item = String> + '_ {
        self.guards.iter().enumerate().map(|(index, guard)| {
            format!(
                "{}; checked-input-bit-partitions-v1 part={index}\n(assert {guard})\n",
                self.query.script
            )
        })
    }
    pub fn check(&self, solver: &Solver, budget: Duration) -> PartitionedVerdict {
        self.query
            .check_parts(solver, budget, self.guards.len(), self.smt2())
    }
}

fn input_guards(name: &str, bits: u8) -> Vec<String> {
    let count = 1usize << bits;
    (0..count)
        .map(|value| {
            format!(
                "(= (bvand {name} {}) {})",
                word(count as u64 - 1),
                word(value as u64)
            )
        })
        .collect()
}

impl Query {
    /// Select1..4 low bits, yielding at most16 exhaustive cases. The selector
    /// can name any original left input, including an independently varied one.
    pub fn input_partitions(&self, register: Reg, bits: u8) -> Result<InputPartitions<'_>, Error> {
        if !(1..=4).contains(&bits) {
            return Err(Error::BoundaryMapping);
        }
        let name = self
            .input_names
            .get(register.0)
            .ok_or(Error::BoundaryMapping)?;
        let guards = input_guards(name, bits);
        if guards.iter().any(|guard| {
            self.script
                .len()
                .saturating_add(guard.len())
                .saturating_add(96)
                > MAX_SCRIPT
        }) {
            return Err(Error::Limit);
        }
        Ok(InputPartitions {
            query: self,
            guards,
        })
    }
    /// Each script adds a guard to the unchanged original disequality. Guards
    /// cover fault/status cases, every listed normal Return, and all other
    /// normal Returns. Iteration constructs at most one additional script at a time.
    pub fn partition_smt2(&self) -> impl Iterator<Item = String> + '_ {
        self.partitions.iter().enumerate().map(|(index, guard)| {
            format!(
                "{}; {PARTITION_MODEL_ID} part={index}\n(assert {guard})\n",
                self.script
            )
        })
    }

    /// Prove every exhaustive partition, or replay a counterexample in one.
    /// Unknown never supplies a partial equivalence result. The shared wall
    /// budget (at most30seconds) also caps SAT witness extraction processes.
    pub fn check_partitioned(&self, solver: &Solver, budget: Duration) -> PartitionedVerdict {
        self.check_parts(solver, budget, self.partitions.len(), self.partition_smt2())
    }
    fn check_parts(
        &self,
        solver: &Solver,
        budget: Duration,
        total: usize,
        scripts: impl Iterator<Item = String>,
    ) -> PartitionedVerdict {
        let deadline = Instant::now() + budget.min(Duration::from_secs(30));
        let mut checked = 0;
        for script in scripts {
            if Instant::now() >= deadline {
                return PartitionedVerdict {
                    verdict: Verdict::Unknown(UnknownReason::SolverTimeout),
                    checked,
                    total,
                };
            }
            let verdict = self.check_script(solver, &script, Some(deadline));
            checked += 1;
            if verdict != Verdict::EquivalentUnderModel {
                return PartitionedVerdict {
                    verdict,
                    checked,
                    total,
                };
            }
        }
        PartitionedVerdict {
            verdict: Verdict::EquivalentUnderModel,
            checked,
            total,
        }
    }
}

#[cfg(test)]
mod tests;

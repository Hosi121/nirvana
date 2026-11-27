//! Register observations are selected after normal exit; effects stay global.
use super::*;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ReturnOutputs {
    pub value: u64,
    pub registers: Vec<Reg>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum Observations {
    Uniform(Vec<Reg>),
    AtReturns {
        rows: Vec<ReturnOutputs>,
        otherwise: Vec<Reg>,
    },
}
impl Observations {
    pub(super) fn uniform(registers: &[Reg]) -> Result<Self, Error> {
        if registers.len() > MAX_REGISTERS {
            return Err(Error::BoundaryMapping);
        }
        Ok(Self::Uniform(registers.to_vec()))
    }
    pub(super) fn at_returns(rows: &[ReturnOutputs]) -> Result<Self, Error> {
        if rows.len() > MAX_INSTRUCTIONS
            || rows.iter().any(|row| row.registers.len() > MAX_REGISTERS)
        {
            return Err(Error::BoundaryMapping);
        }
        let mut values = BTreeSet::new();
        if rows.iter().any(|row| !values.insert(row.value)) {
            return Err(Error::BoundaryMapping);
        }
        Ok(Self::AtReturns {
            rows: rows.to_vec(),
            otherwise: Vec::new(),
        })
    }
    pub(super) fn validate(&mut self, common: usize) -> Result<(), Error> {
        let valid = match self {
            Self::Uniform(registers) => registers.iter().all(|r| r.0 < common),
            Self::AtReturns { rows, otherwise } => {
                *otherwise = (0..common).map(Reg).collect();
                rows.iter()
                    .flat_map(|row| &row.registers)
                    .all(|r| r.0 < common)
            }
        };
        valid.then_some(()).ok_or(Error::BoundaryMapping)
    }
    pub(super) fn at(&self, status: &RunStatus) -> &[Reg] {
        match self {
            Self::Uniform(registers) => registers,
            Self::AtReturns { rows, otherwise } => {
                if let RunStatus::Returned(value) = status
                    && let Some(row) = rows.iter().find(|row| row.value == *value)
                {
                    return &row.registers;
                }
                otherwise
            }
        }
    }
    pub(super) fn model_id(&self) -> &'static str {
        match self {
            Self::Uniform(_) => MODEL_ID,
            Self::AtReturns { .. } => RETURN_OUTPUTS_MODEL_ID,
        }
    }
    pub(super) fn partitions(&self, left: &State, right: &State) -> Vec<String> {
        self.partition_guards(
            &format!("(and {} {})", left.alive, right.alive),
            &left.exit_value,
        )
    }
    pub(super) fn partition_guards(&self, normal: &str, returned: &str) -> Vec<String> {
        let Self::AtReturns { rows, .. } = self else {
            return vec![String::from("true")];
        };
        let cases: Vec<_> = rows
            .iter()
            .map(|row| format!("(= {} {})", returned, word(row.value)))
            .collect();
        let mut partitions = vec![format!("(not {normal})")];
        partitions.extend(cases.iter().map(|case| format!("(and {normal} {case})")));
        partitions.push(format!(
            "(and {normal} (not (or false {})))",
            cases.join(" ")
        ));
        partitions
    }
    pub(super) fn differences(&self, left: &State, right: &State) -> Vec<String> {
        let differences = |registers: &[Reg]| {
            registers
                .iter()
                .map(|r| {
                    format!(
                        "(distinct {} {})",
                        left.registers[r.0], right.registers[r.0]
                    )
                })
                .collect::<Vec<_>>()
        };
        match self {
            Self::Uniform(registers) => differences(registers),
            Self::AtReturns { rows, otherwise } => {
                let guards: Vec<_> = rows
                    .iter()
                    .map(|row| format!("(= {} {})", left.exit_value, word(row.value)))
                    .collect();
                let mut conditions: Vec<_> = rows
                    .iter()
                    .zip(&guards)
                    .map(|(row, guard)| {
                        format!(
                            "(and {guard} (or false {}))",
                            differences(&row.registers).join(" ")
                        )
                    })
                    .collect();
                conditions.push(format!(
                    "(and (not (or false {})) (or false {}))",
                    guards.join(" "),
                    differences(otherwise).join(" ")
                ));
                conditions
            }
        }
    }
}

#[cfg(test)]
mod tests;

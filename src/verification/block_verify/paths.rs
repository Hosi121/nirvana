//! Bounded reachability questions for evaluation input generation.
//!
//! SAT inputs are replayed against the executable IR. UNSAT excludes only the
//! specified complete instruction prefix and input-memory profile, rather than
//! proving a CFG edge unreachable through other paths or loop iterations.
use super::*;
use crate::model::ir::RunReport;

pub const MODEL_ID: &str = "checked-memory-path-inputs-v1";
const MAX_PREFIX: usize = 1024;
const MAX_SCRIPT: usize = 4 * 1024 * 1024;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SymbolicWord {
    pub offset: usize,
    pub width: Width,
}

/// Fixed entry registers and RAM template. The supplied nonoverlapping words
/// alone vary; all other in-bounds bytes retain their template values.
#[derive(Clone, Debug)]
pub struct InputProfile {
    pub registers: Vec<u64>,
    pub memory_base: u64,
    pub memory: Vec<u8>,
    pub words: Vec<SymbolicWord>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PathWitness {
    /// Values in the same order as InputProfile.words, zero-extended to u64.
    pub words: Vec<u64>,
    pub report: RunReport,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Reachability {
    Witness(Box<PathWitness>),
    InfeasiblePrefix,
    Unknown(UnknownReason),
}

#[derive(Clone, Debug)]
pub struct PathQuery {
    smt2: String,
    names: Vec<String>,
    profile: InputProfile,
    program: Program,
    prefix: Vec<u64>,
    next: u64,
}

/// Require execution to complete `prefix` from the entry, without a fault or
/// return, and start `next`. Repeated PCs model the specified loop iterations.
pub fn path_query(
    program: &Program,
    profile: &InputProfile,
    prefix: &[u64],
    next: u64,
) -> Result<PathQuery, UnknownReason> {
    if program.register_count() > 4096
        || prefix.len() > MAX_PREFIX
        || profile.memory.len() > REPLAY_BYTES as usize
        || profile.words.len() > 64
    {
        return Err(UnknownReason::ResourceLimit);
    }
    if profile.registers.len() != program.register_count()
        || profile.words.is_empty()
        || profile
            .memory_base
            .checked_add(profile.memory.len() as u64)
            .is_none()
    {
        return Err(UnknownReason::BoundaryMapping);
    }
    let entry = program.cfg().block(program.cfg().entry()).start;
    if prefix.first().copied() != Some(entry) {
        return Err(UnknownReason::BlockShape);
    }
    let instructions: BTreeMap<_, _> = program
        .instructions()
        .iter()
        .map(|i| (i.address, i))
        .collect();
    if !instructions.contains_key(&next) {
        return Err(UnknownReason::BlockShape);
    }
    let mut builder = Builder {
        declarations: BTreeMap::new(),
        definitions: Vec::new(),
        samples: Vec::new(),
        visits: 0,
    };
    builder.declare("initial_memory", ARRAY);
    builder.declare("base", WORD);
    builder.declare("size", WORD);
    let names: Vec<_> = (0..profile.words.len())
        .map(|i| builder.declare(&format!("input{i}"), WORD))
        .collect();
    let mut bytes = BTreeMap::new();
    let mut assertions = vec![
        format!("(= base {})", word(profile.memory_base)),
        format!("(= size {})", word(profile.memory.len() as u64)),
    ];
    for (input, name) in profile.words.iter().zip(&names) {
        if input
            .offset
            .checked_add(input.width.bytes())
            .is_none_or(|end| end > profile.memory.len())
        {
            return Err(UnknownReason::BoundaryMapping);
        }
        if input.width != Width::U64 {
            assertions.push(format!(
                "(bvule {name} {})",
                word((1u64 << input.width.bits()) - 1)
            ));
        }
        for i in 0..input.width.bytes() {
            let value = format!("((_ extract {} {}) {name})", i * 8 + 7, i * 8);
            if bytes.insert(input.offset + i, value).is_some() {
                return Err(UnknownReason::BoundaryMapping);
            }
        }
    }
    for (offset, &byte) in profile.memory.iter().enumerate() {
        let value = bytes
            .get(&offset)
            .cloned()
            .unwrap_or_else(|| format!("#x{byte:02x}"));
        assertions.push(format!(
            "(= (select initial_memory {}) {value})",
            word(profile.memory_base + offset as u64)
        ));
    }
    let mut state = State {
        registers: profile.registers.iter().map(|&v| word(v)).collect(),
        memory: "initial_memory".into(),
        alive: "true".into(),
        fault_access: word(0),
        fault_address: word(0),
        fault_width: word(0),
        exit_kind: word(0),
        exit_value: word(0),
    };
    for (index, pc) in prefix.iter().enumerate() {
        let instruction = instructions.get(pc).ok_or(UnknownReason::BlockShape)?;
        let target = prefix.get(index + 1).copied().unwrap_or(next);
        let fallthrough = instruction
            .address
            .checked_add(u64::from(instruction.size))
            .ok_or(UnknownReason::BlockShape)?;
        let permitted = match instruction.control {
            Control::Next => target == fallthrough,
            Control::Jump(to) => target == to,
            Control::Branch { target: to, .. } => target == to || target == fallthrough,
            Control::Return(_) => false,
        };
        if !permitted {
            return Err(UnknownReason::BlockShape);
        }
        builder.instruction(instruction, &mut state)?;
        assertions.push(state.alive.clone());
        assertions.push(format!("(= {} {})", state.exit_value, word(target)));
    }
    let mut smt2 = format!(
        "; Nirvana {MODEL_ID}; fixed entry/RAM except symbolic words\n(set-logic QF_AUFBV)\n"
    );
    for (name, sort) in builder.declarations {
        smt2.push_str(&format!("(declare-fun {name} () {sort})\n"));
    }
    for definition in builder.definitions {
        smt2.push_str(&definition);
    }
    for assertion in assertions {
        smt2.push_str(&format!("(assert {assertion})\n"));
    }
    if smt2.len() > MAX_SCRIPT {
        return Err(UnknownReason::ResourceLimit);
    }
    Ok(PathQuery {
        smt2,
        names,
        profile: profile.clone(),
        program: program.clone(),
        prefix: prefix.to_vec(),
        next,
    })
}

impl PathQuery {
    /// Declarations, execution and prefix constraints, without solver commands.
    pub fn smt2(&self) -> &str {
        &self.smt2
    }
    fn replay(&self, values: &BTreeMap<String, u64>) -> Result<PathWitness, UnknownReason> {
        let mut memory = self.profile.memory.clone();
        let mut words = Vec::new();
        for (input, name) in self.profile.words.iter().zip(&self.names) {
            let value = *values
                .get(name)
                .ok_or(UnknownReason::InvalidCounterexample)?;
            if input.width != Width::U64 && value >> input.width.bits() != 0 {
                return Err(UnknownReason::InvalidCounterexample);
            }
            memory[input.offset..input.offset + input.width.bytes()]
                .copy_from_slice(&value.to_le_bytes()[..input.width.bytes()]);
            words.push(value);
        }
        let report = self
            .program
            .run_with_memory(
                &self.profile.registers,
                self.profile.memory_base,
                &memory,
                self.prefix.len() + 1,
            )
            .map_err(|_| UnknownReason::InvalidCounterexample)?;
        if report.state.trace.len() != self.prefix.len() + 1
            || !report.state.trace.starts_with(&self.prefix)
            || report.state.trace.last() != Some(&self.next)
        {
            return Err(UnknownReason::InvalidCounterexample);
        }
        Ok(PathWitness { words, report })
    }
    pub fn check(&self, solver: &Solver) -> Reachability {
        let result = (|| match solver.run_smt(&self.smt2, &[])?.trim() {
            "unsat" => Ok(Reachability::InfeasiblePrefix),
            "unknown" => Ok(Reachability::Unknown(UnknownReason::SolverUnknown)),
            "sat" => {
                let response = solver.run_smt(&self.smt2, &self.names)?;
                let values = parse_named_values(&response, &self.names)?;
                Ok(Reachability::Witness(Box::new(self.replay(&values)?)))
            }
            other => Err(UnknownReason::InvalidResponse(
                other.chars().take(256).collect(),
            )),
        })();
        result.unwrap_or_else(Reachability::Unknown)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn fixture() -> (Program, InputProfile) {
        let program = Program::new(
            0,
            1,
            vec![
                IrInstruction {
                    address: 0,
                    size: 1,
                    assignments: vec![],
                    control: Control::Branch {
                        condition: Expr::load(Expr::Register(Reg(0)), Width::U8),
                        target: 2,
                    },
                },
                IrInstruction {
                    address: 1,
                    size: 1,
                    assignments: vec![],
                    control: Control::Return(Expr::Const(0)),
                },
                IrInstruction {
                    address: 2,
                    size: 1,
                    assignments: vec![],
                    control: Control::Return(Expr::Const(1)),
                },
            ],
        )
        .unwrap();
        let profile = InputProfile {
            registers: vec![100],
            memory_base: 100,
            memory: vec![0; 8],
            words: vec![SymbolicWord {
                offset: 0,
                width: Width::U8,
            }],
        };
        (program, profile)
    }
    #[test]
    fn replay_requires_the_exact_prefix_and_zero_extended_input_width() {
        let (program, profile) = fixture();
        let query = path_query(&program, &profile, &[0], 2).unwrap();
        assert!(
            query
                .replay(&BTreeMap::from([("input0".into(), 1)]))
                .is_ok()
        );
        for value in [0, 256, u64::MAX] {
            assert_eq!(
                query
                    .replay(&BTreeMap::from([("input0".into(), value)]))
                    .unwrap_err(),
                UnknownReason::InvalidCounterexample
            );
        }
        assert!(query.replay(&BTreeMap::new()).is_err());
    }
    #[test]
    fn profiles_and_transfers_are_checked_before_encoding() {
        let (program, profile) = fixture();
        for (prefix, next) in [(vec![], 0), (vec![1], 2), (vec![0], 10), (vec![0, 1], 2)] {
            assert!(path_query(&program, &profile, &prefix, next).is_err());
        }
        for change in 0..4 {
            let mut profile = profile.clone();
            match change {
                0 => profile.words.push(profile.words[0]),
                1 => profile.words[0].offset = 8,
                2 => profile.registers.clear(),
                3 => profile.memory_base = u64::MAX,
                _ => unreachable!(),
            }
            assert!(path_query(&program, &profile, &[0], 2).is_err());
        }
    }
}

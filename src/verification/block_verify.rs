//! Memory-aware translation validation at unchanged basic-block boundaries.
//! The optimizer does not supply the symbolic semantics or proof verdict.

use std::collections::{BTreeMap, BTreeSet};
use std::time::{Duration, Instant};

use crate::control_flow::cfg::Target;
use crate::model::ir::{
    BlockExit, BlockReport, Control, Expr, IrInstruction, Place, Program, Reg, Width,
};
use crate::verification::verify::{
    Solver, UnknownReason, binary_term, parse_named_values, unary_term,
};

pub const MODEL_ID: &str = "checked-memory-block-v1";
const ARRAY: &str = "(Array (_ BitVec 64) (_ BitVec 8))";
const WORD: &str = "(_ BitVec 64)";
const REPLAY_BYTES: u64 = 65536;
type Registers = BTreeSet<usize>;

pub mod paths;
pub mod region;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BlockCounterexample {
    pub before_registers: Vec<u64>,
    pub after_registers: Vec<u64>,
    pub memory_base: u64,
    pub memory: Vec<u8>,
    pub before: BlockReport,
    pub after: BlockReport,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum BlockVerdict {
    EquivalentUnderModel,
    Counterexample(Box<BlockCounterexample>),
    Unknown(UnknownReason),
}

#[derive(Clone, Debug)]
pub struct BlockQuery {
    smt2: String,
    names: Vec<String>,
    samples: Vec<(String, String)>,
    before: Program,
    after: Program,
    start: u64,
    outputs: Vec<Reg>,
    input_names: Vec<String>,
    candidate_names: Vec<String>,
}

struct Builder {
    declarations: BTreeMap<String, String>,
    definitions: Vec<String>,
    samples: Vec<(String, String)>,
    visits: usize,
    interning: Option<BTreeMap<(String, String), String>>,
}

#[derive(Clone)]
struct State {
    registers: Vec<String>,
    memory: String,
    alive: String,
    fault_access: String,
    fault_address: String,
    fault_width: String,
    exit_kind: String,
    exit_value: String,
}

fn word(value: u64) -> String {
    format!("#x{value:016x}")
}

impl Builder {
    fn declare(&mut self, name: &str, sort: &str) -> String {
        self.declarations.insert(name.into(), sort.into());
        name.into()
    }
    fn define(&mut self, sort: &str, term: String) -> String {
        if let Some(name) = self
            .interning
            .as_ref()
            .and_then(|memo| memo.get(&(sort.into(), term.clone())))
        {
            return name.clone();
        }
        let name = format!("v{}", self.definitions.len());
        if let Some(memo) = &mut self.interning {
            memo.insert((sort.into(), term.clone()), name.clone());
            self.definitions.push(format!(
                "(declare-fun {name} () {sort})\n(assert (= {name} {term}))\n"
            ));
        } else {
            self.definitions
                .push(format!("(define-fun {name} () {sort} {term})\n"));
        }
        name
    }
    fn bool(&mut self, term: String) -> String {
        self.define("Bool", term)
    }
    fn value(&mut self, term: String) -> String {
        self.define(WORD, term)
    }
    fn sample(&mut self, address: String) -> Result<(), UnknownReason> {
        if self.samples.len() >= 4096 {
            return Err(UnknownReason::ResourceLimit);
        }
        let address = self.value(address);
        let byte = self.value(format!(
            "((_ zero_extend 56) (select initial_memory {address}))"
        ));
        self.samples.push((address, byte));
        Ok(())
    }
    fn initial(&mut self, count: usize, shared: &Registers, prefix: &str) -> (State, Vec<String>) {
        let registers: Vec<_> = (0..count)
            .map(|index| {
                self.declare(
                    &if shared.contains(&index) {
                        format!("r{index}")
                    } else {
                        format!("{prefix}_r{index}")
                    },
                    WORD,
                )
            })
            .collect();
        (
            State {
                registers: registers.clone(),
                memory: "initial_memory".into(),
                alive: "true".into(),
                fault_access: word(0),
                fault_address: word(0),
                fault_width: word(0),
                exit_kind: word(0),
                exit_value: word(0),
            },
            registers,
        )
    }
    fn check_access(
        &mut self,
        state: &mut State,
        address: &str,
        width: Width,
        write: bool,
        guard: &str,
    ) {
        let bytes = width.bytes() as u64;
        let valid = self.bool(format!("(and (bvule {address} {}) (bvuge {address} base) (bvuge size {}) (bvule (bvsub {address} base) (bvsub size {})))", word(u64::MAX - bytes + 1), word(bytes), word(bytes)));
        let bad = self.bool(format!("(and {} {guard} (not {valid}))", state.alive));
        state.fault_access = self.value(format!(
            "(ite {bad} {} {})",
            word(u64::from(write)),
            state.fault_access
        ));
        state.fault_address = self.value(format!("(ite {bad} {address} {})", state.fault_address));
        state.fault_width =
            self.value(format!("(ite {bad} {} {})", word(bytes), state.fault_width));
        state.alive = self.bool(format!("(and {} (or (not {guard}) {valid}))", state.alive));
    }
    fn expression(
        &mut self,
        expression: &Expr,
        state: &mut State,
        guard: &str,
        depth: usize,
    ) -> Result<String, UnknownReason> {
        self.visits += 1;
        if self.visits > 100_000 || depth > 256 {
            return Err(UnknownReason::ResourceLimit);
        }
        Ok(match expression {
            Expr::Const(value) => word(*value),
            Expr::Unary(op, value) => {
                let value = self.expression(value, state, guard, depth + 1)?;
                self.value(unary_term(op, &value))
            }
            Expr::Register(Reg(index)) => state.registers[*index].clone(),
            Expr::Binary(op, left, right) => {
                let left = self.expression(left, state, guard, depth + 1)?;
                let right = self.expression(right, state, guard, depth + 1)?;
                self.value(binary_term(op, &left, &right))
            }
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => {
                let condition = self.expression(condition, state, guard, depth + 1)?;
                let truth = self.bool(format!("(distinct {condition} {})", word(0)));
                let yes = self.bool(format!("(and {guard} {truth})"));
                let no = self.bool(format!("(and {guard} (not {truth}))"));
                let taken = self.expression(taken, state, &yes, depth + 1)?;
                let not_taken = self.expression(not_taken, state, &no, depth + 1)?;
                self.value(format!("(ite {truth} {taken} {not_taken})"))
            }
            Expr::Load { address, width } => {
                let address = self.expression(address, state, guard, depth + 1)?;
                self.check_access(state, &address, *width, false, guard);
                let mut bytes = Vec::new();
                for offset in 0..width.bytes() {
                    let at = format!("(bvadd {address} {})", word(offset as u64));
                    self.sample(at.clone())?;
                    bytes.push(format!("(select {} {at})", state.memory));
                }
                let mut value = bytes.pop().expect("nonzero width");
                while let Some(byte) = bytes.pop() {
                    value = format!("(concat {value} {byte})");
                }
                if *width != Width::U64 {
                    value = format!("((_ zero_extend {}) {value})", 64 - width.bits());
                }
                self.value(value)
            }
        })
    }
    fn instruction(
        &mut self,
        instruction: &IrInstruction,
        state: &mut State,
    ) -> Result<(), UnknownReason> {
        self.instruction_with_branch(instruction, state).map(|_| ())
    }
    // The DAG encoder can route the evaluated condition directly. Keep its
    // evaluation in the primitive kernel so loads and first faults occur once.
    fn instruction_with_branch(
        &mut self,
        instruction: &IrInstruction,
        state: &mut State,
    ) -> Result<Option<String>, UnknownReason> {
        for assignment in &instruction.assignments {
            match &assignment.destination {
                Place::Register(Reg(index)) => {
                    let value = self.expression(&assignment.value, state, "true", 0)?;
                    // Registers are observed only at a normal block exit.
                    // After a fault all effects and subsequent fault updates
                    // are guarded off, so dead register values may be total.
                    state.registers[*index] = value;
                }
                Place::Memory { address, width } => {
                    let address = self.expression(address, state, "true", 0)?;
                    self.check_access(state, &address, *width, true, "true");
                    let value = self.expression(&assignment.value, state, "true", 0)?;
                    let mut memory = state.memory.clone();
                    for offset in 0..width.bytes() {
                        let at = format!("(bvadd {address} {})", word(offset as u64));
                        self.sample(at.clone())?;
                        memory = format!(
                            "(store {memory} {at} ((_ extract {} {}) {value}))",
                            offset * 8 + 7,
                            offset * 8
                        );
                    }
                    state.memory = self.define(
                        ARRAY,
                        format!("(ite {} {memory} {})", state.alive, state.memory),
                    );
                }
            }
        }
        state.exit_kind = word(0);
        let mut branch = None;
        state.exit_value = match &instruction.control {
            Control::Next => word(instruction.address + u64::from(instruction.size)),
            Control::Jump(target) => word(*target),
            Control::Branch { condition, target } => {
                let condition = self.expression(condition, state, "true", 0)?;
                let next = self.value(format!(
                    "(ite (distinct {condition} {}) {} {})",
                    word(0),
                    word(*target),
                    word(instruction.address + u64::from(instruction.size))
                ));
                branch = Some(condition);
                next
            }
            Control::Return(value) => {
                state.exit_kind = word(1);
                self.expression(value, state, "true", 0)?
            }
        };
        Ok(branch)
    }
    fn block(
        &mut self,
        program: &Program,
        start: u64,
        state: &mut State,
    ) -> Result<(), UnknownReason> {
        let id = program
            .cfg()
            .block_at(start)
            .ok_or(UnknownReason::BlockShape)?;
        for instruction in &program.instructions()[program.cfg().block(id).instructions.clone()] {
            self.instruction(instruction, state)?;
        }
        Ok(())
    }
}

/// Inputs in `shared` must correspond at entry; all other initial registers are
/// independent on the two sides. `outputs` must correspond on normal exit.
pub fn block_query(
    before: &Program,
    after: &Program,
    start: u64,
    shared: &[Reg],
    outputs: &[Reg],
) -> Result<BlockQuery, UnknownReason> {
    if before.register_count() > 4096 || after.register_count() > 4096 {
        return Err(UnknownReason::ResourceLimit);
    }
    let common = before.register_count().min(after.register_count());
    if shared.iter().chain(outputs).any(|reg| reg.0 >= common) {
        return Err(UnknownReason::BoundaryMapping);
    }
    let shared: Registers = shared.iter().map(|reg| reg.0).collect();
    let mut builder = Builder {
        declarations: BTreeMap::new(),
        definitions: Vec::new(),
        samples: Vec::new(),
        visits: 0,
        interning: None,
    };
    builder.declare("initial_memory", ARRAY);
    builder.declare("base", WORD);
    builder.declare("size", WORD);
    builder.declare("memory_witness", WORD);
    let (mut left, input_names) = builder.initial(before.register_count(), &shared, "left");
    let (mut right, candidate_names) = builder.initial(after.register_count(), &shared, "right");
    builder.block(before, start, &mut left)?;
    builder.block(after, start, &mut right)?;
    builder.sample("memory_witness".into())?;
    let mut normal = vec![
        format!("(distinct {} {})", left.exit_kind, right.exit_kind),
        format!("(distinct {} {})", left.exit_value, right.exit_value),
    ];
    normal.extend(outputs.iter().map(|reg| {
        format!(
            "(distinct {} {})",
            left.registers[reg.0], right.registers[reg.0]
        )
    }));
    let different = format!(
        "(or (xor {} {}) (and (not {}) (not {}) (or (distinct {} {}) (distinct {} {}) (distinct {} {}))) (distinct (select {} memory_witness) (select {} memory_witness)) (and {} {} (or {})))",
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
    let mut smt2 =
        format!("; Nirvana {MODEL_ID}; unbounded input bytes, base, size.\n(set-logic QF_AUFBV)\n");
    for (name, sort) in &builder.declarations {
        smt2.push_str(&format!("(declare-fun {name} () {sort})\n"));
    }
    for definition in builder.definitions {
        smt2.push_str(&definition);
    }
    smt2.push_str(&format!("(assert {different})\n"));
    let mut names: Vec<_> = builder
        .declarations
        .iter()
        .filter(|(_, sort)| sort.as_str() == WORD)
        .map(|(name, _)| name.clone())
        .collect();
    for (address, byte) in &builder.samples {
        names.extend([address.clone(), byte.clone()]);
    }
    Ok(BlockQuery {
        smt2,
        names,
        samples: builder.samples,
        before: before.clone(),
        after: after.clone(),
        start,
        outputs: outputs.to_vec(),
        input_names,
        candidate_names,
    })
}

fn differs(left: &BlockReport, right: &BlockReport, outputs: &[Reg]) -> bool {
    left.exit != right.exit
        || left.state.memory != right.state.memory
        || left.state.memory_base != right.state.memory_base
        || (!matches!(left.exit, BlockExit::Fault(_))
            && outputs
                .iter()
                .any(|reg| left.state.registers[reg.0] != right.state.registers[reg.0]))
}

impl BlockQuery {
    pub fn smt2(&self) -> &str {
        &self.smt2
    }
    fn replay(&self, model: &BTreeMap<String, u64>) -> Result<BlockCounterexample, UnknownReason> {
        let base = model["base"];
        let size = model["size"];
        if size > REPLAY_BYTES {
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
            .run_block_with_memory(self.start, &before_registers, base, &memory)
            .map_err(|_| UnknownReason::InvalidCounterexample)?;
        let after = self
            .after
            .run_block_with_memory(self.start, &after_registers, base, &memory)
            .map_err(|_| UnknownReason::InvalidCounterexample)?;
        if !differs(&before, &after, &self.outputs) {
            return Err(UnknownReason::InvalidCounterexample);
        }
        Ok(BlockCounterexample {
            before_registers,
            after_registers,
            memory_base: base,
            memory,
            before,
            after,
        })
    }
    pub fn check(&self, solver: &Solver) -> BlockVerdict {
        let result = (|| -> Result<BlockVerdict, UnknownReason> {
            match solver.run_smt(&self.smt2, &[])?.trim() {
                "unsat" => Ok(BlockVerdict::EquivalentUnderModel),
                "unknown" => Ok(BlockVerdict::Unknown(UnknownReason::SolverUnknown)),
                "sat" => {
                    // Restrict only counterexample extraction. Never use this
                    // bounded replay query to produce an equivalence verdict.
                    let replay = format!(
                        "{}(assert (bvule size {}))\n",
                        self.smt2,
                        word(REPLAY_BYTES)
                    );
                    let response = solver.run_smt(&replay, &self.names)?;
                    let model = parse_named_values(&response, &self.names)?;
                    Ok(BlockVerdict::Counterexample(Box::new(self.replay(&model)?)))
                }
                other => Err(UnknownReason::InvalidResponse(
                    other.chars().take(256).collect(),
                )),
            }
        })();
        result.unwrap_or_else(BlockVerdict::Unknown)
    }
}

#[derive(Clone, Debug)]
pub struct BlockEvidence {
    pub address: u64,
    pub shared_inputs: Vec<Reg>,
    pub required_outputs: Vec<Reg>,
    pub verdict: BlockVerdict,
}

#[derive(Clone, Debug)]
pub struct Validation {
    pub blocks: Vec<BlockEvidence>,
    pub incomplete: Option<UnknownReason>,
    required_blocks: usize,
}

impl Validation {
    pub fn accepted(&self) -> bool {
        self.incomplete.is_none()
            && self.required_blocks != 0
            && self.blocks.len() == self.required_blocks
            && self
                .blocks
                .iter()
                .all(|block| block.verdict == BlockVerdict::EquivalentUnderModel)
    }
}

fn dependencies(expression: &Expr, registers: &mut Registers) -> bool {
    match expression {
        Expr::Const(_) => false,
        Expr::Unary(_, value) => dependencies(value, registers),
        Expr::Register(Reg(index)) => {
            registers.insert(*index);
            false
        }
        Expr::Binary(_, left, right) => {
            let a = dependencies(left, registers);
            let b = dependencies(right, registers);
            a || b
        }
        Expr::Load { address, .. } => {
            dependencies(address, registers);
            true
        }
        Expr::Select {
            condition,
            taken,
            not_taken,
        } => {
            let a = dependencies(condition, registers);
            let b = dependencies(taken, registers);
            let c = dependencies(not_taken, registers);
            a || b || c
        }
    }
}

// This analysis proposes boundary relations. The proof does not assume that
// omitted values happen to agree: they get independent symbolic inputs.
fn boundary_inputs(program: &Program) -> Vec<Registers> {
    let mut inputs = vec![Registers::new(); program.cfg().blocks().len()];
    loop {
        let mut changed = false;
        for id in program.cfg().reachable_blocks().iter().rev() {
            let block = program.cfg().block(*id);
            let mut required = Registers::new();
            for edge in &block.successors {
                if let Target::Block(next) = edge.target {
                    required.extend(&inputs[next.index()]);
                }
            }
            for instruction in program.instructions()[block.instructions.clone()]
                .iter()
                .rev()
            {
                match &instruction.control {
                    Control::Branch { condition, .. } => {
                        dependencies(condition, &mut required);
                    }
                    Control::Return(value) => {
                        dependencies(value, &mut required);
                    }
                    _ => {}
                }
                for assignment in instruction.assignments.iter().rev() {
                    let mut used = Registers::new();
                    let may_fault = dependencies(&assignment.value, &mut used);
                    let needed = match &assignment.destination {
                        Place::Register(Reg(index)) => required.remove(index),
                        Place::Memory { address, .. } => {
                            dependencies(address, &mut required);
                            true
                        }
                    };
                    if needed || may_fault {
                        required.extend(used);
                    }
                }
            }
            changed |= required != inputs[id.index()];
            inputs[id.index()] = required;
        }
        if !changed {
            return inputs;
        }
    }
}

/// Check a reduction with unchanged CFG cutpoints. All shared input bytes,
/// register values, memory bases and sizes remain unconstrained. The function
/// budget is ten seconds and at most 64 blocks; exhaustion is not acceptance.
pub fn validate_program(before: &Program, after: &Program, solver: &Solver) -> Validation {
    let reject = |reason| Validation {
        blocks: Vec::new(),
        incomplete: Some(reason),
        required_blocks: 0,
    };
    if before.cfg().instructions() != after.cfg().instructions()
        || before.cfg().block(before.cfg().entry()).start
            != after.cfg().block(after.cfg().entry()).start
    {
        return reject(UnknownReason::BlockShape);
    }
    if after.register_count() < before.register_count() {
        return reject(UnknownReason::BoundaryMapping);
    }
    let reachable = before.cfg().reachable_blocks();
    if reachable.len() > 64 {
        return reject(UnknownReason::ResourceLimit);
    }
    let left = boundary_inputs(before);
    let right = boundary_inputs(after);
    let mut relations = left;
    for (relation, candidate) in relations.iter_mut().zip(right) {
        relation.extend(candidate);
    }
    if reachable.iter().any(|id| {
        relations[id.index()]
            .iter()
            .any(|reg| *reg >= before.register_count())
    }) {
        return reject(UnknownReason::BoundaryMapping);
    }
    let deadline = Instant::now() + Duration::from_secs(10);
    let mut validation = Validation {
        blocks: Vec::new(),
        incomplete: None,
        required_blocks: reachable.len(),
    };
    for id in reachable {
        let block = before.cfg().block(id);
        let shared_inputs: Vec<_> = relations[id.index()].iter().copied().map(Reg).collect();
        let mut outputs = Registers::new();
        for edge in &block.successors {
            if let Target::Block(next) = edge.target {
                outputs.extend(&relations[next.index()]);
            }
        }
        let required_outputs: Vec<_> = outputs.into_iter().map(Reg).collect();
        let Some(remaining) = deadline.checked_duration_since(Instant::now()) else {
            validation.incomplete = Some(UnknownReason::SolverTimeout);
            break;
        };
        let verdict = match block_query(
            before,
            after,
            block.start,
            &shared_inputs,
            &required_outputs,
        ) {
            Ok(query) => query.check(&solver.limited_to(remaining)),
            Err(reason) => BlockVerdict::Unknown(reason),
        };
        let stop = verdict != BlockVerdict::EquivalentUnderModel;
        validation.blocks.push(BlockEvidence {
            address: block.start,
            shared_inputs,
            required_outputs,
            verdict,
        });
        if stop {
            break;
        }
    }
    validation
}

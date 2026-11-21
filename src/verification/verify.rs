//! Translation validation for pairs of load-free u64 expressions.
//! This encoder does not call the simplifier. UNSAT establishes equality for
//! every input under this bit-vector encoding, trusting the encoder and solver.

use std::collections::{BTreeMap, BTreeSet};
use std::io::{Read, Write};
use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

use crate::model::ir::{BinaryOp, Control, Expr, IrInstruction, Program, Reg};

pub const MODEL_ID: &str = "pure-u64-v1";

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum UnknownReason {
    MemoryExpression,
    ResourceLimit,
    SolverUnavailable(String),
    SolverFailure(String),
    SolverTimeout,
    SolverUnknown,
    InvalidResponse(String),
    InvalidCounterexample,
    BlockShape,
    BoundaryMapping,
    ReplayLimit,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Counterexample {
    pub registers: Vec<(Reg, u64)>,
    pub before: u64,
    pub after: u64,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Verdict {
    EquivalentUnderModel,
    Counterexample(Counterexample),
    Unknown(UnknownReason),
}

#[derive(Clone, Debug)]
pub struct CheckedRewrite {
    /// The candidate is retained only after an EquivalentUnderModel verdict.
    pub expression: Expr,
    pub verdict: Verdict,
}

#[derive(Clone, Debug)]
pub struct PureQuery {
    smt2: String,
    registers: Vec<usize>,
    before: Expr,
    after: Expr,
}

impl PureQuery {
    /// Declarations and a disequality assertion, without solver commands.
    pub fn smt2(&self) -> &str {
        &self.smt2
    }
    pub fn register_indices(&self) -> &[usize] {
        &self.registers
    }

    fn replay(&self, values: &BTreeMap<usize, u64>) -> Result<Counterexample, UnknownReason> {
        let count = self.registers.last().map_or(0, |index| index + 1);
        let mut inputs = vec![0; count];
        for &index in &self.registers {
            inputs[index] = *values
                .get(&index)
                .ok_or(UnknownReason::InvalidCounterexample)?;
        }
        let evaluate = |expression: &Expr| {
            Program::new(
                0,
                count,
                vec![IrInstruction {
                    address: 0,
                    size: 1,
                    assignments: vec![],
                    control: Control::Return(expression.clone()),
                }],
            )
            .expect("encoder validated registers")
            .execute(&inputs, 1)
            .expect("pure total expression")
            .value
        };
        let before = evaluate(&self.before);
        let after = evaluate(&self.after);
        if before == after {
            return Err(UnknownReason::InvalidCounterexample);
        }
        Ok(Counterexample {
            registers: self
                .registers
                .iter()
                .map(|&index| (Reg(index), inputs[index]))
                .collect(),
            before,
            after,
        })
    }
}

struct Encoder {
    definitions: Vec<String>,
    registers: BTreeSet<usize>,
    visits: usize,
}

impl Encoder {
    fn expression(&mut self, expression: &Expr, depth: usize) -> Result<String, UnknownReason> {
        self.visits += 1;
        if self.visits > 100_000 || depth > 256 {
            return Err(UnknownReason::ResourceLimit);
        }
        let term = match expression {
            Expr::Const(value) => return Ok(format!("#x{value:016x}")),
            Expr::Register(Reg(index)) => {
                if *index >= 4096 {
                    return Err(UnknownReason::ResourceLimit);
                }
                self.registers.insert(*index);
                return Ok(format!("r{index}"));
            }
            Expr::Load { .. } => return Err(UnknownReason::MemoryExpression),
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => {
                let c = self.expression(condition, depth + 1)?;
                let t = self.expression(taken, depth + 1)?;
                let n = self.expression(not_taken, depth + 1)?;
                format!("(ite (distinct {c} #x0000000000000000) {t} {n})")
            }
            Expr::Binary(op, left, right) => {
                let l = self.expression(left, depth + 1)?;
                let r = self.expression(right, depth + 1)?;
                binary_term(op, &l, &r)
            }
        };
        let name = format!("e{}", self.definitions.len());
        self.definitions
            .push(format!("(define-fun {name} () (_ BitVec 64) {term})\n"));
        Ok(name)
    }
}

pub(crate) fn binary_term(op: &BinaryOp, l: &str, r: &str) -> String {
    match op {
        BinaryOp::Eq | BinaryOp::Ne | BinaryOp::Ult | BinaryOp::Ule => {
            let op = match op {
                BinaryOp::Eq => "=",
                BinaryOp::Ne => "distinct",
                BinaryOp::Ult => "bvult",
                _ => "bvule",
            };
            format!("(ite ({op} {l} {r}) #x0000000000000001 #x0000000000000000)")
        }
        BinaryOp::Shl | BinaryOp::Shr | BinaryOp::AShr => {
            let op = match op {
                BinaryOp::Shl => "bvshl",
                BinaryOp::Shr => "bvlshr",
                _ => "bvashr",
            };
            format!("({op} {l} (bvand {r} #x000000000000003f))")
        }
        BinaryOp::UMulHigh => format!(
            "((_ extract 127 64) (bvmul ((_ zero_extend 64) {l}) ((_ zero_extend 64) {r})))"
        ),
        BinaryOp::SMulHigh => format!(
            "((_ extract 127 64) (bvmul ((_ sign_extend 64) {l}) ((_ sign_extend 64) {r})))"
        ),
        _ => {
            let op = match op {
                BinaryOp::Add => "bvadd",
                BinaryOp::Sub => "bvsub",
                BinaryOp::Mul => "bvmul",
                BinaryOp::And => "bvand",
                BinaryOp::Or => "bvor",
                BinaryOp::Xor => "bvxor",
                _ => unreachable!(),
            };
            format!("({op} {l} {r})")
        }
    }
}

pub fn pure_query(before: &Expr, after: &Expr) -> Result<PureQuery, UnknownReason> {
    let mut encoder = Encoder {
        definitions: vec![],
        registers: BTreeSet::new(),
        visits: 0,
    };
    let left = encoder.expression(before, 0)?;
    let right = encoder.expression(after, 0)?;
    let mut smt2 = format!(
        "; Nirvana {MODEL_ID}: all register inputs are unconstrained u64.\n(set-logic QF_BV)\n"
    );
    for index in &encoder.registers {
        smt2.push_str(&format!("(declare-fun r{index} () (_ BitVec 64))\n"));
    }
    for definition in encoder.definitions {
        smt2.push_str(&definition);
    }
    smt2.push_str(&format!("(assert (distinct {left} {right}))\n"));
    Ok(PureQuery {
        smt2,
        registers: encoder.registers.into_iter().collect(),
        before: before.clone(),
        after: after.clone(),
    })
}

#[derive(Clone, Debug)]
pub struct Solver {
    executable: PathBuf,
    timeout: Duration,
}

impl Solver {
    pub fn new(executable: impl Into<PathBuf>) -> Self {
        Self {
            executable: executable.into(),
            timeout: Duration::from_secs(2),
        }
    }
    pub fn with_timeout(mut self, timeout: Duration) -> Self {
        self.timeout = timeout.clamp(Duration::from_millis(1), Duration::from_secs(30));
        self
    }
    pub(crate) fn limited_to(&self, timeout: Duration) -> Self {
        self.clone().with_timeout(self.timeout.min(timeout))
    }
    pub fn check(&self, before: &Expr, after: &Expr) -> Verdict {
        match pure_query(before, after) {
            Ok(query) => self.check_query(&query),
            Err(reason) => Verdict::Unknown(reason),
        }
    }
    pub fn checked_rewrite(&self, before: &Expr, candidate: &Expr) -> CheckedRewrite {
        let verdict = self.check(before, candidate);
        let expression = if verdict == Verdict::EquivalentUnderModel {
            candidate
        } else {
            before
        }
        .clone();
        CheckedRewrite {
            expression,
            verdict,
        }
    }
    pub fn check_query(&self, query: &PureQuery) -> Verdict {
        let result = (|| match self.run(query, false)?.trim() {
            "unsat" => Ok(Verdict::EquivalentUnderModel),
            "unknown" => Ok(Verdict::Unknown(UnknownReason::SolverUnknown)),
            "sat" => {
                let values = if query.registers.is_empty() {
                    BTreeMap::new()
                } else {
                    parse_values(&self.run(query, true)?, &query.registers)?
                };
                Ok(Verdict::Counterexample(query.replay(&values)?))
            }
            other => Err(UnknownReason::InvalidResponse(
                other.chars().take(256).collect(),
            )),
        })();
        result.unwrap_or_else(Verdict::Unknown)
    }

    fn run(&self, query: &PureQuery, model: bool) -> Result<String, UnknownReason> {
        let names = if model {
            query
                .registers
                .iter()
                .map(|index| format!("r{index}"))
                .collect()
        } else {
            Vec::new()
        };
        self.run_smt(&query.smt2, &names)
    }

    pub(crate) fn run_smt(&self, smt2: &str, values: &[String]) -> Result<String, UnknownReason> {
        let mut script = format!(
            "(set-option :timeout {})\n(set-option :produce-models true)\n(set-option :pp.bv-literals true)\n{}(check-sat)\n",
            self.timeout.as_millis(),
            smt2
        );
        if !values.is_empty() {
            let names = values.join(" ");
            script.push_str(&format!("(get-value ({names}))\n"));
        }
        let mut child = Command::new(&self.executable)
            .args(["-in", "-smt2"])
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .map_err(|error| UnknownReason::SolverUnavailable(error.to_string()))?;
        let mut stdin = child.stdin.take().expect("piped stdin");
        let stdout = child.stdout.take().expect("piped stdout");
        let stderr = child.stderr.take().expect("piped stderr");
        // Drain both streams while writing, including on early parser errors.
        let writer = std::thread::spawn(move || stdin.write_all(script.as_bytes()));
        let reader = |stream: Box<dyn Read + Send>| {
            std::thread::spawn(move || {
                let mut bytes = Vec::new();
                stream
                    .take(1_048_577)
                    .read_to_end(&mut bytes)
                    .map(|_| bytes)
            })
        };
        let output = reader(Box::new(stdout));
        let errors = reader(Box::new(stderr));
        let deadline = Instant::now() + self.timeout + Duration::from_millis(200);
        let mut timed_out = false;
        let mut wait_error = None;
        loop {
            match child.try_wait() {
                Ok(Some(_)) => break,
                Err(error) => {
                    wait_error = Some(error.to_string());
                    let _ = child.kill();
                    break;
                }
                _ => {}
            }
            if Instant::now() >= deadline {
                timed_out = true;
                let _ = child.kill();
                break;
            }
            std::thread::sleep(Duration::from_millis(2));
        }
        let status = child.wait();
        let written = writer.join();
        let output = output.join();
        let errors = errors.join();
        if timed_out {
            return Err(UnknownReason::SolverTimeout);
        }
        if let Some(error) = wait_error {
            return Err(UnknownReason::SolverFailure(error));
        }
        let io_error = || UnknownReason::SolverFailure("solver process I/O failed".into());
        written.map_err(|_| io_error())?.map_err(|_| io_error())?;
        let output = output.map_err(|_| io_error())?.map_err(|_| io_error())?;
        let errors = errors.map_err(|_| io_error())?.map_err(|_| io_error())?;
        if !status.map_err(|_| io_error())?.success() || !errors.is_empty() {
            return Err(UnknownReason::SolverFailure(
                String::from_utf8_lossy(&errors).chars().take(256).collect(),
            ));
        }
        if output.len() > 1_048_576 {
            return Err(UnknownReason::ResourceLimit);
        }
        String::from_utf8(output)
            .map_err(|_| UnknownReason::InvalidResponse("non-UTF8 solver response".into()))
    }
}

fn parse_values(output: &str, expected: &[usize]) -> Result<BTreeMap<usize, u64>, UnknownReason> {
    let names: Vec<_> = expected.iter().map(|index| format!("r{index}")).collect();
    let values = parse_named_values(output, &names)?;
    Ok(expected
        .iter()
        .map(|&index| (index, values[&format!("r{index}")]))
        .collect())
}

pub(crate) fn parse_named_values(
    output: &str,
    expected: &[String],
) -> Result<BTreeMap<String, u64>, UnknownReason> {
    let error = || UnknownReason::InvalidResponse("malformed get-value response".into());
    let separated = output.replace('(', " ( ").replace(')', " ) ");
    let mut tokens = separated.split_whitespace();
    if tokens.next() != Some("sat") || tokens.next() != Some("(") {
        return Err(error());
    }
    let mut values = BTreeMap::new();
    loop {
        match tokens.next() {
            Some(")") => break,
            Some("(") => {}
            _ => return Err(error()),
        }
        let name = tokens.next().ok_or_else(error)?;
        let token = tokens.next().ok_or_else(error)?;
        let value = if let Some(hex) = token.strip_prefix("#x") {
            u64::from_str_radix(hex, 16).map_err(|_| error())?
        } else if let Some(binary) = token.strip_prefix("#b") {
            u64::from_str_radix(binary, 2).map_err(|_| error())?
        } else {
            return Err(error());
        };
        if tokens.next() != Some(")")
            || !expected.iter().any(|expected| expected == name)
            || values.insert(name.to_string(), value).is_some()
        {
            return Err(error());
        }
    }
    if tokens.next().is_some() || values.len() != expected.len() {
        return Err(error());
    }
    Ok(values)
}

//! Endpoint observations for the selected loop candidate; machine prefixes
//! retain their existing stage contract and original instruction budgets.
use nirvana::{
    ir::{AccessKind, Program, RunReport, RunStatus},
    readable::loop_recovery::Emission,
    transform::rolled_loop::EquivalenceProof,
};
use std::{fmt::Write, path::Path};

const MAX_RECORD_BYTES: usize = 16 * 1024 * 1024;

pub(super) struct Stage<'a> {
    emission: &'a Emission,
    limit: usize,
    cases: usize,
    observations: usize,
    status: &'static str,
    records: String,
    failure: Option<String>,
}
impl<'a> Stage<'a> {
    pub fn new(emission: &'a Emission, limit: usize) -> Self {
        Self {
            emission,
            limit,
            cases: 0,
            observations: 0,
            status: if emission.candidate().is_some() {
                "passed"
            } else {
                "not_applied"
            },
            records: String::new(),
            failure: None,
        }
    }
    pub fn observe(&mut self, input: &[u64], ram: &[u8], machine: &RunReport) {
        let case = self.cases;
        self.cases += 1;
        if self.status != "passed" {
            return;
        }
        let Some(candidate) = self.emission.candidate() else {
            return;
        };
        let recovery = candidate.recovery();
        for initial in [0, u64::MAX] {
            let mut display_input = vec![initial; recovery.source().register_count()];
            for (slot, &value) in display_input.iter_mut().zip(input) {
                *slot = value;
            }
            let run = || {
                let final_input = recovery
                    .extend_input(&display_input, initial)
                    .map_err(|e| e.to_string())?;
                let display = recovery
                    .source()
                    .run_with_memory(&display_input, super::BASE, ram, self.limit)
                    .map_err(|e| e.to_string())?;
                let recovered = recovery
                    .program()
                    .run_with_memory(&final_input, super::BASE, ram, self.limit)
                    .map_err(|e| e.to_string())?;
                Ok::<_, String>((display, recovered))
            };
            let (display, recovered) = match run() {
                Ok(pair) => pair,
                Err(error) => {
                    self.status = "rejected";
                    self.failure = Some(error);
                    return;
                }
            };
            let row = format!(
                "{{\"case\":{case},\"initial\":{initial},\"input\":{input:?},\"ram\":\"{}\",\"machine\":{},\"display\":{},\"recovered\":{}}}\n",
                hex(ram),
                endpoint(machine),
                endpoint(&display),
                endpoint(&recovered)
            );
            if self.records.len().saturating_add(row.len()) > MAX_RECORD_BYTES {
                self.status = "budget_exhausted";
                self.failure = Some("loop endpoint record budget".into());
                return;
            }
            self.records.push_str(&row);
            self.observations += 2;
            if [&machine.status, &display.status, &recovered.status]
                .contains(&&RunStatus::Suspended)
            {
                self.status = "budget_exhausted";
                self.failure = Some(format!(
                    "endpoint suspension at case {case}; step budgets are independent"
                ));
                return;
            }
            if !same_endpoint(machine, &display) || !same_endpoint(machine, &recovered) {
                self.status = "counterexample";
                self.failure = Some(format!(
                    "loop endpoint mismatch at case {case}, private initializer {initial}"
                ));
                return;
            }
        }
    }
    pub fn json(&self, out: &Path) -> std::io::Result<String> {
        let emission = self.emission;
        let retained = emission
            .retention()
            .map_or("null".into(), |r| format!("{:?}", r.kind()));
        let baseline = emission.baseline();
        let candidate = if let Some(candidate) = emission.candidate() {
            let recovery = candidate.recovery();
            for (name, program) in [
                ("loop-source.ir.txt", recovery.source()),
                ("loop-recovered.ir.txt", recovery.program()),
            ] {
                std::fs::write(out.join(name), program_text(program))?;
            }
            std::fs::write(out.join("loop-baseline.c"), &baseline.code)?;
            std::fs::write(out.join("loop-candidate.c"), &candidate.output().code)?;
            std::fs::write(out.join("loop-endpoints.jsonl"), &self.records)?;
            let verified = recovery.contextual().verified_region();
            std::fs::write(
                out.join("loop-completion.smt2"),
                verified.completion_query().smt2(),
            )?;
            std::fs::write(out.join("loop-comparison.smt2"), verified.query().smt2())?;
            let (method, checked) = match verified.equivalence_proof() {
                EquivalenceProof::ExhaustivePartitions { checked } => {
                    let problem = verified
                        .proposal()
                        .verification_problem()
                        .map_err(std::io::Error::other)?;
                    let partitions = problem.input_partitions().map_err(std::io::Error::other)?;
                    let scripts: Box<dyn Iterator<Item = String> + '_> = match &partitions {
                        Some(parts) => Box::new(parts.smt2()),
                        None => Box::new(verified.query().partition_smt2()),
                    };
                    let mut count = 0;
                    for (n, script) in scripts.enumerate() {
                        std::fs::write(out.join(format!("loop-part-{n}.smt2")), script)?;
                        count += 1;
                    }
                    if count != *checked {
                        return Err(std::io::Error::other("loop proof partition count"));
                    }
                    ("exhaustive_partitions", *checked)
                }
                EquivalenceProof::CutComposition(certificate) => {
                    for (n, obligation) in certificate.problem().obligations().iter().enumerate() {
                        std::fs::write(
                            out.join(format!("loop-cut-{n}.smt2")),
                            obligation.query().smt2(),
                        )?;
                    }
                    ("cut_composition", certificate.checked())
                }
            };
            let context = recovery.contextual().evidence();
            let parameters: Vec<_> = recovery.parameters().iter().map(|r| r.0).collect();
            format!(
                "{{\"source_registers\":{},\"program_registers\":{},\"parameters\":{parameters:?},\"group\":{},\"structured\":{},\"locals\":{},\"completion\":\"unsat\",\"proof_method\":\"{method}\",\"checked\":{checked},\"context_model\":\"{}\",\"outside_instructions\":{},\"original_region_instructions\":{},\"candidate_region_instructions\":{},\"future_reads_checked\":{},\"source_ir\":\"loop-source.ir.txt\",\"program_ir\":\"loop-recovered.ir.txt\",\"baseline_c\":\"loop-baseline.c\",\"candidate_c\":\"loop-candidate.c\",\"states\":\"loop-endpoints.jsonl\"}}",
                recovery.source().register_count(),
                recovery.program().register_count(),
                recovery.group(),
                candidate.output().fallback_reason.is_none(),
                candidate.output().locals.len(),
                nirvana::transform::rolled_loop::CONTEXT_MODEL_ID,
                context.outside_instructions,
                context.original_region_instructions,
                context.candidate_region_instructions,
                context.excluded_continuation_reads_checked
            )
        } else {
            "null".into()
        };
        let witness = if let Some(failure) = &self.failure {
            std::fs::write(out.join("loop-recovery.witness.txt"), failure)?;
            "\"loop-recovery.witness.txt\""
        } else {
            "null"
        };
        Ok(format!(
            "{{\"schema\":\"nirvana-loop-recovery-evaluation-v1\",\"model\":\"{}\",\"contract\":\"return-all-ram-first-fault-v1\",\"selected\":{},\"retention\":{retained},\"attempt_seconds\":{},\"baseline\":{{\"structured\":{},\"locals\":{}}},\"candidate\":{candidate},\"endpoint\":{{\"status\":\"{}\",\"cases\":{},\"observations\":{},\"step_limit\":{},\"private_initializers\":[0,{}],\"comparisons\":[\"display_zero\",\"recovered_zero\",\"display_ones\",\"recovered_ones\"],\"witness\":{witness}}}}}",
            nirvana::readable::loop_recovery::MODEL_ID,
            emission.accepted(),
            emission.elapsed().as_secs_f64(),
            baseline.fallback_reason.is_none(),
            baseline.locals.len(),
            self.status,
            self.cases,
            self.observations,
            self.limit,
            u64::MAX
        ))
    }
}
fn hex(bytes: &[u8]) -> String {
    let mut text = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        write!(text, "{byte:02x}").unwrap();
    }
    text
}
fn endpoint(report: &RunReport) -> String {
    let status = match report.status {
        RunStatus::Returned(value) => format!("{{\"kind\":\"returned\",\"value\":{value}}}"),
        RunStatus::Fault(fault) => format!(
            "{{\"kind\":\"fault\",\"address\":{},\"access\":\"{}\",\"width\":{}}}",
            fault.address,
            if fault.access == AccessKind::Read {
                "read"
            } else {
                "write"
            },
            fault.width.bytes()
        ),
        RunStatus::Suspended => "{\"kind\":\"suspended\"}".into(),
    };
    format!(
        "{{\"status\":{status},\"memory\":\"{}\"}}",
        hex(&report.state.memory)
    )
}
fn same_endpoint(a: &RunReport, b: &RunReport) -> bool {
    a.status == b.status && a.state.memory == b.state.memory
}
fn program_text(program: &Program) -> String {
    format!(
        "entry={} registers={}\n{:#?}\n",
        program.cfg().block(program.cfg().entry()).start,
        program.register_count(),
        program.instructions()
    )
}

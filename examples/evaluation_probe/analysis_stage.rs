//! Static source-bound checks; these are not concrete execution comparisons.
use nirvana::{
    dataflow::{memory_ssa, ssa::SsaFunction},
    ir::Program,
};

struct Check {
    status: &'static str,
    evidence: Option<String>,
    reason: Option<String>,
}
impl Check {
    fn unavailable(reason: String) -> Self {
        Self {
            status: "unavailable",
            evidence: None,
            reason: Some(reason),
        }
    }
    fn analysis_error(reason: String) -> Self {
        Self {
            status: if reason.starts_with("memory SSA check mismatch:") {
                "rejected"
            } else {
                "unavailable"
            },
            evidence: None,
            reason: Some(reason),
        }
    }
    fn checked<T>(
        result: Result<T, memory_ssa::ValidationError>,
        render: impl FnOnce(T) -> String,
    ) -> Self {
        match result {
            Ok(value) => Self {
                status: "passed",
                evidence: Some(render(value)),
                reason: None,
            },
            Err(error) => Self {
                status: if matches!(error, memory_ssa::ValidationError::Invalid(_)) {
                    "rejected"
                } else {
                    "unavailable"
                },
                evidence: None,
                reason: Some(error.to_string()),
            },
        }
    }
    fn json(&self, name: &str, model: &str, checker: &str, has_report: bool) -> String {
        format!(
            "{{\"name\":{name:?},\"model\":{model:?},\"checker\":{checker:?},\"status\":{:?},\"input_ir\":\"analysis-input.ir.txt\",\"memory_ssa\":{},\"evidence\":{},\"reason\":{}}}",
            self.status,
            if has_report {
                "\"memory-ssa.json\""
            } else {
                "null"
            },
            self.evidence.as_deref().unwrap_or("null"),
            self.reason
                .as_ref()
                .map_or("null".into(), |r| format!("{r:?}"))
        )
    }
}

pub(super) struct Stage {
    input: String,
    report: Option<String>,
    graph: Check,
    queries: Check,
}
impl Stage {
    pub fn new(source: &Program) -> Self {
        let input = format!(
            "entry={} registers={}\n{:#?}\n",
            source.cfg().block(source.cfg().entry()).start,
            source.register_count(),
            source.instructions()
        );
        let mut stage = Self {
            input,
            report: None,
            graph: Check::unavailable("register SSA unavailable".into()),
            queries: Check::unavailable("register SSA unavailable".into()),
        };
        let Some(registers) = SsaFunction::build(source) else {
            return stage;
        };
        let analysis = match memory_ssa::analyze(source, &registers) {
            Ok(analysis) => analysis,
            Err(reason) => {
                stage.graph = Check::analysis_error(reason.clone());
                stage.queries = Check::analysis_error(reason);
                return stage;
            }
        };
        stage.report = match analysis.to_json() {
            Ok(report) => Some(report),
            Err(reason) => {
                stage.graph = Check::unavailable(reason.clone());
                stage.queries = Check::unavailable(reason);
                return stage;
            }
        };
        stage.graph = Check::checked(
            memory_ssa::validate_graph(source, &registers, &analysis),
            |e| {
                format!(
                    "{{\"blocks\":{},\"definitions\":{},\"accesses\":{},\"phi_inputs\":{},\"opaque_effects\":{}}}",
                    e.blocks, e.definitions, e.accesses, e.phi_inputs, e.opaque_effects
                )
            },
        );
        stage.queries = match memory_ssa::validate(source, &registers, &analysis) {
            Ok(e) => match e.queries {
                Some(q) => Check::checked(Ok::<_, memory_ssa::ValidationError>(q), |q| {
                    format!(
                        "{{\"queries\":{},\"states\":{},\"links\":{},\"candidate_bytes\":{}}}",
                        q.queries, q.states, q.links, q.candidate_bytes
                    )
                }),
                None => Check::unavailable(
                    analysis
                        .queries()
                        .as_ref()
                        .err()
                        .cloned()
                        .unwrap_or_else(|| "query coverage unavailable".into()),
                ),
            },
            Err(error) => Check::checked(Err::<(), _>(error), |_| unreachable!()),
        };
        stage
    }
    pub fn statuses(&self) -> [&'static str; 2] {
        [self.graph.status, self.queries.status]
    }
    pub fn json(&self, out: &std::path::Path) -> std::io::Result<String> {
        std::fs::write(out.join("analysis-input.ir.txt"), &self.input)?;
        if let Some(report) = &self.report {
            std::fs::write(out.join("memory-ssa.json"), report)?;
        }
        Ok(format!(
            "[{},{}]",
            self.graph.json(
                "memory_ssa_graph",
                "nirvana-memory-ssa-graph-v1",
                "memory_ssa::validate_graph",
                self.report.is_some()
            ),
            self.queries.json(
                "memory_ssa_queries",
                "nirvana-memory-ssa-coverage-v1",
                "memory_ssa::validate",
                self.report.is_some()
            )
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::Check;

    #[test]
    fn builder_validation_failures_remain_rejections() {
        for (reason, expected) in [
            (
                "memory SSA check mismatch: uncovered predecessor bytes",
                "rejected",
            ),
            ("memory SSA check unavailable: work budget", "unavailable"),
            ("memory SSA query storage limit", "unavailable"),
        ] {
            let check = Check::analysis_error(reason.into());
            assert_eq!(check.status, expected);
            assert_eq!(check.reason.as_deref(), Some(reason));
            assert!(check.evidence.is_none());
        }
    }
}

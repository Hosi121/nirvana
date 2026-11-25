//! Static source-bound checks; these are not concrete execution comparisons.
use nirvana::{
    dataflow::{memory_ssa, ssa::SsaFunction, type_infer},
    ir::Program,
};

struct Check {
    status: &'static str,
    evidence: Option<String>,
    reason: Option<String>,
}
impl Check {
    fn passed(evidence: String) -> Self {
        Self {
            status: "passed",
            evidence: Some(evidence),
            reason: None,
        }
    }
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
    fn json(
        &self,
        name: &str,
        model: &str,
        checker: &str,
        report_field: &str,
        report_name: &str,
        has_report: bool,
    ) -> String {
        format!(
            "{{\"name\":{name:?},\"model\":{model:?},\"checker\":{checker:?},\"status\":{:?},\"input_ir\":\"analysis-input.ir.txt\",{report_field:?}:{},\"evidence\":{},\"reason\":{}}}",
            self.status,
            if has_report {
                format!("{report_name:?}")
            } else {
                "null".into()
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
    types: Option<String>,
    graph: Check,
    queries: Check,
    addresses: Check,
    bounds: Check,
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
            types: None,
            graph: Check::unavailable("register SSA unavailable".into()),
            queries: Check::unavailable("register SSA unavailable".into()),
            addresses: Check::unavailable("register SSA unavailable".into()),
            bounds: Check::unavailable("unsigned bound analysis unavailable".into()),
        };
        // Type/layout candidates do not establish a source-language type. Only
        // the separately checked unsigned storage upper bounds are claimed.
        if let Some(types) = type_infer::TypeAnalysis::analyze(source) {
            if let Some(report) = types.to_json() {
                stage.types = Some(report);
                let bits: Vec<_> = types.values().iter().map(|v| v.maximum_bits).collect();
                stage.bounds = match type_infer::check_bounds(source, types.graph(), &bits) {
                    Ok(e) => Check::passed(format!(
                        "{{\"values\":{},\"assignments\":{},\"phi_inputs\":{},\"expressions\":{}}}",
                        e.values, e.assignments, e.phi_inputs, e.expressions
                    )),
                    Err(reason) => Check {
                        status: if reason.contains("limit") || reason.contains("unavailable") {
                            "unavailable"
                        } else {
                            "rejected"
                        },
                        evidence: None,
                        reason: Some(reason),
                    },
                };
            } else {
                stage.bounds = Check::unavailable("unsigned bound report limit".into());
            }
        }
        let Some(registers) = SsaFunction::build(source) else {
            return stage;
        };
        let analysis = match memory_ssa::analyze(source, &registers) {
            Ok(analysis) => analysis,
            Err(reason) => {
                stage.graph = Check::analysis_error(reason.clone());
                stage.queries = Check::analysis_error(reason.clone());
                stage.addresses = Check::analysis_error(reason);
                return stage;
            }
        };
        stage.report = match analysis.to_json() {
            Ok(report) => Some(report),
            Err(reason) => {
                stage.graph = Check::unavailable(reason.clone());
                stage.queries = Check::unavailable(reason.clone());
                stage.addresses = Check::unavailable(reason);
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
            Ok(e) => {
                let a = e.addresses;
                stage.addresses = Check::passed(format!(
                    "{{\"accesses\":{},\"modular_forms\":{},\"phi_inputs\":{},\"phi_checked\":{},\"source_atoms\":{},\"basis_evaluations\":{}}}",
                    a.accesses,
                    a.modular_forms,
                    a.phi_inputs,
                    a.phi_checked,
                    a.source_atoms,
                    a.basis_evaluations
                ));
                match e.queries {
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
                }
            }
            Err(error) => {
                stage.addresses = Check::checked(Err::<(), _>(error.clone()), |_| unreachable!());
                Check::checked(Err::<(), _>(error), |_| unreachable!())
            }
        };
        stage
    }
    pub fn statuses(&self) -> [&'static str; 4] {
        [
            self.graph.status,
            self.queries.status,
            self.addresses.status,
            self.bounds.status,
        ]
    }
    pub fn json(&self, out: &std::path::Path) -> std::io::Result<String> {
        std::fs::write(out.join("analysis-input.ir.txt"), &self.input)?;
        if let Some(report) = &self.report {
            std::fs::write(out.join("memory-ssa.json"), report)?;
        }
        if let Some(report) = &self.types {
            std::fs::write(out.join("type-constraints.json"), report)?;
        }
        Ok(format!(
            "[{},{},{},{}]",
            self.graph.json(
                "memory_ssa_graph",
                "nirvana-memory-ssa-graph-v1",
                "memory_ssa::validate_graph",
                "memory_ssa",
                "memory-ssa.json",
                self.report.is_some()
            ),
            self.queries.json(
                "memory_ssa_queries",
                "nirvana-memory-ssa-coverage-v1",
                "memory_ssa::validate",
                "memory_ssa",
                "memory-ssa.json",
                self.report.is_some()
            ),
            self.addresses.json(
                "memory_addresses",
                "nirvana-modular-address-v1",
                "memory_ssa::validate",
                "memory_ssa",
                "memory-ssa.json",
                self.report.is_some()
            ),
            self.bounds.json(
                "unsigned_bounds",
                "nirvana-unsigned-bounds-v1",
                "type_infer::check_bounds",
                "type_constraints",
                "type-constraints.json",
                self.types.is_some()
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

//! Bind the selected render's consumed unsigned facts to their actual source.
use nirvana::{
    dataflow::value_width::{self, ValidationError},
    readable::{ReadableC, StorageProvenance, StorageSnapshot, StorageSourcePhase},
};
use std::collections::BTreeSet;
use std::fmt::{self, Write};

const MAX_BYTES: usize = 16 * 1024 * 1024;
const MODEL: &str = "nirvana-selected-storage-v1";

struct Text(String);
impl Write for Text {
    fn write_str(&mut self, text: &str) -> fmt::Result {
        if self
            .0
            .len()
            .checked_add(text.len())
            .is_none_or(|n| n > MAX_BYTES)
        {
            return Err(fmt::Error);
        }
        self.0.push_str(text);
        Ok(())
    }
}

fn quote(text: &str) -> String {
    let mut result = String::from("\"");
    for character in text.chars() {
        match character {
            '"' => result.push_str("\\\""),
            '\\' => result.push_str("\\\\"),
            '\n' => result.push_str("\\n"),
            '\r' => result.push_str("\\r"),
            '\t' => result.push_str("\\t"),
            c if c < ' ' => write!(result, "\\u{:04x}", c as u32).unwrap(),
            c => result.push(c),
        }
    }
    result.push('"');
    result
}

struct Failure(&'static str, String);
impl Failure {
    fn unavailable(reason: impl Into<String>) -> Self {
        Self("unavailable", reason.into())
    }
    fn invalid(reason: &str) -> Self {
        Self("rejected", reason.into())
    }
}
impl From<ValidationError> for Failure {
    fn from(error: ValidationError) -> Self {
        Self(
            if matches!(error, ValidationError::Invalid(_)) {
                "rejected"
            } else {
                "unavailable"
            },
            error.to_string(),
        )
    }
}

struct Artifacts {
    source: String,
    manifest: String,
    code: String,
}

pub(super) struct Stage {
    pub status: &'static str,
    artifacts: Option<Artifacts>,
    evidence: Option<String>,
    reason: Option<String>,
}

impl Stage {
    pub fn new(output: &ReadableC) -> Self {
        let result = match &output.storage_provenance {
            StorageProvenance::Captured(snapshot) => build(snapshot, output),
            StorageProvenance::NotCaptured => {
                Err(Failure::unavailable("selected storage not captured"))
            }
            StorageProvenance::Unavailable(reason) => Err(Failure::unavailable(*reason)),
            StorageProvenance::Rejected(reason) => Err(Failure::invalid(reason)),
        };
        match result {
            Ok((artifacts, evidence)) => Self {
                status: "passed",
                artifacts: Some(artifacts),
                evidence: Some(evidence),
                reason: None,
            },
            Err(Failure(status, reason)) => Self {
                status,
                artifacts: None,
                evidence: None,
                reason: Some(reason),
            },
        }
    }

    pub fn json(&self, out: &std::path::Path) -> std::io::Result<String> {
        let reason = self.reason.as_deref().map_or("null".into(), quote);
        let input = if let Some(artifacts) = &self.artifacts {
            std::fs::write(out.join("selected-storage-input.ir.txt"), &artifacts.source)?;
            std::fs::write(out.join("selected-storage.json"), &artifacts.manifest)?;
            std::fs::write(out.join("selected-readable.c"), &artifacts.code)?;
            "\"selected-storage-input.ir.txt\""
        } else {
            let manifest = format!(
                "{{\"schema\":\"{MODEL}\",\"scope\":\"selected-c-unsigned-width-observations\",\"status\":{:?},\"source_phase\":null,\"registers\":null,\"entry\":null,\"certificate\":null,\"parameters\":null,\"locals\":null,\"reason\":{reason}}}",
                self.status
            );
            std::fs::write(out.join("selected-storage.json"), manifest)?;
            "null"
        };
        let code = if self.artifacts.is_some() {
            "\"selected-readable.c\""
        } else {
            "null"
        };
        Ok(format!(
            "{{\"name\":\"selected_storage\",\"model\":\"{MODEL}\",\"checker\":\"value_width::validate+selected_storage::validate_locals\",\"status\":{:?},\"input_ir\":{input},\"selected_storage\":\"selected-storage.json\",\"emitted_c\":{code},\"evidence\":{},\"reason\":{reason}}}",
            self.status,
            self.evidence.as_deref().unwrap_or("null")
        ))
    }
}

fn validate_locals(snapshot: &StorageSnapshot, output: &ReadableC) -> Result<usize, Failure> {
    if output.locals.len() > 100_000 {
        return Err(Failure::unavailable("selected local count limit"));
    }
    let count = snapshot.source.register_count();
    let mut parameters = BTreeSet::new();
    for register in &output.parameters {
        if register.0 >= count || !parameters.insert(register.0) {
            return Err(Failure::invalid("selected parameter register"));
        }
    }
    let mut names = BTreeSet::new();
    let mut members = 0usize;
    for local in &output.locals {
        if local.name.is_empty()
            || local.name.len() > 256
            || !names.insert(&local.name)
            || !local
                .name
                .bytes()
                .enumerate()
                .all(|(i, c)| c == b'_' || c.is_ascii_alphabetic() || i > 0 && c.is_ascii_digit())
        {
            return Err(Failure::invalid("selected local name"));
        }
        let mut registers = BTreeSet::new();
        if local.registers.is_empty() {
            return Err(Failure::invalid("selected local lacks members"));
        }
        members = members
            .checked_add(local.registers.len())
            .filter(|&n| n <= 1_000_000)
            .ok_or_else(|| Failure::unavailable("selected local member limit"))?;
        for &register in &local.registers {
            if register.0 >= count || !registers.insert(register.0) {
                return Err(Failure::invalid("selected local member register"));
            }
            if local.width.bits() < snapshot.widths.width(register).bits() {
                return Err(Failure::invalid(
                    "selected unsigned local narrower than member",
                ));
            }
        }
    }
    Ok(members)
}

fn build(snapshot: &StorageSnapshot, output: &ReadableC) -> Result<(Artifacts, String), Failure> {
    // Recheck the retained proposal; never replace it with a new analysis.
    let (Some(widths), Some(incoming)) = (snapshot.widths.widths(), snapshot.widths.incoming())
    else {
        return Err(match snapshot.widths.verification() {
            Err(error) => (*error).into(),
            Ok(_) => Failure::invalid("checked selected storage facts missing"),
        });
    };
    let evidence = value_width::validate(&snapshot.source, widths, incoming)?;
    let members = validate_locals(snapshot, output)?;
    if output.code.len() > MAX_BYTES {
        return Err(Failure::unavailable("selected C artifact limit"));
    }
    let certificate = snapshot.widths.to_json().map_err(Failure::unavailable)?;
    let source = &snapshot.source;
    let entry = source.cfg().block(source.cfg().entry()).start;
    let mut input = Text(String::new());
    write!(
        input,
        "entry={entry} registers={}\n{:#?}\n",
        source.register_count(),
        source.instructions()
    )
    .map_err(|_| Failure::unavailable("selected input artifact limit"))?;
    let mut manifest = Text(String::new());
    let phase = match snapshot.source_phase {
        StorageSourcePhase::BeforePresentation => "before-presentation",
        StorageSourcePhase::DisplayAfterDce => "display-after-dce",
    };
    let parameters: Vec<_> = output.parameters.iter().map(|r| r.0).collect();
    write!(manifest,
        "{{\"schema\":\"{MODEL}\",\"scope\":\"selected-c-unsigned-width-observations\",\"status\":\"checked\",\"source_phase\":\"{phase}\",\"registers\":{},\"entry\":{entry},\"certificate\":{certificate},\"parameters\":{parameters:?},\"locals\":[",
        source.register_count()).map_err(|_| Failure::unavailable("selected manifest artifact limit"))?;
    for (index, local) in output.locals.iter().enumerate() {
        let registers: Vec<_> = local.registers.iter().map(|r| r.0).collect();
        let optional = |value: Option<nirvana::ir::Width>| {
            value.map_or("null".into(), |w| w.bits().to_string())
        };
        write!(manifest,
            "{}{{\"name\":{},\"registers\":{registers:?},\"unsigned_bits\":{},\"signed_bits\":{},\"address_bits\":{}}}",
            if index == 0 { "" } else { "," }, quote(&local.name), local.width.bits(), optional(local.signed_width), optional(local.address_width))
            .map_err(|_| Failure::unavailable("selected manifest artifact limit"))?;
    }
    manifest
        .write_str("],\"reason\":null}")
        .map_err(|_| Failure::unavailable("selected manifest artifact limit"))?;
    let e = evidence;
    let evidence = format!(
        "{{\"registers\":{},\"narrow_registers\":{},\"blocks\":{},\"edges\":{},\"assignments\":{},\"reads\":{},\"expressions\":{},\"local_variables\":{},\"local_members\":{members},\"parameters\":{}}}",
        e.registers,
        e.narrow_registers,
        e.blocks,
        e.edges,
        e.assignments,
        e.reads,
        e.expressions,
        output.locals.len(),
        output.parameters.len()
    );
    Ok((
        Artifacts {
            source: input.0,
            manifest: manifest.0,
            code: output.code.clone(),
        },
        evidence,
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    use nirvana::{
        ir::{Assignment, Control, Expr, IrInstruction, Place, Program, Reg, Width},
        readable::{self, ReadableOptions},
    };
    use std::sync::Arc;

    fn source(width: Width) -> Program {
        Program::new(
            0,
            1,
            vec![IrInstruction {
                address: 0,
                size: 1,
                assignments: vec![Assignment {
                    destination: Place::Register(Reg(0)),
                    value: Expr::load(Expr::Const(4096), width),
                }],
                control: Control::Return(Expr::Register(Reg(0))),
            }],
        )
        .unwrap()
    }

    #[test]
    fn selected_certificate_is_rechecked_against_its_retained_source() {
        let good = source(Width::U8);
        let mut output =
            readable::emit_readable_c_with_storage_provenance(&good, ReadableOptions::default())
                .unwrap();
        assert_eq!(Stage::new(&output).status, "passed");
        output.storage_provenance = StorageProvenance::Captured(Arc::new(StorageSnapshot {
            source: Arc::new(source(Width::U64)),
            widths: value_width::ValueWidths::analyze(&good),
            source_phase: StorageSourcePhase::BeforePresentation,
        }));
        let rejected = Stage::new(&output);
        assert_eq!(rejected.status, "rejected");
        assert!(rejected.artifacts.is_none());
    }

    #[test]
    fn missing_capture_known_rejection_and_artifact_limits_remain_explicit() {
        let mut output = readable::emit_readable_c_with_storage_provenance(
            &source(Width::U8),
            ReadableOptions::default(),
        )
        .unwrap();
        output.code = "x".repeat(MAX_BYTES + 1);
        assert_eq!(Stage::new(&output).status, "unavailable");
        output.storage_provenance = StorageProvenance::Rejected("bad consumed facts");
        assert_eq!(Stage::new(&output).status, "rejected");
        output.storage_provenance = StorageProvenance::NotCaptured;
        assert_eq!(Stage::new(&output).status, "unavailable");
    }
}

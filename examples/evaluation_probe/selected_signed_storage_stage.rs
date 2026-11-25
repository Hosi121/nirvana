//! Bind signed local choices to the exact final display source and checked SSA.
use super::storage_artifacts::{Failure, MAX_BYTES, Text, quote};
use nirvana::{
    dataflow::signed_width::{self, ValidationError},
    readable::{ReadableC, SignedStorageProvenance, SignedStorageSnapshot},
};
use std::collections::BTreeSet;
use std::fmt::Write;

const MODEL: &str = "nirvana-selected-signed-storage-v1";

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
    ssa: String,
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
        let result = match &output.signed_storage_provenance {
            SignedStorageProvenance::Captured(snapshot) => build(snapshot, output),
            SignedStorageProvenance::NotCaptured => {
                Err(Failure::unavailable("selected signed storage not captured"))
            }
            SignedStorageProvenance::Unavailable(reason) => Err(Failure::unavailable(*reason)),
            SignedStorageProvenance::Rejected(reason) => Err(Failure::invalid(reason)),
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
        if let Some(a) = &self.artifacts {
            std::fs::write(out.join("selected-signed-input.ir.txt"), &a.source)?;
            std::fs::write(out.join("selected-signed-ssa.txt"), &a.ssa)?;
            std::fs::write(out.join("selected-signed-storage.json"), &a.manifest)?;
            std::fs::write(out.join("selected-signed-readable.c"), &a.code)?;
        } else {
            std::fs::write(
                out.join("selected-signed-storage.json"),
                format!(
                    "{{\"schema\":\"{MODEL}\",\"scope\":\"selected-c-sign-extension-observations\",\"status\":{:?},\"source_phase\":null,\"registers\":null,\"entry\":null,\"certificate\":null,\"parameters\":null,\"locals\":null,\"reason\":{reason}}}",
                    self.status
                ),
            )?;
        }
        let name = |s: &str| {
            if self.artifacts.is_some() {
                quote(s)
            } else {
                "null".into()
            }
        };
        Ok(format!(
            "{{\"name\":\"selected_signed_storage\",\"model\":\"{MODEL}\",\"checker\":\"signed_width::validate+selected_signed_storage::validate_locals\",\"status\":{:?},\"input_ir\":{},\"input_ssa\":{},\"selected_signed_storage\":\"selected-signed-storage.json\",\"emitted_c\":{},\"evidence\":{},\"reason\":{reason}}}",
            self.status,
            name("selected-signed-input.ir.txt"),
            name("selected-signed-ssa.txt"),
            name("selected-signed-readable.c"),
            self.evidence.as_deref().unwrap_or("null")
        ))
    }
}

fn validate_locals(
    snapshot: &SignedStorageSnapshot,
    output: &ReadableC,
) -> Result<(usize, usize, usize), Failure> {
    if output.locals.len() > 100_000 {
        return Err(Failure::unavailable("selected signed local count limit"));
    }
    let count = snapshot.source.register_count();
    let mut assigned = BTreeSet::new();
    for r in &output.parameters {
        if r.0 >= count || !assigned.insert(r.0) {
            return Err(Failure::invalid("selected signed parameter register"));
        }
    }
    let mut names = BTreeSet::new();
    let (mut members, mut signed_locals, mut signed_members) = (0usize, 0usize, 0usize);
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
            return Err(Failure::invalid("selected signed local name"));
        }
        if local.registers.is_empty() {
            return Err(Failure::invalid("selected signed local lacks members"));
        }
        members = members
            .checked_add(local.registers.len())
            .filter(|&n| n <= 1_000_000)
            .ok_or_else(|| Failure::unavailable("selected signed local member limit"))?;
        for r in &local.registers {
            if r.0 >= count || !assigned.insert(r.0) {
                return Err(Failure::invalid("selected signed member assigned twice"));
            }
        }
        if let Some(width) = local.signed_width {
            if local.width != nirvana::ir::Width::U64
                || local.address_width.is_some()
                || width == nirvana::ir::Width::U64
                || local
                    .registers
                    .iter()
                    .any(|&r| snapshot.widths.width(r) > width)
            {
                return Err(Failure::invalid(
                    "selected signed local narrower than member",
                ));
            }
            signed_locals += 1;
            signed_members += local.registers.len();
        }
    }
    Ok((members, signed_locals, signed_members))
}

fn build(
    snapshot: &SignedStorageSnapshot,
    output: &ReadableC,
) -> Result<(Artifacts, String), Failure> {
    let e = signed_width::validate(&snapshot.source, &snapshot.widths)?;
    let (members, signed_locals, signed_members) = validate_locals(snapshot, output)?;
    if output.code.len() > MAX_BYTES {
        return Err(Failure::unavailable("selected signed C artifact limit"));
    }
    let certificate = snapshot.widths.to_json().map_err(Failure::unavailable)?;
    let graph = snapshot
        .widths
        .ssa()
        .ok_or_else(|| Failure::invalid("selected signed checked SSA missing"))?;
    let source = &snapshot.source;
    let entry = source.cfg().block(source.cfg().entry()).start;
    let mut input = Text(String::new());
    write!(
        input,
        "entry={entry} registers={}\n{:#?}\n",
        source.register_count(),
        source.instructions()
    )
    .map_err(|_| Failure::unavailable("selected signed source artifact limit"))?;
    let mut ssa = Text(String::new());
    write!(
        ssa,
        "entry={} registers={} values={}\n{graph:#?}\n",
        graph.entry,
        graph.register_count,
        graph.values.len()
    )
    .map_err(|_| Failure::unavailable("selected signed SSA artifact limit"))?;
    let parameters: Vec<_> = output.parameters.iter().map(|r| r.0).collect();
    let mut manifest = Text(String::new());
    write!(manifest,"{{\"schema\":\"{MODEL}\",\"scope\":\"selected-c-sign-extension-observations\",\"status\":\"checked\",\"source_phase\":\"prepared-display\",\"registers\":{},\"entry\":{entry},\"certificate\":{certificate},\"parameters\":{parameters:?},\"locals\":[",source.register_count())
        .map_err(|_| Failure::unavailable("selected signed manifest artifact limit"))?;
    for (i, local) in output.locals.iter().enumerate() {
        let regs: Vec<_> = local.registers.iter().map(|r| r.0).collect();
        let optional =
            |w: Option<nirvana::ir::Width>| w.map_or("null".into(), |w| w.bits().to_string());
        write!(manifest,"{}{{\"name\":{},\"registers\":{regs:?},\"unsigned_bits\":{},\"signed_bits\":{},\"address_bits\":{}}}",if i==0 {""} else {","},quote(&local.name),local.width.bits(),optional(local.signed_width),optional(local.address_width))
            .map_err(|_| Failure::unavailable("selected signed manifest artifact limit"))?;
    }
    manifest
        .write_str("],\"reason\":null}")
        .map_err(|_| Failure::unavailable("selected signed manifest artifact limit"))?;
    let evidence = format!(
        "{{\"registers\":{},\"narrow_registers\":{},\"values\":{},\"constants\":{},\"blocks\":{},\"phi_inputs\":{},\"assignments\":{},\"reads\":{},\"expressions\":{},\"local_variables\":{},\"local_members\":{members},\"signed_locals\":{signed_locals},\"signed_members\":{signed_members},\"parameters\":{}}}",
        e.registers,
        e.narrow_registers,
        e.values,
        e.constants,
        e.blocks,
        e.phi_inputs,
        e.assignments,
        e.reads,
        e.expressions,
        output.locals.len(),
        output.parameters.len()
    );
    Ok((
        Artifacts {
            source: input.0,
            ssa: ssa.0,
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
        ir::{Assignment, Control, Expr, IrInstruction, Program, Reg, UnaryOp, Width},
        readable::{self, ReadableOptions},
    };
    use std::sync::Arc;

    fn source(width: Width) -> Program {
        Program::new(
            0,
            2,
            vec![IrInstruction {
                address: 0,
                size: 1,
                assignments: vec![Assignment {
                    destination: Reg(1).into(),
                    value: Expr::unary(UnaryOp::SignExtend(width), Expr::Register(Reg(0))),
                }],
                control: Control::Return(Expr::Register(Reg(1))),
            }],
        )
        .unwrap()
    }
    #[test]
    fn retained_source_local_widths_and_capture_status_are_independently_checked() {
        let p = source(Width::U8);
        let mut output =
            readable::emit_readable_c_with_storage_provenance(&p, ReadableOptions::default())
                .unwrap();
        assert_eq!(Stage::new(&output).status, "passed");
        output.signed_storage_provenance =
            SignedStorageProvenance::Captured(Arc::new(SignedStorageSnapshot {
                source: Arc::new(source(Width::U64)),
                widths: signed_width::SignedWidths::analyze(&p),
            }));
        assert_eq!(Stage::new(&output).status, "rejected");
        output.signed_storage_provenance = SignedStorageProvenance::NotCaptured;
        assert_eq!(Stage::new(&output).status, "unavailable");
        output.signed_storage_provenance =
            SignedStorageProvenance::Rejected("known invalid signed facts");
        assert_eq!(Stage::new(&output).status, "rejected");
    }

    #[test]
    fn incompatible_signed_local_metadata_cannot_use_a_checked_source_certificate() {
        let p = source(Width::U32);
        let mut output =
            readable::emit_readable_c_with_storage_provenance(&p, ReadableOptions::default())
                .unwrap();
        let snapshot = Arc::new(SignedStorageSnapshot {
            source: Arc::new(p.clone()),
            widths: signed_width::SignedWidths::analyze(&p),
        });
        output.signed_storage_provenance = SignedStorageProvenance::Captured(snapshot);
        output.locals.push(readable::LocalValue {
            register: Reg(1),
            registers: vec![Reg(1)],
            name: "forged".into(),
            width: Width::U64,
            signed_width: Some(Width::U8),
            address_width: None,
            role: None,
        });
        assert_eq!(Stage::new(&output).status, "rejected");
    }
}

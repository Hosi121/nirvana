//! Bounded source-entry sign-extension observations and retained claims.

use super::{Claim, SignedWidths, ValidationError};
use std::fmt::Display;

const MAX_REPORT_BYTES: usize = 16 * 1024 * 1024;

struct Json {
    text: String,
    limit: usize,
}

impl Json {
    fn raw(&mut self, text: &str) -> Result<(), String> {
        if self
            .text
            .len()
            .checked_add(text.len())
            .is_none_or(|length| length > self.limit)
        {
            return Err("signed storage report size limit".into());
        }
        self.text.push_str(text);
        Ok(())
    }

    fn number(&mut self, value: impl Display) -> Result<(), String> {
        self.raw(&value.to_string())
    }

    fn string(&mut self, text: &str) -> Result<(), String> {
        self.raw("\"")?;
        for character in text.chars() {
            match character {
                '"' => self.raw("\\\"")?,
                '\\' => self.raw("\\\\")?,
                '\n' => self.raw("\\n")?,
                '\r' => self.raw("\\r")?,
                '\t' => self.raw("\\t")?,
                character if character < ' ' => {
                    self.raw(&format!("\\u{:04x}", u32::from(character)))?
                }
                character => self.raw(character.encode_utf8(&mut [0; 4]))?,
            }
        }
        self.raw("\"")
    }
}

pub(super) fn render(value: &SignedWidths) -> Result<String, String> {
    render_bounded(value, MAX_REPORT_BYTES)
}

fn render_bounded(value: &SignedWidths, limit: usize) -> Result<String, String> {
    let mut out = Json {
        text: String::new(),
        limit,
    };
    out.raw("{\"schema\":\"nirvana-signed-storage-v1\",\"scope\":\"source-entry-sign-extension-observations\",\"status\":")?;
    match value.verification() {
        Err(error) => {
            out.string(match error {
                ValidationError::Invalid(_) => "rejected",
                ValidationError::Unavailable(_) => "unavailable",
            })?;
            out.raw(",\"evidence\":null,\"widths\":null,\"values\":null,\"entry\":null,\"registers\":null,\"reason\":")?;
            out.string(&error.to_string())?;
        }
        Ok(evidence) => {
            let widths = value
                .widths()
                .ok_or("signed storage report missing widths")?;
            let certificate = value
                .certificate
                .as_ref()
                .ok_or("signed storage report missing certificate")?;
            if widths.len() != evidence.registers
                || certificate.claims.len() != evidence.values
                || certificate.graph.register_count != evidence.registers
            {
                return Err("signed storage report dimensions".into());
            }
            out.raw("\"checked\",\"evidence\":{\"registers\":")?;
            out.number(evidence.registers)?;
            for (name, count) in [
                ("narrow_registers", evidence.narrow_registers),
                ("values", evidence.values),
                ("constants", evidence.constants),
                ("blocks", evidence.blocks),
                ("phi_inputs", evidence.phi_inputs),
                ("assignments", evidence.assignments),
                ("reads", evidence.reads),
                ("expressions", evidence.expressions),
            ] {
                out.raw(",")?;
                out.string(name)?;
                out.raw(":")?;
                out.number(count)?;
            }
            out.raw("},\"widths\":[")?;
            for (index, width) in widths.iter().enumerate() {
                if index != 0 {
                    out.raw(",")?;
                }
                out.number(width.bits())?;
            }
            out.raw("],\"values\":[")?;
            for (index, claim) in certificate.claims.iter().enumerate() {
                if index != 0 {
                    out.raw(",")?;
                }
                match claim {
                    Claim::Constant(number) => {
                        out.raw("{\"constant\":")?;
                        out.number(number)?;
                    }
                    Claim::Fits(width) => {
                        out.raw("{\"signed_bits\":")?;
                        out.number(width.bits())?;
                    }
                }
                out.raw("}")?;
            }
            out.raw("],\"entry\":")?;
            out.number(certificate.graph.entry)?;
            out.raw(",\"registers\":")?;
            out.number(certificate.graph.register_count)?;
            out.raw(",\"reason\":null")?;
        }
    }
    out.raw("}")?;
    Ok(out.text)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::model::ir::{
        Assignment, Control, Expr, IrInstruction, Program, Reg, UnaryOp, Width,
    };
    use std::sync::Arc;

    fn source() -> Program {
        Program::new(
            16,
            4,
            vec![
                IrInstruction {
                    address: 0,
                    size: 1,
                    assignments: vec![],
                    control: Control::Return(Expr::Const(0)),
                },
                IrInstruction {
                    address: 16,
                    size: 1,
                    assignments: vec![
                        Assignment {
                            destination: Reg(1).into(),
                            value: Expr::Const(255),
                        },
                        Assignment {
                            destination: Reg(2).into(),
                            value: Expr::unary(
                                UnaryOp::SignExtend(Width::U8),
                                Expr::Register(Reg(0)),
                            ),
                        },
                        Assignment {
                            destination: Reg(3).into(),
                            value: Expr::Const(u64::MAX),
                        },
                    ],
                    control: Control::Return(Expr::Register(Reg(1))),
                },
            ],
        )
        .unwrap()
    }

    #[test]
    fn checked_report_retains_exact_claim_objects_and_shares_certificate() {
        let source = source();
        let widths = SignedWidths::analyze(&source);
        let evidence = widths.verification().unwrap();
        assert_eq!(
            widths.widths(),
            Some([Width::U64, Width::U16, Width::U8, Width::U8].as_slice())
        );
        assert_eq!(widths.ssa().unwrap().entry, 16);
        assert_eq!(widths.ssa().unwrap().blocks.len(), 1);
        assert_eq!(widths.ssa().unwrap().values.len(), evidence.values);
        assert_eq!(evidence.constants, 2);
        assert_eq!(evidence.narrow_registers, 3);
        assert_eq!(evidence.assignments, 3);
        assert_eq!(evidence.reads, 2);
        assert_eq!(evidence.expressions, 5);
        assert_eq!(
            super::super::validate(&source, &widths).as_ref(),
            widths.verification()
        );
        let cloned = widths.clone();
        assert!(Arc::ptr_eq(
            widths.certificate.as_ref().unwrap(),
            cloned.certificate.as_ref().unwrap()
        ));
        let report = widths.to_json().unwrap();
        assert!(report.starts_with("{\"schema\":\"nirvana-signed-storage-v1\",\"scope\":\"source-entry-sign-extension-observations\",\"status\":\"checked\""));
        assert!(report.contains("\"widths\":[64,16,8,8],\"values\":["));
        assert!(report.contains("{\"constant\":255}"));
        assert!(report.contains("{\"constant\":18446744073709551615}"));
        assert!(report.contains("{\"signed_bits\":8}"));
        assert!(report.contains("{\"signed_bits\":64}"));
        assert!(report.ends_with("\"entry\":16,\"registers\":4,\"reason\":null}"));
        assert_eq!(cloned.to_json().unwrap(), report);
        assert_eq!(render_bounded(&widths, report.len()).unwrap(), report);
        assert!(render_bounded(&widths, report.len() - 1).is_err());
    }

    #[test]
    fn unavailable_and_rejected_reports_keep_reasons_and_no_partial_facts() {
        for (value, status, reason) in [
            (SignedWidths::default(), "unavailable", "not analyzed"),
            (
                SignedWidths::failed(ValidationError::Invalid("bad \"claim\"\n")),
                "rejected",
                r#"bad \"claim\"\n"#,
            ),
        ] {
            assert!(value.widths().is_none());
            assert!(value.ssa().is_none());
            assert_eq!(value.width(Reg(1)), Width::U64);
            assert_eq!(value.width(Reg(usize::MAX)), Width::U64);
            let report = value.to_json().unwrap();
            assert!(report.contains(&format!("\"status\":\"{status}\"")));
            assert!(report.contains("\"evidence\":null,\"widths\":null,\"values\":null,\"entry\":null,\"registers\":null"));
            assert!(report.contains(reason));
            assert!(!report.contains("\"reason\":null"));
        }
    }
}

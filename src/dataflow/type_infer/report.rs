use super::*;
use crate::dataflow::ssa::Definition;
use std::fmt::Write as _;
const MAX_REPORT_BYTES: usize = 16 * 1024 * 1024;
fn site(site: Site) -> String {
    format!(
        "{{\"instruction\":{},\"assignment\":{}}}",
        site.instruction,
        site.assignment
            .map_or_else(|| "null".into(), |n| n.to_string())
    )
}
fn ids(values: &[ValueId]) -> String {
    format!(
        "[{}]",
        values
            .iter()
            .map(|n| n.0.to_string())
            .collect::<Vec<_>>()
            .join(",")
    )
}
fn uses(value: Uses) -> String {
    let fields = [
        ("signed_compare", value.signed_compare),
        ("unsigned_compare", value.unsigned_compare),
        ("logical_shift", value.logical_shift),
        ("bitwise", value.bitwise),
        ("address_base", value.address_base),
        ("address_index", value.address_index),
        ("returned", value.returned),
        ("stored", value.stored),
    ];
    format!(
        "[{}]",
        fields
            .into_iter()
            .filter(|(_, set)| *set)
            .map(|(name, _)| format!("\"{name}\""))
            .collect::<Vec<_>>()
            .join(",")
    )
}
fn shape(value: AddressShape) -> String {
    match value {
        AddressShape::Unknown => "{\"kind\":\"unknown\"}".into(),
        AddressShape::Absolute(n) => format!("{{\"kind\":\"absolute\",\"address\":{n}}}"),
        AddressShape::Base {
            base,
            offset,
            index,
        } => format!(
            "{{\"kind\":\"affine\",\"base\":{},\"offset\":{},\"offset_bits\":\"0x{:016x}\",\"index\":{}}}",
            base.0,
            offset as i64,
            offset,
            index.map_or_else(
                || "null".into(),
                |i| format!(
                    "{{\"value\":{},\"stride\":{},\"stride_bits\":\"0x{:016x}\"}}",
                    i.value.0, i.stride as i64, i.stride
                )
            )
        ),
    }
}
fn paths(path: &[PathEdge]) -> String {
    format!(
        "[{}]",
        path.iter()
            .map(|p| match p {
                PathEdge::Left => "\"left\"",
                PathEdge::Right => "\"right\"",
                PathEdge::Address => "\"address\"",
                PathEdge::Condition => "\"condition\"",
                PathEdge::Taken => "\"taken\"",
                PathEdge::NotTaken => "\"not_taken\"",
            })
            .collect::<Vec<_>>()
            .join(",")
    )
}
fn check(out: &str) -> Option<()> {
    (out.len() <= MAX_REPORT_BYTES).then_some(())
}
pub(super) fn render(analysis: &TypeAnalysis) -> Option<String> {
    let mut out = String::from(
        "{\n  \"schema\":\"nirvana-type-constraints-v1\",\n  \"identity\":\"ssa\",\n  \"access_model\":\"syntactic-possible\",\n  \"interpretations\":\"tentative\",\n  \"values\":[\n",
    );
    for (i, (definition, fact)) in analysis
        .graph
        .values
        .iter()
        .zip(&analysis.facts)
        .enumerate()
    {
        if i > 0 {
            out.push_str(",\n");
        }
        let origin = match definition {
            Definition::Initial { register } => {
                format!("{{\"kind\":\"initial\",\"register\":{}}}", register.0)
            }
            Definition::Assignment {
                site: point,
                register,
            } => format!(
                "{{\"kind\":\"assignment\",\"register\":{},\"site\":{}}}",
                register.0,
                site(*point)
            ),
            Definition::Phi {
                block,
                register,
                inputs,
            } => format!(
                "{{\"kind\":\"phi\",\"block\":{block},\"register\":{},\"inputs\":[{}]}}",
                register.0,
                inputs
                    .iter()
                    .map(|p| format!(
                        "{{\"predecessor\":{},\"value\":{}}}",
                        p.predecessor
                            .map_or_else(|| "null".into(), |n| n.to_string()),
                        p.value.0
                    ))
                    .collect::<Vec<_>>()
                    .join(",")
            ),
        };
        let storage = match fact.maximum_bits {
            0..=8 => 8,
            9..=16 => 16,
            17..=32 => 32,
            _ => 64,
        };
        write!(out,"    {{\"id\":{i},\"alias\":{},\"origin\":{origin},\"maximum_bits\":{},\"storage_bits_candidate\":{storage},\"direct_uses\":{},\"flow_uses\":{}}}",analysis.aliases[i].0,fact.maximum_bits,uses(fact.direct_uses),uses(fact.flow_uses)).ok()?;
        check(&out)?;
    }
    out.push_str("\n  ],\n  \"accesses\":[\n");
    for (i, a) in analysis.accesses.iter().enumerate() {
        if i > 0 {
            out.push_str(",\n");
        }
        let operand = match a.operand {
            Operand::Destination => "destination",
            Operand::Value => "value",
            Operand::Control => "control",
        };
        let kind = match a.kind {
            AccessKind::Read => "read",
            AccessKind::Write => "write",
        };
        write!(out,"    {{\"site\":{},\"operand\":\"{operand}\",\"path\":{},\"kind\":\"{kind}\",\"width\":{},\"address\":{},\"result\":{}}}",site(a.site),paths(&a.path),a.width.bytes(),shape(a.address),a.result.map_or_else(||"null".into(),|n|n.0.to_string())).ok()?;
        check(&out)?;
    }
    out.push_str("\n  ],\n  \"layout_candidates\":[\n");
    for (i, layout) in analysis.layouts.iter().enumerate() {
        if i > 0 {
            out.push_str(",\n");
        }
        write!(out, "    {{\"base\":{},\"fields\":[", layout.base.0).ok()?;
        for (i, f) in layout.fields.iter().enumerate() {
            if i > 0 {
                out.push(',');
            }
            write!(out,"{{\"offset\":{},\"offset_bits\":\"0x{:016x}\",\"width\":{},\"reads\":{},\"writes\":{},\"loaded_values\":{}}}",f.offset as i64,f.offset,f.width.bytes(),f.reads,f.writes,ids(&f.loaded_values)).ok()?;
            check(&out)?;
        }
        out.push_str("],\"arrays\":[");
        for (i, a) in layout.arrays.iter().enumerate() {
            if i > 0 {
                out.push(',');
            }
            write!(out,"{{\"offset\":{},\"offset_bits\":\"0x{:016x}\",\"stride\":{},\"stride_bits\":\"0x{:016x}\",\"width\":{},\"indices\":{},\"loaded_values\":{},\"reads\":{},\"writes\":{}}}",a.offset as i64,a.offset,a.stride as i64,a.stride,a.width.bytes(),ids(&a.indices),ids(&a.loaded_values),a.reads,a.writes).ok()?;
            check(&out)?;
        }
        write!(
            out,
            "],\"overlaps\":[{}],\"ambiguous_intervals\":{}}}",
            layout
                .overlaps
                .iter()
                .map(|(a, b)| format!("[{a},{b}]"))
                .collect::<Vec<_>>()
                .join(","),
            layout.ambiguous_intervals
        )
        .ok()?;
        check(&out)?;
    }
    out.push_str("\n  ]\n}\n");
    check(&out)?;
    Some(out)
}

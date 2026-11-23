use super::*;
use crate::dataflow::address_identity::{AddressShape, Operand};
use std::fmt::Write;

const MAX_REPORT_BYTES: usize = 16 * 1024 * 1024;

pub(super) fn render(analysis: &Analysis) -> Result<String, String> {
    let mut out = String::from(
        "{\"schema\":\"nirvana-memory-ssa-v1\",\"status\":\"analyzed\",\"scope\":\"function-entry-normal-continuations\",\"reads\":\"syntactic-possible\"",
    );
    if let Some(e) = analysis.graph_evidence() {
        write!(out, ",\"verification\":{{\"model\":\"nirvana-memory-ssa-graph-v1\",\"scope\":\"source-bound-generations\",\"blocks\":{},\"definitions\":{},\"accesses\":{},\"phi_inputs\":{},\"opaque_effects\":{}}}",
            e.blocks,e.definitions,e.accesses,e.phi_inputs,e.opaque_effects).unwrap();
    }
    out.push_str(",\"definitions\":[");
    for (id, definition) in analysis.definitions.iter().enumerate() {
        if id > 0 {
            out.push(',');
        }
        write!(out, "{{\"id\":{id},\"kind\":").unwrap();
        match definition {
            Definition::Initial => out.push_str("\"initial\""),
            Definition::Phi { block, inputs } => {
                write!(out, "\"phi\",\"block\":{block},\"inputs\":[").unwrap();
                for (i, input) in inputs.iter().enumerate() {
                    if i > 0 {
                        out.push(',');
                    }
                    out.push_str("{\"predecessor\":");
                    match input.predecessor {
                        Some(p) => write!(out, "{p}").unwrap(),
                        None => out.push_str("null"),
                    }
                    write!(out, ",\"memory\":{}}}", input.memory.0).unwrap();
                }
                out.push(']');
            }
            Definition::Store { access, previous } => {
                write!(
                    out,
                    "\"store\",\"access\":{access},\"previous\":{}",
                    previous.0
                )
                .unwrap();
            }
            Definition::Opaque { effect, previous } => {
                write!(out, "\"opaque\",\"instruction\":{},\"phase\":\"{}\",\"effect\":\"{}\",\"previous\":{}",
                    effect.instruction, if effect.phase == Phase::Before { "before" } else { "after" },
                    match effect.kind { EffectKind::CallStack => "call-stack", EffectKind::Call => "call", EffectKind::StringStore => "string-store", EffectKind::StringMove => "string-move" },previous.0).unwrap();
            }
        }
        out.push('}');
        bound(&out)?;
    }
    out.push_str("],\"blocks\":[");
    for (i, block) in analysis.blocks.iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
        write!(
            out,
            "{{\"start\":{},\"entry\":{},\"exit\":{},\"events\":[",
            block.start, block.entry.0, block.exit.0
        )
        .unwrap();
        for (j, event) in block.events.iter().enumerate() {
            if j > 0 {
                out.push(',');
            }
            match event {
                Event::Access(id) => write!(out, "{{\"access\":{id}}}").unwrap(),
                Event::Effect(id) => write!(out, "{{\"effect\":{}}}", id.0).unwrap(),
            }
        }
        out.push_str("]}");
        bound(&out)?;
    }
    out.push_str("],\"accesses\":[");
    for (id, access) in analysis.accesses.iter().enumerate() {
        if id > 0 {
            out.push(',');
        }
        let a = &access.source;
        write!(
            out,
            "{{\"id\":{id},\"instruction\":{},\"assignment\":",
            a.site.instruction
        )
        .unwrap();
        match a.site.assignment {
            Some(i) => write!(out, "{i}").unwrap(),
            None => out.push_str("null"),
        }
        write!(
            out,
            ",\"operand\":\"{}\",\"path\":[",
            match a.operand {
                Operand::Destination => "destination",
                Operand::Value => "value",
                Operand::Control => "control",
            }
        )
        .unwrap();
        for (i, edge) in a.path.iter().enumerate() {
            if i > 0 {
                out.push(',');
            }
            write!(out, "\"{edge:?}\"").unwrap();
        }
        write!(
            out,
            "],\"kind\":\"{}\",\"width\":{},\"incoming\":{},\"definition\":",
            if a.kind == AccessKind::Read {
                "read"
            } else {
                "write"
            },
            a.width.bits(),
            access.incoming.0
        )
        .unwrap();
        match access.definition {
            Some(id) => write!(out, "{}", id.0).unwrap(),
            None => out.push_str("null"),
        }
        out.push_str(",\"address\":");
        match a.address {
            AddressShape::Unknown => out.push_str("{\"kind\":\"unknown\"}"),
            AddressShape::Absolute(address) => {
                write!(out, "{{\"kind\":\"absolute\",\"address\":{address}}}").unwrap()
            }
            AddressShape::Base {
                base,
                offset,
                index,
            } => {
                write!(
                    out,
                    "{{\"kind\":\"base\",\"value\":{},\"offset\":{offset},\"index\":",
                    base.0
                )
                .unwrap();
                match index {
                    Some(index) => write!(
                        out,
                        "{{\"value\":{},\"stride\":{}}}",
                        index.value.0, index.stride
                    )
                    .unwrap(),
                    None => out.push_str("null"),
                }
                out.push('}');
            }
        }
        out.push_str(",\"identity\":");
        if let Some(address) = &access.address {
            write!(out, "{{\"offset\":{},\"terms\":[", address.offset).unwrap();
            for (i, (value, coefficient)) in address.terms.iter().enumerate() {
                if i > 0 {
                    out.push(',');
                }
                write!(
                    out,
                    "{{\"value\":{},\"coefficient\":{coefficient}}}",
                    value.0
                )
                .unwrap();
            }
            out.push_str("]}");
        } else {
            out.push_str("null");
        }
        out.push('}');
        bound(&out)?;
    }
    out.push_str("],\"queries\":{");
    match &analysis.queries {
        Ok(queries) => {
            out.push_str("\"status\":\"analyzed\",\"reads\":[");
            for (i, query) in queries.iter().enumerate() {
                if i > 0 {
                    out.push(',');
                }
                write!(out, "{{\"access\":{},\"translated_edges\":{},\"address_widened\":{},\"candidates\":[", query.access,query.translated_edges,query.address_widened).unwrap();
                for (j, candidate) in query.candidates.iter().enumerate() {
                    if j > 0 {
                        out.push(',');
                    }
                    write!(
                        out,
                        "{{\"definition\":{},\"alias\":\"{}\",\"byte_mask\":{},\"byte_sources\":{:?},\"unknown_bytes\":{}}}",
                        candidate.definition.0,
                        match candidate.alias {
                            Alias::Disjoint => "disjoint",
                            Alias::Exact => "exact",
                            Alias::Overlap => "overlap",
                            Alias::May => "may",
                        },
                        candidate.byte_mask,
                        candidate.byte_sources,
                        candidate.unknown_bytes,
                    )
                    .unwrap();
                }
                out.push_str("]}");
                bound(&out)?;
            }
            out.push(']');
        }
        Err(reason) => {
            // Query failures are fixed ASCII resource messages from walk.rs.
            write!(out, "\"status\":\"unavailable\",\"reason\":{reason:?}").unwrap();
        }
    }
    out.push_str("}}");
    bound(&out)?;
    Ok(out)
}

fn bound(out: &str) -> Result<(), String> {
    if out.len() > MAX_REPORT_BYTES {
        Err("memory SSA report size limit".into())
    } else {
        Ok(())
    }
}

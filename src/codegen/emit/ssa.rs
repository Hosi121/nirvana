//! C rendering for checked SSA destruction; storage analysis stays in dataflow.
use crate::dataflow::ssa_destroy::LoweredFunction;

const MAX_C_BYTES: usize = 32 * 1024 * 1024;

impl LoweredFunction {
    /// Named local storage with the same full-register C interface as `emit_c`.
    /// Original checked memory operations and canonical register writes remain.
    pub fn emit_c(&self) -> Result<super::COutput, String> {
        use std::fmt::Write as _;
        let mut output = super::emit_c(self.program()).map_err(|e| e.to_string())?;
        let mut declarations = String::from("    (void)r;\n");
        for local in 0..self.plan().local_count {
            writeln!(
                declarations,
                "    uint64_t v_{local} = UINT64_C(0); (void)v_{local};"
            )
            .unwrap();
            if declarations.len() > MAX_C_BYTES {
                return Err("SSA C declaration limit".into());
            }
        }
        declarations.push_str("    uint64_t phi_tmp = UINT64_C(0), phi_condition = UINT64_C(0);\n    (void)phi_tmp; (void)phi_condition;\n");
        for &(local, register) in self.initializations() {
            writeln!(declarations, "    v_{local} = r[{}];", register.0).unwrap();
        }
        if let Some(edge) = self
            .edges()
            .iter()
            .find(|e| e.from.is_none() && e.to == self.entry())
        {
            for copy in &edge.schedule.copies {
                writeln!(
                    declarations,
                    "    {} = {};",
                    self.local_name(copy.destination),
                    self.local_name(copy.source)
                )
                .unwrap();
            }
        }
        let marker = "    (void)r;\n";
        if output.code.matches(marker).count() != 1 {
            return Err("SSA C function entry unavailable".into());
        }
        output.code = output.code.replacen(marker, &declarations, 1);
        output.code = self.name_storage(&output.code)?;
        Ok(output)
    }

    fn local_name(&self, local: usize) -> String {
        if local == self.plan().local_count {
            "phi_tmp".into()
        } else if local == self.plan().local_count + 1 {
            "phi_condition".into()
        } else {
            format!("v_{local}")
        }
    }

    fn name_storage(&self, code: &str) -> Result<String, String> {
        // The source here is exclusively our C emitter: fixed register tokens,
        // no user identifiers or string literals containing array expressions.
        let mut out = String::new();
        let mut rest = code;
        while let Some(at) = rest.find("r[") {
            out.push_str(&rest[..at]);
            rest = &rest[at..];
            let end = rest.find(']').ok_or("SSA C register token")?;
            let register = rest[2..end]
                .parse::<usize>()
                .map_err(|_| "SSA C register index")?;
            if register < self.source_register_count() {
                out.push_str(&rest[..=end]);
            } else {
                out.push_str(&self.local_name(register - self.source_register_count()));
            }
            rest = &rest[end + 1..];
            if out.len() > MAX_C_BYTES {
                return Err("SSA C output limit".into());
            }
        }
        out.push_str(rest);
        if out.len() > MAX_C_BYTES {
            return Err("SSA C output limit".into());
        }
        Ok(out)
    }
}

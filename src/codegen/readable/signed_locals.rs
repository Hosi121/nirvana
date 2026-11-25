//! Decode checked signed storage at ordinary U64 reads. Assignment conversion
//! and scalar integer promotions stay separate from the register allocator.
use super::*;

pub(super) fn recover(
    program: &Program,
    locals: &mut [LocalValue],
    addresses: &BTreeSet<usize>,
) -> (
    BTreeMap<usize, Width>,
    crate::dataflow::signed_width::SignedWidths,
) {
    let facts = crate::dataflow::signed_width::SignedWidths::analyze(program);
    let mut result = BTreeMap::new();
    for local in locals {
        if local.width != Width::U64
            || local.address_width.is_some()
            || local.registers.iter().any(|r| addresses.contains(&r.0))
        {
            continue;
        }
        let width = local
            .registers
            .iter()
            .map(|&r| facts.width(r))
            .max()
            .unwrap_or(Width::U64);
        if width == Width::U64 {
            continue;
        }
        local.signed_width = Some(width);
        for reg in &local.registers {
            result.insert(reg.0, width);
        }
    }
    (result, facts)
}

impl Printer<'_> {
    fn signed_operand(&self, value: &Expr, bits: u32, point: Option<(u64, usize)>) -> String {
        if let Expr::Register(reg) = value
            && self
                .signed_widths
                .get(&reg.0)
                .is_some_and(|w| w.bits() <= bits)
        {
            return self.register(*reg);
        }
        let width = match bits {
            8 => Width::U8,
            16 => Width::U16,
            32 => Width::U32,
            _ => unreachable!(),
        };
        format!(
            "nirvana_signed{bits}({})",
            self.expression_at(stored_value(value, width), point).text
        )
    }
    pub(super) fn signed_word_operation(
        &self,
        operation: crate::transform::word_signed_division::Operation,
        value: &Expr,
        divisor: i64,
        bits: u32,
        point: Option<(u64, usize)>,
    ) -> String {
        let op = match operation {
            crate::transform::word_signed_division::Operation::Quotient => "/",
            crate::transform::word_signed_division::Operation::Remainder => "%",
        };
        format!("{} {op} {divisor}", self.signed_operand(value, bits, point))
    }
    pub(super) fn signed_statement(
        &self,
        code: &mut String,
        indent: usize,
        value: &Expr,
        point: Option<(u64, usize)>,
        prefix: &str,
        width: Width,
    ) -> Result<(), SequenceError> {
        if needs_sequence(value) {
            // Preserve the existing ordered-load plan, then decode once.
            return self.value_statement(
                code,
                indent,
                value,
                point,
                &format!("{prefix}nirvana_signed{}(", width.bits()),
                ");",
            );
        }
        let normalized = self.normalize_arithmetic(value, point);
        let value = &normalized;
        let text = match value {
            Expr::Const(n) => (*n as i64).to_string(),
            Expr::Register(reg) if self.signed_widths.get(&reg.0).is_some_and(|w| *w <= width) => {
                self.register(*reg)
            }
            Expr::Unary(crate::model::ir::UnaryOp::SignExtend(w), inner) if *w != Width::U64 => {
                self.signed_operand(inner, w.bits(), point)
            }
            _ => match idioms::recognize(value) {
                Some(idioms::View::WordSignedExtended {
                    operation,
                    value,
                    divisor,
                    bits,
                }) => self.signed_word_operation(operation, value, divisor, bits, point),
                _ => format!(
                    "nirvana_signed{}({})",
                    width.bits(),
                    self.expression_at(value, point).text
                ),
            },
        };
        line(code, indent, &format!("{prefix}{text};"));
        Ok(())
    }
}

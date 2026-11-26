//! C syntax emission from the prepared function and validated views.
use super::*;

pub(super) struct Printer<'a> {
    pub(super) source_program: &'a Program,
    pub(super) context_remainders:
        Option<&'a crate::transform::context_remainder::ContextRemainders>,
    pub(super) graph_remainders: Option<&'a crate::transform::remainder_graph::GraphRemainders>,
    pub(super) names: BTreeMap<usize, String>,
    pub(super) read: BTreeSet<usize>,
    pub(super) views: Option<MemoryViews>,
    pub(super) first_temporary: usize,
    pub(super) widths: BTreeMap<usize, Width>,
    pub(super) signed_widths: BTreeMap<usize, Width>,
    pub(super) address_types: BTreeMap<usize, Width>,
    pub(super) address_uses: BTreeSet<usize>,
    pub(super) recover_objects: bool,
    pub(super) compact_memory: bool,
    pub(super) slots: BTreeMap<usize, usize>,
    pub(super) initial_slots: Vec<usize>,
    pub(super) declarations: Rc<DeclarationPlan>,
}

/// Borrow the original setup sites. A setup-bearing test runs as statements at
/// the top of the body, including the final visit and every local continue.
pub(super) struct LoopHeader<'a> {
    pub(super) text: String,
    pub(super) setup: &'a [Node],
    pub(super) test: Option<Expr>,
    pub(super) body: &'a [Node],
}

impl Printer<'_> {
    pub(super) fn normalize_arithmetic(&self, expr: &Expr, point: Option<(u64, usize)>) -> Expr {
        crate::transform::simplify::word_arithmetic(expr, |value| {
            matches!(value, Expr::Load { .. })
                || idioms::recognize(value).is_some()
                || self.context_remainder(value, point).is_some()
        })
    }
    pub(super) fn context_remainder(
        &self,
        expression: &Expr,
        point: Option<(u64, usize)>,
    ) -> Option<crate::transform::context_remainder::ContextView<'_>> {
        if !matches!(expression, Expr::Binary(BinaryOp::Sub, _, _)) {
            return None;
        }
        let (instruction, assignment) = point?;
        self.context_remainders
            .and_then(|plan| plan.view(self.source_program, instruction, assignment, expression))
            .or_else(|| {
                let view = self.graph_remainders?.view(
                    self.source_program,
                    instruction,
                    assignment,
                    expression,
                )?;
                Some(crate::transform::context_remainder::ContextView {
                    value: view.value,
                    divisor: view.divisor,
                    maximum_remainder: view.maximum_remainder,
                    quotient: view.quotient,
                })
            })
    }

    pub(super) fn expression(&self, expr: &Expr) -> Render {
        self.expression_at(expr, None)
    }

    pub(super) fn expression_at(&self, expr: &Expr, point: Option<(u64, usize)>) -> Render {
        let atom = |text, unsigned| Render {
            text,
            unsigned,
            precedence: 13,
        };
        if let Some(view) = self.context_remainder(expr, point) {
            return Render {
                text: format!(
                    "{} % {}",
                    self.expression_at(view.value, point).u64(),
                    self.expression(&Expr::Const(view.divisor)).text
                ),
                unsigned: true,
                precedence: 11,
            };
        }
        if let Some(view) = idioms::recognize(expr) {
            return match view {
                idioms::View::WordSignedExtended {
                    operation,
                    value,
                    divisor,
                    bits,
                } => atom(
                    format!(
                        "(uint64_t)({})",
                        self.signed_word_operation(operation, value, divisor, bits, point)
                    ),
                    true,
                ),
                idioms::View::WordSigned {
                    name,
                    value,
                    divisor,
                    bits,
                } => {
                    let literal = if divisor == i64::MIN {
                        "INT64_MIN".to_owned()
                    } else if divisor < 0 {
                        format!("-INT64_C({})", divisor.unsigned_abs())
                    } else {
                        format!("INT64_C({divisor})")
                    };
                    atom(
                        format!(
                            "{name}({}, {literal}, {bits})",
                            self.expression_at(value, point).text
                        ),
                        true,
                    )
                }
                idioms::View::Signed {
                    name,
                    value,
                    divisor,
                } => {
                    let literal = if divisor == i64::MIN {
                        "INT64_MIN".to_owned()
                    } else if divisor < 0 {
                        format!("-INT64_C({})", divisor.unsigned_abs())
                    } else {
                        format!("INT64_C({divisor})")
                    };
                    atom(
                        format!(
                            "{name}({}, {literal})",
                            self.expression_at(value, point).text
                        ),
                        true,
                    )
                }
                idioms::View::Call { name, arguments } => {
                    let arguments = arguments
                        .into_iter()
                        .map(|argument| self.expression_at(argument, point).text)
                        .collect::<Vec<_>>()
                        .join(", ");
                    atom(format!("{name}({arguments})"), true)
                }
                idioms::View::Divide { value, divisor } => Render {
                    text: format!(
                        "{} / {}",
                        self.expression_at(value, point).u64(),
                        self.expression(&Expr::Const(divisor)).text
                    ),
                    unsigned: true,
                    precedence: 11,
                },
                idioms::View::Remainder { value, divisor } => Render {
                    text: format!(
                        "{} % {}",
                        self.expression_at(value, point).u64(),
                        self.expression(&Expr::Const(divisor)).text
                    ),
                    unsigned: true,
                    precedence: 11,
                },
            };
        }
        let normalized = self.normalize_arithmetic(expr, point);
        if normalized != *expr {
            return self.expression_at(&normalized, point);
        }
        match expr {
            Expr::Unary(crate::model::ir::UnaryOp::Extract { start, width }, value) => {
                let value = self.expression_at(value, point);
                if *start >= 64 {
                    return Render {
                        text: format!("{} & 0", value.u64()),
                        unsigned: true,
                        precedence: 6,
                    };
                }
                let shifted = if *start == 0 {
                    Render {
                        text: value.u64(),
                        unsigned: true,
                        precedence: 13,
                    }
                } else {
                    Render {
                        text: format!("{} >> {start}", value.u64()),
                        unsigned: true,
                        precedence: 9,
                    }
                };
                if *width == Width::U64 {
                    return shifted;
                }
                Render {
                    text: format!(
                        "{} & {}",
                        shifted.child(12),
                        self.expression(&Expr::Const(width.mask())).text
                    ),
                    unsigned: true,
                    precedence: 6,
                }
            }
            Expr::Unary(op, value) => atom(
                crate::codegen::emit::integer::unary_expression(
                    *op,
                    &self.expression_at(value, point).text,
                ),
                true,
            ),
            Expr::Const(value) if *value <= i32::MAX as u64 => atom(value.to_string(), false),
            Expr::Const(value) => atom(format!("UINT64_C(0x{value:x})"), true),
            Expr::Register(reg) if self.signed_widths.contains_key(&reg.0) => {
                atom(format!("(uint64_t){}", self.register(*reg)), true)
            }
            Expr::Register(reg) => atom(
                self.register(*reg),
                self.widths.get(&reg.0).copied().unwrap_or(Width::U64) == Width::U64,
            ),
            Expr::Load { address, width } => atom(self.load(point, address, address, *width), true),
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => {
                let condition = self.expression_at(condition, point);
                let taken = self.expression_at(taken, point);
                let not_taken = self.expression_at(not_taken, point);
                Render {
                    text: format!(
                        "{} ? {} : {}",
                        condition.child(3),
                        taken.text,
                        not_taken.child(2)
                    ),
                    precedence: 2,
                    unsigned: taken.unsigned || not_taken.unsigned,
                }
            }
            Expr::Binary(op, left, right) => {
                // Truth wrappers are introduced by control-flow rendering.
                // Only remove/invert these wrappers; general algebra here can
                // erase a variable after dependency/allocation analysis.
                if matches!(op, BinaryOp::Eq | BinaryOp::Ne)
                    && matches!(**right, Expr::Const(0))
                    && matches!(
                        **left,
                        Expr::Binary(
                            BinaryOp::Eq | BinaryOp::Ne | BinaryOp::Ult | BinaryOp::Ule,
                            ..
                        )
                    )
                {
                    if *op == BinaryOp::Ne {
                        return self.expression_at(left, point);
                    }
                    let Expr::Binary(inner, a, b) = &**left else {
                        unreachable!()
                    };
                    if matches!(inner, BinaryOp::Eq | BinaryOp::Ne) {
                        let complement = if *inner == BinaryOp::Eq {
                            BinaryOp::Ne
                        } else {
                            BinaryOp::Eq
                        };
                        return self.expression_at(
                            &Expr::binary(complement, (**a).clone(), (**b).clone()),
                            point,
                        );
                    }
                    let symbol = match inner {
                        BinaryOp::Ult => ">=",
                        BinaryOp::Ule => ">",
                        _ => unreachable!(),
                    };
                    return Render {
                        text: format!(
                            "{} {symbol} {}",
                            self.expression_at(a, point).child(9),
                            self.expression_at(b, point).child(9)
                        ),
                        precedence: 8,
                        unsigned: false,
                    };
                }
                if *op == BinaryOp::Add
                    && let Expr::Const(value) = **left
                    && !matches!(**right, Expr::Const(_))
                {
                    return self.expression_at(
                        &Expr::binary(BinaryOp::Add, (**right).clone(), Expr::Const(value)),
                        point,
                    );
                }
                if *op == BinaryOp::Add
                    && let Expr::Const(value) = **right
                    && value > i64::MAX as u64
                {
                    return self.expression_at(
                        &Expr::binary(
                            BinaryOp::Sub,
                            (**left).clone(),
                            Expr::Const(value.wrapping_neg()),
                        ),
                        point,
                    );
                }
                let l = self.expression_at(left, point);
                let r = self.expression_at(right, point);
                if let Some(call) =
                    crate::codegen::emit::integer::helper_call(*op, &l.text, &r.text)
                {
                    return atom(call, true);
                }
                let (symbol, precedence) = match op {
                    BinaryOp::Or => ("|", 4),
                    BinaryOp::Xor => ("^", 5),
                    BinaryOp::And => ("&", 6),
                    BinaryOp::Eq => ("==", 7),
                    BinaryOp::Ne => ("!=", 7),
                    BinaryOp::Ult => ("<", 8),
                    BinaryOp::Ule => ("<=", 8),
                    BinaryOp::Shl => ("<<", 9),
                    BinaryOp::Shr => (">>", 9),
                    BinaryOp::Add => ("+", 10),
                    BinaryOp::Sub => ("-", 10),
                    BinaryOp::Mul => ("*", 11),
                    BinaryOp::UMulHigh
                    | BinaryOp::SMulHigh
                    | BinaryOp::AShr
                    | BinaryOp::UDiv
                    | BinaryOp::URem
                    | BinaryOp::SDiv
                    | BinaryOp::SRem
                    | BinaryOp::Insert { .. } => unreachable!(),
                };
                let comparison = matches!(
                    op,
                    BinaryOp::Eq | BinaryOp::Ne | BinaryOp::Ult | BinaryOp::Ule
                );
                let shift = matches!(op, BinaryOp::Shl | BinaryOp::Shr);
                // A comparison in C has type int. Promote before wrapping
                // arithmetic and before a shift, not after a possible overflow.
                let promote = !comparison && (!l.unsigned && (!r.unsigned || shift));
                let bitwise = matches!(op, BinaryOp::And | BinaryOp::Or | BinaryOp::Xor);
                // Equal bitwise operators associate without changing any bits.
                // Keep mixed/arithmetic operands parenthesized for C warnings.
                let bitwise_precedence = |operand: &Expr| {
                    if matches!(operand, Expr::Binary(inner, ..) if inner == op) {
                        precedence
                    } else {
                        12
                    }
                };
                let operand_precedence = if bitwise {
                    bitwise_precedence(left)
                } else if shift {
                    12
                } else if comparison {
                    9
                } else {
                    precedence
                };
                let left_text = if promote {
                    l.u64()
                } else {
                    l.child(operand_precedence)
                };
                let right_text = if shift && !bounded_shift(right) {
                    format!("({} & 63)", r.child(12))
                } else {
                    r.child(if bitwise {
                        bitwise_precedence(right)
                    } else if comparison {
                        9
                    } else {
                        precedence + 1
                    })
                };
                Render {
                    text: format!("{left_text} {symbol} {right_text}"),
                    precedence,
                    unsigned: !comparison,
                }
            }
        }
    }

    pub(super) fn address_value(
        &self,
        reg: Reg,
        point: Option<(u64, usize)>,
        value: &Expr,
    ) -> Option<String> {
        if !self.address_uses.contains(&reg.0) {
            return None;
        }
        self.address_view(point, value)
            .map(|view| format!("{view}.address"))
    }

    pub(super) fn address_view(
        &self,
        point: Option<(u64, usize)>,
        address: &Expr,
    ) -> Option<String> {
        if let Some(view) = self.views.as_ref().and_then(|v| v.at(point, address)) {
            return Some(view.render(self.compact_memory, |index| self.expression(index).text));
        }
        if !self.recover_objects {
            return None;
        }
        // Borrow the current address's operands. An SSA alias representative
        // may no longer occupy its old C slot, so it cannot supply new reads.
        let view = crate::transform::access_expr::recognize(address)?;
        if !crate::transform::access_expr::validate(address, &view) {
            return None;
        }
        let base = self.expression(view.base).text;
        let index = self.expression(view.index).text;
        if self.compact_memory {
            let element = format!(
                "element({base}, {index}, {})",
                syntax::argument(view.stride)
            );
            Some(if view.offset == 0 {
                element
            } else {
                format!("field({element}, {})", syntax::argument(view.offset))
            })
        } else {
            Some(format!(
                "nirvana_view_index((struct nirvana_view){{{base}}}, {index}, UINT64_C({}), UINT64_C({}))",
                view.stride, view.offset
            ))
        }
    }

    pub(super) fn local_type(&self, reg: Reg) -> String {
        local_type(
            self.widths.get(&reg.0).copied().unwrap_or(Width::U64),
            self.address_types.get(&reg.0).copied(),
            self.signed_widths.get(&reg.0).copied(),
        )
    }

    pub(super) fn load(
        &self,
        point: Option<(u64, usize)>,
        address: &Expr,
        original: &Expr,
        width: Width,
    ) -> String {
        let view = self.address_view(point, original);
        if self.compact_memory {
            let location = view.unwrap_or_else(|| self.expression_at(address, point).text);
            format!("read{}({location})", width.bits())
        } else if let Some(view) = view {
            format!("nirvana_view_load(&m, {view}, {})", width.bytes())
        } else {
            format!(
                "nirvana_load(&m, {}, {})",
                self.expression_at(address, point).text,
                width.bytes()
            )
        }
    }

    pub(super) fn register(&self, reg: Reg) -> String {
        if reg.0 >= self.first_temporary {
            format!("nirvana_value_{}", reg.0 - self.first_temporary)
        } else {
            self.names[&reg.0].clone()
        }
    }

    pub(super) fn evaluations(
        &self,
        code: &mut String,
        indent: usize,
        steps: &[Evaluation],
        point: Option<(u64, usize)>,
    ) {
        for step in steps {
            match step {
                Evaluation::Assign { destination, value } => line(
                    code,
                    indent,
                    &format!(
                        "{} = {};",
                        self.register(*destination),
                        self.expression(value).text
                    ),
                ),
                Evaluation::Load {
                    destination,
                    address,
                    original_address,
                    width,
                } => {
                    let value = self.load(point, address, original_address, *width);
                    line(
                        code,
                        indent,
                        &format!("{} = {value};", self.register(*destination)),
                    );
                }
                Evaluation::If {
                    condition,
                    taken,
                    not_taken,
                } => {
                    line(
                        code,
                        indent,
                        &format!("if ({}) {{", self.expression(condition).text),
                    );
                    self.evaluations(code, indent + 1, taken, point);
                    line(code, indent, "} else {");
                    self.evaluations(code, indent + 1, not_taken, point);
                    line(code, indent, "}");
                }
            }
        }
    }

    pub(super) fn ordered_expression(
        &self,
        code: &mut String,
        indent: usize,
        expr: &Expr,
        point: Option<(u64, usize)>,
        next: &mut usize,
    ) -> Result<Render, SequenceError> {
        if !needs_sequence(expr) {
            return Ok(self.expression_at(expr, point));
        }
        let plan = sequence(expr, *next)?;
        for reg in *next..plan.next_register {
            line(
                code,
                indent,
                &format!("uint64_t {};", self.register(Reg(reg))),
            );
        }
        *next = plan.next_register;
        self.evaluations(code, indent, &plan.steps, point);
        Ok(self.expression(&plan.value))
    }

    pub(super) fn value_statement(
        &self,
        code: &mut String,
        indent: usize,
        expr: &Expr,
        point: Option<(u64, usize)>,
        prefix: &str,
        suffix: &str,
    ) -> Result<(), SequenceError> {
        let scoped = needs_sequence(expr);
        if scoped {
            line(code, indent, "{");
        }
        let inner = indent + usize::from(scoped);
        let mut next = self.first_temporary;
        let value = self.ordered_expression(code, inner, expr, point, &mut next)?;
        line(code, inner, &format!("{prefix}{}{suffix}", value.text));
        if scoped {
            line(code, indent, "}");
        }
        Ok(())
    }

    pub(super) fn assignments(
        &self,
        code: &mut String,
        indent: usize,
        address: u64,
        assignments: &[Assignment],
    ) -> Result<(), SequenceError> {
        for (index, assignment) in assignments.iter().enumerate() {
            let point = Some((address, index));
            match &assignment.destination {
                Place::Register(reg) => {
                    if self.read.contains(&reg.0)
                        && let Expr::Register(source) = assignment.value
                        && self.names.contains_key(&source.0)
                        && self.register(*reg) == self.register(source)
                    {
                        continue;
                    }
                    if self.read.contains(&reg.0) {
                        let name = self.register(*reg);
                        let width = self.widths.get(&reg.0).copied().unwrap_or(Width::U64);
                        let initialize = self.declarations.at((address, index), &name);
                        let prefix = if initialize {
                            format!("{} {name} = ", self.local_type(*reg))
                        } else {
                            format!("{name} = ")
                        };
                        if let Some(value) = self.address_value(*reg, point, &assignment.value) {
                            line(code, indent, &format!("{prefix}{value};"));
                        } else if let Some(&signed) = self.signed_widths.get(&reg.0) {
                            self.signed_statement(
                                code,
                                indent,
                                &assignment.value,
                                point,
                                &prefix,
                                signed,
                            )?;
                        } else {
                            // Normalize while the explicit word observer is
                            // present, before spelling its truncation as a C type.
                            let normalized = self.normalize_arithmetic(&assignment.value, point);
                            let value = stored_value(&normalized, width);
                            if !initialize
                                && self.compact_memory
                                && let Some(statement) = self.compound(*reg, value, point)
                            {
                                line(code, indent, &statement);
                                continue;
                            }
                            self.value_statement(code, indent, value, point, &prefix, ";")?;
                        }
                    } else if assignment.value.uses_memory() {
                        self.value_statement(
                            code,
                            indent,
                            &assignment.value,
                            point,
                            "(void)(",
                            ");",
                        )?;
                    }
                }
                Place::Memory { address, width } => {
                    // Evaluate and check the destination before a possibly
                    // faulting RHS, capturing an address exactly once.
                    let scoped = assignment.value.uses_memory() || needs_sequence(address);
                    if scoped {
                        line(code, indent, "{");
                    }
                    let inner = indent + usize::from(scoped);
                    let mut next = self.first_temporary;
                    let view = self.address_view(point, address);
                    let destination = if let Some(view) = &view {
                        format!("{view}.address")
                    } else {
                        let value =
                            self.ordered_expression(code, inner, address, point, &mut next)?;
                        if scoped {
                            line(
                                code,
                                inner,
                                &format!("const uint64_t nirvana_address = {};", value.text),
                            );
                            "nirvana_address".into()
                        } else {
                            value.text
                        }
                    };
                    if scoped {
                        line(
                            code,
                            inner,
                            &format!(
                                "(void)nirvana_offset(&m, {destination}, {});",
                                width.bytes()
                            ),
                        );
                    }
                    let value = self
                        .ordered_expression(
                            code,
                            inner,
                            stored_value(&assignment.value, *width),
                            point,
                            &mut next,
                        )?
                        .text;
                    let statement = if self.compact_memory {
                        format!(
                            "write{}({}, {value});",
                            width.bits(),
                            view.unwrap_or(destination)
                        )
                    } else if let Some(view) = view {
                        format!(
                            "nirvana_view_store(&m, {view}, {}, {value});",
                            width.bytes()
                        )
                    } else {
                        format!(
                            "nirvana_store(&m, {destination}, {}, {value});",
                            width.bytes()
                        )
                    };
                    line(code, inner, &statement);
                    if scoped {
                        line(code, indent, "}");
                    }
                }
            }
        }
        Ok(())
    }

    pub(super) fn compound(
        &self,
        destination: Reg,
        value: &Expr,
        point: Option<(u64, usize)>,
    ) -> Option<String> {
        if needs_sequence(value) {
            return None;
        }
        let same = |a: Reg, b: Reg| {
            self.names
                .get(&a.0)
                .zip(self.names.get(&b.0))
                .is_some_and(|(a, b)| a == b)
        };
        // Direct total-IR operations admit C compounds when the literal
        // divisor is nonzero. Both operands still denote current storage.
        if let Expr::Binary(op @ (BinaryOp::UDiv | BinaryOp::URem), left, right) = value
            && let Expr::Register(source) = **left
            && let Expr::Const(divisor) = **right
            && divisor != 0
            && same(destination, source)
        {
            return Some(format!(
                "{} {}= {};",
                self.register(destination),
                if *op == BinaryOp::UDiv { "/" } else { "%" },
                self.expression(right).text
            ));
        }
        // Arithmetic proof precedes compound extraction, which would otherwise
        // hide the whole subtraction behind `x -= quotient * divisor`.
        if crate::transform::signed_division_expr::recognize_remainder(value).is_some() {
            return None;
        }
        let remainder = self
            .context_remainder(value, point)
            .map(|view| (view.value, view.divisor))
            .or_else(|| {
                crate::transform::remainder_expr::recognize(value)
                    .map(|view| (view.value, view.divisor))
            });
        if let Some((Expr::Register(source), divisor)) = remainder
            && same(destination, *source)
        {
            return Some(format!(
                "{} %= {};",
                self.register(destination),
                self.expression(&Expr::Const(divisor)).text
            ));
        }
        if remainder.is_some() {
            return None;
        }
        let (mut op, mut right) = crate::transform::self_update::extract(value, destination, same)
            .or_else(|| {
                // Subtraction has no associative-chain rule; preserve the existing
                // direct x=x-y spelling without reassociating any operands.
                if let Expr::Binary(BinaryOp::Sub, left, right) = value
                    && let Expr::Register(source) = **left
                    && same(destination, source)
                {
                    Some((BinaryOp::Sub, (**right).clone()))
                } else {
                    None
                }
            })?;
        // x + (2^64 - n) and x - n have the same unsigned low bits at
        // every supported storage width. Keep small decrements readable.
        if op == BinaryOp::Add
            && let Expr::Const(value) = right
            && value > i64::MAX as u64
        {
            op = BinaryOp::Sub;
            right = Expr::Const(value.wrapping_neg());
        }
        // These are standalone updates (also used as for-loop clauses), so
        // no expression consumes the old or new value. Unsigned ++/-- retain
        // the same wrap and narrowing as the corresponding compound update.
        if right == Expr::Const(1) {
            match op {
                BinaryOp::Add => return Some(format!("++{};", self.register(destination))),
                BinaryOp::Sub => return Some(format!("--{};", self.register(destination))),
                _ => {}
            }
        }
        let symbol = match op {
            BinaryOp::Add => "+",
            BinaryOp::Sub => "-",
            BinaryOp::Mul => "*",
            BinaryOp::And => "&",
            BinaryOp::Or => "|",
            BinaryOp::Xor => "^",
            _ => return None,
        };
        let right = self.expression_at(&right, point);
        // Narrow C integers promote to signed int. Force 64-bit arithmetic
        // before the operation, then let the unsigned destination truncate.
        let right = if self
            .widths
            .get(&destination.0)
            .copied()
            .unwrap_or(Width::U64)
            == Width::U64
        {
            right.text
        } else {
            right.u64()
        };
        Some(format!("{} {symbol}= {right};", self.register(destination)))
    }

    pub(super) fn loop_clauses(&self, steps: &[Node], update: bool) -> Option<Vec<String>> {
        let mut clauses = Vec::new();
        for step in steps {
            let Node::Step {
                address,
                assignments,
            } = step
            else {
                return None;
            };
            for (index, assignment) in assignments.iter().enumerate() {
                let point = Some((*address, index));
                match &assignment.destination {
                    Place::Register(reg) => {
                        if self.read.contains(&reg.0)
                            && let Expr::Register(source) = assignment.value
                            && self.names.contains_key(&source.0)
                            && self.register(*reg) == self.register(source)
                        {
                            continue;
                        }
                        if self.read.contains(&reg.0) {
                            let width = self.widths.get(&reg.0).copied().unwrap_or(Width::U64);
                            let normalized = self.normalize_arithmetic(&assignment.value, point);
                            let value = stored_value(&normalized, width);
                            if let Some(value) = self.address_value(*reg, point, value) {
                                clauses.push(format!("{} = {value}", self.register(*reg)));
                            } else if update
                                && self.compact_memory
                                && let Some(statement) = self.compound(*reg, value, point)
                            {
                                clauses.push(statement.strip_suffix(';')?.into());
                            } else {
                                clauses.push(format!(
                                    "{} = {}",
                                    self.register(*reg),
                                    self.expression_at(value, point).text
                                ));
                            }
                        } else if assignment.value.uses_memory() {
                            clauses.push(self.expression_at(&assignment.value, point).text);
                        }
                    }
                    Place::Memory { address, width } => {
                        // For-header recovery admits only pure destinations and
                        // pure RHS values. The checked store is the only faulting
                        // operation in this clause, just as in a standalone store.
                        if !update || address.uses_memory() || assignment.value.uses_memory() {
                            return None;
                        }
                        let value = self
                            .expression_at(stored_value(&assignment.value, *width), point)
                            .text;
                        let view = self.address_view(point, address);
                        let text = if self.compact_memory {
                            let destination =
                                view.unwrap_or_else(|| self.expression_at(address, point).text);
                            format!("write{}({destination}, {value})", width.bits())
                        } else if let Some(view) = view {
                            format!("nirvana_view_store(&m, {view}, {}, {value})", width.bytes())
                        } else {
                            format!(
                                "nirvana_store(&m, {}, {}, {value})",
                                self.expression_at(address, point).text,
                                width.bytes()
                            )
                        };
                        clauses.push(text);
                    }
                }
            }
        }
        Some(clauses)
    }

    pub(super) fn loop_header<'a>(&self, body: &'a [Node]) -> Option<LoopHeader<'a>> {
        let mut for_shape = false;
        if let Some(header) =
            crate::transform::for_loop::recover(body, |reg| self.slots.get(&reg.0).copied())
        {
            let updates = self.loop_clauses(header.update, true)?;
            let update = updates.join(", ");
            for_shape = !updates.is_empty();
            // Small recurrence updates remain idiomatic for clauses. Larger
            // bundles stay in their original body positions via while_header.
            if !updates.is_empty()
                && updates.len() <= 2
                && update.len() <= 80
                && (!header.body.is_empty() || updates.len() == 1)
            {
                let has_setup = !self.loop_clauses(header.setup, false)?.is_empty();
                let condition = if has_setup {
                    String::new()
                } else {
                    self.expression(&header.condition).text
                };
                return Some(LoopHeader {
                    text: format!("for (; {condition}; {update}) {{"),
                    setup: if has_setup { header.setup } else { &[] },
                    test: has_setup.then_some(header.condition),
                    body: header.body,
                });
            }
        }
        let header = crate::control_flow::loop_shape::while_header(body)?;
        let has_setup = !self.loop_clauses(header.setup, false)?.is_empty();
        Some(LoopHeader {
            text: if for_shape && has_setup {
                "for (;;) {".into()
            } else if has_setup {
                "while (1) {".into()
            } else if for_shape {
                format!("for (; {}; ) {{", self.expression(&header.condition).text)
            } else {
                format!("while ({}) {{", self.expression(&header.condition).text)
            },
            setup: if has_setup { header.setup } else { &[] },
            test: has_setup.then_some(header.condition),
            body: header.body,
        })
    }

    pub(super) fn loop_setup(
        &self,
        code: &mut String,
        header: &LoopHeader<'_>,
        indent: usize,
        nonlocal: bool,
        facts: &crate::transform::guarded_loop::Facts,
        labels: &LoopLabels<'_>,
    ) -> Result<(), ReadableError> {
        self.nodes_with_facts(code, header.setup, indent, nonlocal, facts, labels)?;
        if let Some(condition) = &header.test {
            self.value_statement(
                code,
                indent,
                &prepare::invert(condition),
                None,
                "if (",
                ") break;",
            )?;
        }
        Ok(())
    }

    pub(super) fn nodes(
        &self,
        code: &mut String,
        nodes: &[Node],
        indent: usize,
        nonlocal: bool,
    ) -> Result<(), ReadableError> {
        let labels = LoopLabels::analyze(nodes).ok_or(ReadableError::LoopLabelsUnavailable)?;
        let facts = crate::transform::guarded_loop::Facts::new(&self.initial_slots);
        self.nodes_with_facts(code, nodes, indent, nonlocal, &facts, &labels)
    }

    pub(super) fn nodes_with_facts(
        &self,
        code: &mut String,
        nodes: &[Node],
        indent: usize,
        nonlocal: bool,
        incoming: &crate::transform::guarded_loop::Facts,
        labels: &LoopLabels<'_>,
    ) -> Result<(), ReadableError> {
        let mut facts = incoming.clone();
        for node in nodes {
            match node {
                Node::Evaluate(value) => {
                    self.value_statement(code, indent, value, None, "(void)(", ");")?;
                }
                Node::Step {
                    address,
                    assignments,
                } => self.assignments(code, indent, *address, assignments)?,
                Node::If {
                    condition,
                    taken,
                    not_taken,
                } => {
                    if !nonlocal
                        && let Some(loop_view) = crate::transform::guarded_loop::recover(
                            condition,
                            taken,
                            not_taken,
                            &facts,
                            |reg| self.slots.get(&reg.0).copied(),
                        )
                        && self.guard_alias_reads_safe(taken, &loop_view.condition)
                    {
                        // Reuse the existing pre-test/for renderer. The proof
                        // expression is never emitted: this condition is the
                        // original latch, with only proven copy aliases changed.
                        let mut pretest = vec![Node::If {
                            condition: loop_view.condition.clone(),
                            taken: vec![],
                            not_taken: vec![Node::Break],
                        }];
                        pretest.extend_from_slice(loop_view.body);
                        pretest.push(Node::Continue);
                        let loop_facts =
                            facts.enter_loop(loop_view.body, |reg| self.slots.get(&reg.0).copied());
                        if let Some(header) = self.loop_header(&pretest) {
                            line(code, indent, &header.text);
                            self.loop_setup(
                                code,
                                &header,
                                indent + 1,
                                nonlocal,
                                &loop_facts,
                                labels,
                            )?;
                            let middle = header.body;
                            let middle = if matches!(middle.last(), Some(Node::Continue)) {
                                &middle[..middle.len() - 1]
                            } else {
                                middle
                            };
                            self.nodes_with_facts(
                                code,
                                middle,
                                indent + 1,
                                nonlocal,
                                &loop_facts,
                                labels,
                            )?;
                            line(code, indent, "}");
                            facts.observe(node, |reg| self.slots.get(&reg.0).copied());
                            continue;
                        }
                    }
                    let scoped = needs_sequence(condition);
                    if scoped {
                        line(code, indent, "{");
                    }
                    let inner = indent + usize::from(scoped);
                    let mut next = self.first_temporary;
                    let value = self.ordered_expression(code, inner, condition, None, &mut next)?;
                    line(code, inner, &format!("if ({}) {{", value.text));
                    self.nodes_with_facts(code, taken, inner + 1, nonlocal, &facts, labels)?;
                    if !not_taken.is_empty() {
                        line(code, inner, "} else {");
                        self.nodes_with_facts(
                            code,
                            not_taken,
                            inner + 1,
                            nonlocal,
                            &facts,
                            labels,
                        )?;
                    }
                    line(code, inner, "}");
                    if scoped {
                        line(code, indent, "}");
                    }
                }
                Node::Loop(body) => {
                    if !nonlocal && let Some(view) = crate::control_flow::loop_exit::recover(body) {
                        let loop_facts =
                            facts.enter_loop(body, |reg| self.slots.get(&reg.0).copied());
                        line(code, indent, "do {");
                        self.nodes_with_facts(
                            code,
                            view.body,
                            indent + 1,
                            nonlocal,
                            &loop_facts,
                            labels,
                        )?;
                        let condition = self.expression(view.condition).text;
                        let condition = if view.continue_when {
                            condition
                        } else {
                            format!("!({condition})")
                        };
                        line(code, indent, &format!("}} while ({condition});"));
                        // The exit follows successful loop completion. Entry
                        // constants must not survive writes from any iteration.
                        facts.observe(node, |reg| self.slots.get(&reg.0).copied());
                        self.nodes_with_facts(code, view.exit, indent, nonlocal, &facts, labels)?;
                        continue;
                    }
                    let continue_label = labels.continue_label(node);
                    let recovered_header = if continue_label.is_none() {
                        self.loop_header(body)
                    } else {
                        None
                    };
                    let (header, middle, footer) = if continue_label.is_some() {
                        ("for (;;) {".into(), body.as_slice(), "}".into())
                    } else if let Some(header) = &recovered_header {
                        (header.text.clone(), header.body, String::from("}"))
                    } else if !nonlocal
                        && let Some(view) = crate::control_flow::loop_shape::post_test(body)
                    {
                        let condition = self.expression(view.condition).text;
                        let condition = if view.continue_when {
                            condition
                        } else {
                            format!("!({condition})")
                        };
                        ("do {".into(), view.body, format!("}} while ({condition});"))
                    } else {
                        match body.as_slice() {
                            [
                                prefix @ ..,
                                Node::If {
                                    condition,
                                    taken,
                                    not_taken,
                                },
                            ] if is_continue(taken)
                                && is_break(not_taken)
                                && !contains_continue(prefix)
                                && !needs_sequence(condition) =>
                            {
                                (
                                    "do {".into(),
                                    prefix,
                                    format!("}} while ({});", self.expression(condition).text),
                                )
                            }
                            _ => ("for (;;) {".into(), body.as_slice(), "}".into()),
                        }
                    };
                    if let Some(label) = continue_label {
                        line(code, indent, &format!("{label}: ;"));
                    }
                    line(code, indent, &header);
                    let middle = if matches!(middle.last(), Some(Node::Continue)) {
                        &middle[..middle.len() - 1]
                    } else {
                        middle
                    };
                    let loop_facts = facts.enter_loop(body, |reg| self.slots.get(&reg.0).copied());
                    if let Some(header) = &recovered_header {
                        self.loop_setup(code, header, indent + 1, nonlocal, &loop_facts, labels)?;
                    }
                    self.nodes_with_facts(code, middle, indent + 1, nonlocal, &loop_facts, labels)?;
                    line(code, indent, &footer);
                    if let Some(label) = labels.break_label(node) {
                        line(code, indent, &format!("{label}: ;"));
                    }
                }
                Node::Break => line(code, indent, "break;"),
                Node::Continue => line(code, indent, "continue;"),
                Node::BreakOuter { .. } | Node::ContinueOuter { .. } => {
                    let target = labels
                        .target(node)
                        .ok_or(ReadableError::LoopLabelsUnavailable)?;
                    line(code, indent, &format!("goto {target};"));
                }
                Node::Return(value) => {
                    self.value_statement(code, indent, value, None, "return ", ";")?
                }
            }
            facts.observe(node, |reg| self.slots.get(&reg.0).copied());
        }
        Ok(())
    }

    pub(super) fn guard_alias_reads_safe(&self, taken: &[Node], condition: &Expr) -> bool {
        let mut pending = vec![condition];
        while let Some(expr) = pending.pop() {
            match expr {
                Expr::Binary(op, a, b) => {
                    if matches!(
                        op,
                        BinaryOp::Eq | BinaryOp::Ne | BinaryOp::Ult | BinaryOp::Ule
                    ) && self.expression(a).text == self.expression(b).text
                    {
                        // A proof under initial constants can accept this, but
                        // emitting x==x would introduce a C diagnostic. Keep the
                        // original guard instead of doing late algebra/DCE.
                        return false;
                    }
                    pending.extend([&**a, &**b]);
                }
                Expr::Select {
                    condition,
                    taken,
                    not_taken,
                } => pending.extend([&**condition, &**taken, &**not_taken]),
                Expr::Load { address, .. } => pending.push(address),
                _ => {}
            }
        }
        if self.views.is_none() {
            return true;
        }
        let [Node::Loop(body)] = taken else {
            return false;
        };
        let Some(Node::If { condition: old, .. }) = body.last() else {
            return false;
        };
        let reads = |expression: &Expr| {
            let mut found = BTreeSet::new();
            let mut pending = vec![expression];
            while let Some(expr) = pending.pop() {
                match expr {
                    Expr::Register(reg) => {
                        if let Some(&slot) = self.slots.get(&reg.0) {
                            found.insert(slot);
                        }
                    }
                    Expr::Const(_) => {}
                    Expr::Unary(_, value) => pending.push(value),
                    Expr::Binary(_, a, b) => pending.extend([&**a, &**b]),
                    Expr::Load { address, .. } => pending.push(address),
                    Expr::Select {
                        condition,
                        taken,
                        not_taken,
                    } => pending.extend([&**condition, &**taken, &**not_taken]),
                }
            }
            found
        };
        let protected: BTreeSet<_> = self
            .address_uses
            .iter()
            .filter_map(|r| self.slots.get(r))
            .copied()
            .collect();
        // Address-view printing may replace a copy's RHS with a captured view.
        // Retain the original guard if it could be the last printed read of
        // such a slot; raw AST copy use alone is insufficient here.
        reads(old)
            .difference(&reads(condition))
            .all(|slot| !protected.contains(slot))
    }
}

// A single load has no competing faulting operand. Keep that common machine
// shape compact; multiple/nested loads need explicit evaluation statements.

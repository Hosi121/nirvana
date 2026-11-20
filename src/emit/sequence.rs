//! Private C temporaries for the existing ordered-expression plan.

use super::line;
use crate::ir::{Assignment, BinaryOp, Control, Expr, Place, Program, Reg};
use crate::sequence::{
    Evaluation, MAX_ADDRESS_METADATA_NODES, MAX_EXPRESSION_DEPTH, MAX_EXPRESSION_NODES,
    SequenceError, sequence,
};

// Bound the complete input before recursive helper detection, AST recovery, or
// rendering. Per-expression limits agree with the shared sequencing pass.
const MAX_PROGRAM_NODES: usize = 1_048_576;

pub(crate) fn validate_program(program: &Program) -> Result<(), SequenceError> {
    let mut remaining = MAX_PROGRAM_NODES;
    for instruction in program.instructions() {
        remaining = remaining
            .checked_sub(1 + instruction.assignments.len())
            .ok_or(SequenceError::ExpressionTooLarge)?;
    }
    let mut validate = |root: &Expr| -> Result<(), SequenceError> {
        let mut pending = vec![(root, 1usize, 0usize)];
        let mut nodes = 0usize;
        let mut metadata = 0usize;
        let mut loads = 0usize;
        while let Some((expr, depth, ancestors)) = pending.pop() {
            if depth > MAX_EXPRESSION_DEPTH {
                return Err(SequenceError::ExpressionTooDeep);
            }
            remaining = remaining
                .checked_sub(1)
                .ok_or(SequenceError::ExpressionTooLarge)?;
            nodes += 1;
            metadata += ancestors;
            if metadata > MAX_ADDRESS_METADATA_NODES {
                return Err(SequenceError::AddressMetadataTooLarge);
            }
            match expr {
                Expr::Const(_) | Expr::Register(_) => {}
                Expr::Binary(_, left, right) => {
                    pending.push((right, depth + 1, ancestors));
                    pending.push((left, depth + 1, ancestors));
                }
                Expr::Load { address, .. } => {
                    loads += 1;
                    pending.push((address, depth + 1, ancestors + 1));
                }
                Expr::Select {
                    condition,
                    taken,
                    not_taken,
                } => {
                    pending.push((not_taken, depth + 1, ancestors));
                    pending.push((taken, depth + 1, ancestors));
                    pending.push((condition, depth + 1, ancestors));
                }
            }
        }
        if loads > 1 && nodes > MAX_EXPRESSION_NODES {
            return Err(SequenceError::ExpressionTooLarge);
        }
        Ok(())
    };
    for instruction in program.instructions() {
        for assignment in &instruction.assignments {
            if let Place::Memory { address, .. } = &assignment.destination {
                validate(address)?;
            }
            validate(&assignment.value)?;
        }
        match &instruction.control {
            Control::Branch { condition, .. } => validate(condition)?,
            Control::Return(value) => validate(value)?,
            _ => {}
        }
    }
    Ok(())
}

pub(crate) struct Expressions {
    first_temporary: usize,
    local_range: Option<(usize, usize)>,
}

impl Expressions {
    pub(crate) fn new(program: &Program) -> Self {
        Self {
            first_temporary: program.register_count(),
            local_range: None,
        }
    }

    /// Additional local storage remains separate from the canonical registers.
    pub(crate) fn with_locals(first_local: usize, local_count: usize) -> Self {
        Self {
            first_temporary: first_local + local_count + 2,
            local_range: Some((first_local, local_count)),
        }
    }

    fn register(&self, reg: Reg) -> String {
        if reg.0 < self.first_temporary {
            if let Some((first, count)) = self.local_range
                && reg.0 >= first
            {
                return match reg.0 - first {
                    index if index < count => format!("v_{index}"),
                    index if index == count => "phi_tmp".into(),
                    _ => "phi_condition".into(),
                };
            }
            format!("r[{}]", reg.0)
        } else {
            format!("nirvana_t{}", reg.0 - self.first_temporary)
        }
    }

    fn evaluations(&self, code: &mut String, indent: usize, steps: &[Evaluation]) {
        for step in steps {
            match step {
                Evaluation::Assign { destination, value } => line(
                    code,
                    indent,
                    &format!(
                        "{} = {};",
                        self.register(*destination),
                        self.expression(value)
                    ),
                ),
                Evaluation::Load {
                    destination,
                    address,
                    width,
                    ..
                } => line(
                    code,
                    indent,
                    &format!(
                        "{} = nirvana_load(&m, {}, {});",
                        self.register(*destination),
                        self.expression(address),
                        width.bytes()
                    ),
                ),
                Evaluation::If {
                    condition,
                    taken,
                    not_taken,
                } => {
                    line(
                        code,
                        indent,
                        &format!("if ({}) {{", self.expression(condition)),
                    );
                    self.evaluations(code, indent + 1, taken);
                    line(code, indent, "} else {");
                    self.evaluations(code, indent + 1, not_taken);
                    line(code, indent, "}");
                }
            }
        }
    }

    fn ordered(
        &self,
        code: &mut String,
        indent: usize,
        expr: &Expr,
        next: &mut usize,
    ) -> Result<String, SequenceError> {
        if !needs_sequence(expr) {
            return Ok(self.expression(expr));
        }
        let plan = sequence(expr, *next)?;
        for index in *next..plan.next_register {
            line(
                code,
                indent,
                &format!("uint64_t {};", self.register(Reg(index))),
            );
        }
        *next = plan.next_register;
        self.evaluations(code, indent, &plan.steps);
        Ok(self.expression(&plan.value))
    }

    pub(crate) fn begin(
        &self,
        code: &mut String,
        indent: usize,
        expr: &Expr,
    ) -> Result<(usize, String), SequenceError> {
        let scoped = needs_sequence(expr);
        if scoped {
            line(code, indent, "{");
        }
        let inner = indent + usize::from(scoped);
        let mut next = self.first_temporary;
        let value = self.ordered(code, inner, expr, &mut next)?;
        Ok((inner, value))
    }

    pub(crate) fn end(&self, code: &mut String, indent: usize, inner: usize) {
        if inner != indent {
            line(code, indent, "}");
        }
    }

    pub(crate) fn statement(
        &self,
        code: &mut String,
        indent: usize,
        expr: &Expr,
        prefix: &str,
        suffix: &str,
    ) -> Result<(), SequenceError> {
        let (inner, value) = self.begin(code, indent, expr)?;
        line(code, inner, &format!("{prefix}{value}{suffix}"));
        self.end(code, indent, inner);
        Ok(())
    }

    pub(crate) fn assignments(
        &self,
        code: &mut String,
        indent: usize,
        statements: &[Assignment],
    ) -> Result<(), SequenceError> {
        for assignment in statements {
            match &assignment.destination {
                Place::Register(reg) => self.statement(
                    code,
                    indent,
                    &assignment.value,
                    &format!("{} = ", self.register(*reg)),
                    ";",
                )?,
                Place::Memory { address, width } => {
                    // The IR checks the entire destination before evaluating
                    // the RHS. Capture exactly once, without guest-reg writes.
                    let scoped = assignment.value.uses_memory() || needs_sequence(address);
                    if scoped {
                        line(code, indent, "{");
                    }
                    let inner = indent + usize::from(scoped);
                    let mut next = self.first_temporary;
                    let address = self.ordered(code, inner, address, &mut next)?;
                    let address = if scoped {
                        line(
                            code,
                            inner,
                            &format!("const uint64_t nirvana_address = {address};"),
                        );
                        line(
                            code,
                            inner,
                            &format!(
                                "(void)nirvana_offset(&m, nirvana_address, {});",
                                width.bytes()
                            ),
                        );
                        "nirvana_address".to_owned()
                    } else {
                        address
                    };
                    let value = self.ordered(code, inner, &assignment.value, &mut next)?;
                    line(
                        code,
                        inner,
                        &format!("nirvana_store(&m, {address}, {}, {value});", width.bytes()),
                    );
                    self.end(code, indent, inner);
                }
            }
        }
        Ok(())
    }

    fn expression(&self, expr: &Expr) -> String {
        match expr {
            Expr::Const(value) => format!("UINT64_C({value})"),
            Expr::Register(reg) => self.register(*reg),
            Expr::Load { address, width } => format!(
                "nirvana_load(&m, {}, {})",
                self.expression(address),
                width.bytes()
            ),
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => format!(
                "({} ? {} : {})",
                self.expression(condition),
                self.expression(taken),
                self.expression(not_taken)
            ),
            Expr::Binary(op, left, right) => {
                let left = self.expression(left);
                let mut right = self.expression(right);
                if *op == BinaryOp::UMulHigh {
                    return format!("nirvana_umul_high({left}, {right})");
                }
                let operator = match op {
                    BinaryOp::Add => "+",
                    BinaryOp::Sub => "-",
                    BinaryOp::Mul => "*",
                    BinaryOp::And => "&",
                    BinaryOp::Or => "|",
                    BinaryOp::Xor => "^",
                    BinaryOp::Shl => "<<",
                    BinaryOp::Shr => ">>",
                    BinaryOp::Eq => "==",
                    BinaryOp::Ne => "!=",
                    BinaryOp::Ult => "<",
                    BinaryOp::Ule => "<=",
                    BinaryOp::UMulHigh => unreachable!(),
                };
                if matches!(op, BinaryOp::Shl | BinaryOp::Shr) {
                    right = format!("({right} & UINT64_C(63))");
                }
                // Comparisons must also have uint64_t type when nested inside
                // arithmetic, to avoid accidental signed-int operations in C.
                format!("((uint64_t)({left} {operator} {right}))")
            }
        }
    }
}

// A single syntactic read can retain C's lazy ?: directly. Pure operands have
// no effects, traps, or register writes; two reads must be explicitly ordered.
fn needs_sequence(root: &Expr) -> bool {
    let mut pending = vec![root];
    let mut loads = 0;
    while let Some(expr) = pending.pop() {
        match expr {
            Expr::Const(_) | Expr::Register(_) => {}
            Expr::Binary(_, left, right) => {
                pending.push(right);
                pending.push(left);
            }
            Expr::Load { address, .. } => {
                loads += 1;
                if loads > 1 {
                    return true;
                }
                pending.push(address);
            }
            Expr::Select {
                condition,
                taken,
                not_taken,
            } => {
                pending.push(not_taken);
                pending.push(taken);
                pending.push(condition);
            }
        }
    }
    false
}

//! Check source projection, pure assumptions, marker frame and observation map.
use super::super::observations::Observations;
use super::*;

fn assertion(value: &Expr, normalizers: &[Assignment]) -> bool {
    let Expr::Binary(BinaryOp::Eq, predicate, zero) = value else {
        return false;
    };
    if **zero != Expr::Const(0) {
        return false;
    }
    let mut pending = vec![&**predicate];
    let mut leaves = Vec::new();
    while let Some(next) = pending.pop() {
        if let Expr::Binary(BinaryOp::And, left, right) = next {
            pending.extend([&**right, &**left]);
        } else {
            leaves.push(next);
        }
        if pending.len() + leaves.len() > MAX_NORMALIZERS {
            return false;
        }
    }
    leaves.len()==normalizers.len() && leaves.into_iter().zip(normalizers).all(|(value,assignment)| {
        matches!((value,&assignment.destination),(Expr::Binary(BinaryOp::Eq,left,right),Place::Register(reg))
            if **left==Expr::Register(*reg)&&**right==assignment.value)
    })
}
fn property(
    query: &Query,
    projected: &Program,
    normalizers: &[Assignment],
    assumed: bool,
    terminal: u64,
) -> Result<(), Error> {
    let marker = Reg(projected.register_count());
    let shared: Vec<_> = (0..projected.register_count()).map(Reg).collect();
    if query.shared_inputs() != shared || query.outputs != Observations::Uniform(vec![marker]) {
        return Err(Error::Source);
    }
    for (right, actual) in [(false, &query.before), (true, &query.after)] {
        if entry(actual) != entry(projected)
            || actual.register_count() != projected.register_count() + 1
            || actual.instructions().len() != projected.instructions().len()
        {
            return Err(Error::Source);
        }
        for (original, actual) in projected.instructions().iter().zip(actual.instructions()) {
            if original.address != actual.address
                || original.size != actual.size
                || original.control != actual.control
                || actual.assignments.get(..original.assignments.len())
                    != Some(original.assignments.as_slice())
            {
                return Err(Error::Source);
            }
            let mut tail = &actual.assignments[original.assignments.len()..];
            if original.address == entry(projected) {
                if assumed {
                    if tail.get(..normalizers.len()) != Some(normalizers) {
                        return Err(Error::Source);
                    }
                    tail = &tail[normalizers.len()..];
                }
                if !matches!(tail.first(),Some(Assignment{destination:Place::Register(r),value:Expr::Const(0)}) if *r==marker)
                {
                    return Err(Error::Source);
                }
                tail = &tail[1..];
            }
            if right && original.address == terminal {
                let Some(Assignment {
                    destination: Place::Register(r),
                    value,
                }) = tail.first()
                else {
                    return Err(Error::Source);
                };
                if *r != marker || !assertion(value, normalizers) {
                    return Err(Error::Source);
                }
                tail = &tail[1..];
            }
            if !tail.is_empty() {
                return Err(Error::Source);
            }
        }
    }
    Ok(())
}
pub(super) fn validate(problem: &Problem) -> Result<(), Error> {
    check_normalizers(&problem.source, &problem.normalizers)?;
    let feedback = &problem.feedback_region;
    feedback.validate().map_err(Error::Extraction)?;
    if !feedback.belongs_to(&problem.source)
        || feedback.source_entry() != problem.header
        || feedback.input_bit_caps().iter().any(|&bits| bits != 64)
    {
        return Err(Error::Source);
    }
    let terminal = feedback_terminal(feedback, problem.header)?;
    property(
        &problem.feedback,
        feedback.program(),
        &problem.normalizers,
        true,
        terminal,
    )?;
    match &problem.base_region {
        Some(prefix) => {
            prefix.validate().map_err(Error::Extraction)?;
            if entry(&problem.source) == problem.header
                || !prefix.belongs_to(&problem.source)
                || prefix.source_entry() != entry(&problem.source)
                || prefix.input_bit_caps().iter().any(|&bits| bits != 64)
            {
                return Err(Error::Source);
            }
            property(
                &problem.base,
                prefix.program(),
                &problem.normalizers,
                false,
                feedback_terminal(prefix, problem.header)?,
            )
        }
        None => {
            if entry(&problem.source) != problem.header {
                return Err(Error::Source);
            }
            let identity = Program::new(
                0,
                problem.source.register_count() + 1,
                vec![IrInstruction {
                    address: 0,
                    size: 1,
                    assignments: vec![],
                    control: Control::Return(Expr::Const(0)),
                }],
            )
            .map_err(|_| Error::Source)?;
            property(&problem.base, &identity, &problem.normalizers, false, 0)
        }
    }
}

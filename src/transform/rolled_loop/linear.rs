//! Fuse a synthetic linear jump while retaining sequential memory effects.
use super::*;

pub(super) fn fuse(mut program: Program, synthetic: u64, feedback: u64) -> Result<Program, Error> {
    for _ in 0..region::MAX_INSTRUCTIONS {
        let cfg = program.cfg();
        let pair = cfg.blocks().iter().find_map(|from| {
            if from.start < synthetic {
                return None;
            }
            let last = program.instructions().get(from.instructions.end - 1)?;
            let Control::Jump(to) = last.control else {
                return None;
            };
            if to < synthetic || to == feedback {
                return None;
            }
            let target = cfg.block(cfg.block_at(to)?);
            if target.id == from.id
                || target.predecessors.len() != 1
                || target.predecessors[0] != from.id
            {
                return None;
            }
            let tail = program.instructions().get(target.instructions.end - 1)?;
            if !matches!(tail.control, Control::Jump(_)) {
                return None;
            }
            Some((from.instructions.end - 1, target.instructions.clone()))
        });
        let Some((head, tail)) = pair else {
            return Ok(program);
        };
        let mut instructions = program.instructions().to_vec();
        let suffix: Vec<_> = instructions[tail.clone()]
            .iter()
            .flat_map(|i| i.assignments.iter().cloned())
            .collect();
        instructions[head].assignments.extend(suffix);
        instructions[head].control = instructions[tail.end - 1].control.clone();
        let instructions = instructions
            .into_iter()
            .enumerate()
            .filter(|(index, _)| !tail.contains(index))
            .map(|(_, i)| i)
            .collect();
        let entry = cfg.block(cfg.entry()).start;
        program = Program::new(entry, program.register_count(), instructions)
            .map_err(|_| Error::Projection)?;
    }
    Err(Error::Limit)
}

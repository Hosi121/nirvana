use super::controls::{Limit, exits};
use super::*;

// Recover a copy used only when this normal lane reaches the outer latch.
// Staging the update there keeps the source's last-lane storage convention.
pub(super) fn staging(
    source: &Program,
    slice: &Region,
    limit: &Limit,
    mark: Reg,
    latch: u64,
) -> Option<(Site, Reg, Reg)> {
    let instructions: BTreeMap<_, _> = source
        .instructions()
        .iter()
        .map(|i| (i.address, i))
        .collect();
    let branch = instructions[&limit.site];
    let Control::Branch { target, .. } = branch.control else {
        return None;
    };
    let selected = slice.source_to_region().keys().copied().collect();
    let mut pc = [target, branch.address + u64::from(branch.size)]
        .into_iter()
        .find(|&pc| {
            exits(source, &selected, slice.continuations(), pc).ok()
                == Some(BTreeSet::from([latch]))
        })?;
    let mut copied = None;
    let mut seen = BTreeSet::new();
    while pc != latch {
        if !seen.insert(pc) {
            return None;
        }
        let i = *instructions.get(&pc)?;
        for a in &i.assignments {
            if matches!((&a.destination,&a.value),(Place::Register(d),Expr::Register(s))if d==s) {
                continue;
            }
            let (Place::Register(dest), Expr::Register(from)) = (&a.destination, &a.value) else {
                return None;
            };
            if *from != mark || *dest == mark || copied.replace(*dest).is_some() {
                return None;
            }
        }
        pc = match i.control {
            Control::Jump(to) => to,
            Control::Next => pc + u64::from(i.size),
            _ => return None,
        };
    }
    let temporary = copied?;
    let mut updates = branch
        .assignments
        .iter()
        .enumerate()
        .filter(|(_, a)| a.destination == Place::Register(mark));
    let (assignment, update) = updates.next()?;
    if updates.next().is_some() || update.value.uses_memory() {
        return None;
    }
    Some((
        Site {
            instruction: branch.address,
            assignment: Some(assignment),
        },
        mark,
        temporary,
    ))
}

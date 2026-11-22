//! Enumerate all entry prefixes through one instruction in an acyclic ancestor
//! region. Limits reject the whole set, so callers can distinguish exhaustive
//! UNSAT questions from a selected or bounded collection of observed prefixes.
use super::*;
use crate::control_flow::cfg::BlockId;

/// Success contains every syntactic entry path ending at `through`, including
/// its assignments/control. Cycles among its reachable ancestors are rejected.
pub fn dag_prefixes_to(
    program: &Program,
    through: u64,
    limit: usize,
) -> Result<Vec<Vec<u64>>, UnknownReason> {
    if !(1..=4096).contains(&limit) || program.instructions().len() > 100_000 {
        return Err(UnknownReason::ResourceLimit);
    }
    let cfg = program.cfg();
    let position = program
        .instructions()
        .binary_search_by_key(&through, |i| i.address)
        .map_err(|_| UnknownReason::BlockShape)?;
    let last = cfg
        .blocks()
        .iter()
        .find(|b| b.instructions.contains(&position))
        .ok_or(UnknownReason::BlockShape)?
        .id;
    let reachable = cfg.reachable_blocks();
    if !reachable.contains(&last) {
        return Ok(vec![]);
    }
    let mut ancestors = BTreeSet::new();
    let mut pending = vec![last];
    let mut work = 1_000_000usize;
    while let Some(id) = pending.pop() {
        work = work.checked_sub(1).ok_or(UnknownReason::ResourceLimit)?;
        if reachable.contains(&id) && ancestors.insert(id) {
            pending.extend(&cfg.block(id).predecessors);
        }
    }
    let mut incoming: BTreeMap<_, _> = ancestors
        .iter()
        .map(|&id| {
            (
                id,
                cfg.block(id)
                    .predecessors
                    .iter()
                    .filter(|p| ancestors.contains(p))
                    .count(),
            )
        })
        .collect();
    let mut ready: Vec<_> = incoming
        .iter()
        .filter_map(|(&id, &n)| (n == 0).then_some(id))
        .collect();
    let mut removed = 0;
    while let Some(id) = ready.pop() {
        removed += 1;
        // CFG edges can repeat a target; predecessor lists are unique.
        let successors: BTreeSet<_> = cfg
            .block(id)
            .successors
            .iter()
            .filter_map(|e| match e.target {
                Target::Block(to) if ancestors.contains(&to) => Some(to),
                _ => None,
            })
            .collect();
        for to in successors {
            work = work.checked_sub(1).ok_or(UnknownReason::ResourceLimit)?;
            let n = incoming.get_mut(&to).unwrap();
            *n -= 1;
            if *n == 0 {
                ready.push(to);
            }
        }
    }
    if removed != ancestors.len() {
        return Err(UnknownReason::BlockShape);
    }
    let mut result = Vec::new();
    let mut pending: Vec<Vec<BlockId>> = vec![vec![last]];
    while let Some(path) = pending.pop() {
        work = work
            .checked_sub(path.len())
            .ok_or(UnknownReason::ResourceLimit)?;
        if *path.last().unwrap() == cfg.entry() {
            let prefix: Vec<_> = path
                .iter()
                .rev()
                .flat_map(|&id| {
                    let range = cfg.block(id).instructions.clone();
                    program.instructions()[range]
                        .iter()
                        .take_while(move |i| id != last || i.address <= through)
                        .map(|i| i.address)
                })
                .collect();
            if prefix.len() > MAX_PREFIX || result.len() == limit {
                return Err(UnknownReason::ResourceLimit);
            }
            result.push(prefix);
        } else {
            for &before in &cfg.block(*path.last().unwrap()).predecessors {
                if ancestors.contains(&before) {
                    work = work
                        .checked_sub(path.len())
                        .ok_or(UnknownReason::ResourceLimit)?;
                    let mut next = path.clone();
                    next.push(before);
                    pending.push(next);
                    if pending.len() > limit {
                        return Err(UnknownReason::ResourceLimit);
                    }
                }
            }
        }
    }
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;
    fn program(controls: Vec<Control>) -> Program {
        Program::new(
            0,
            1,
            controls
                .into_iter()
                .enumerate()
                .map(|(n, control)| IrInstruction {
                    address: n as u64,
                    size: 1,
                    assignments: vec![],
                    control,
                })
                .collect(),
        )
        .unwrap()
    }
    #[test]
    fn every_diamond_prefix_is_retained_and_limits_discard_partial_sets() {
        let p = program(vec![
            Control::Branch {
                condition: Expr::Register(Reg(0)),
                target: 2,
            },
            Control::Jump(3),
            Control::Next,
            Control::Next,
            Control::Return(Expr::Const(0)),
        ]);
        let prefixes: BTreeSet<_> = dag_prefixes_to(&p, 4, 4).unwrap().into_iter().collect();
        assert_eq!(
            prefixes,
            BTreeSet::from([vec![0, 1, 3, 4], vec![0, 2, 3, 4]])
        );
        assert_eq!(
            dag_prefixes_to(&p, 4, 1).unwrap_err(),
            UnknownReason::ResourceLimit
        );
        assert_eq!(dag_prefixes_to(&p, 3, 4).unwrap().len(), 2);
        assert!(dag_prefixes_to(&p, 99, 4).is_err());
    }
    #[test]
    fn cycles_are_local_to_the_ancestor_region_and_parallel_edges_are_unique() {
        let p = program(vec![
            Control::Branch {
                condition: Expr::Register(Reg(0)),
                target: 2,
            },
            Control::Jump(1),
            Control::Return(Expr::Const(0)),
        ]);
        assert_eq!(dag_prefixes_to(&p, 2, 4).unwrap(), [vec![0, 2]]);
        assert_eq!(
            dag_prefixes_to(&p, 1, 4).unwrap_err(),
            UnknownReason::BlockShape
        );
        let parallel = program(vec![
            Control::Branch {
                condition: Expr::Register(Reg(0)),
                target: 1,
            },
            Control::Return(Expr::Const(0)),
        ]);
        assert_eq!(dag_prefixes_to(&parallel, 1, 4).unwrap(), [vec![0, 1]]);
    }

    #[test]
    fn all_small_forward_programs_match_an_instruction_path_oracle() {
        fn walk(
            p: &Program,
            pc: u64,
            through: u64,
            path: &mut Vec<u64>,
            out: &mut BTreeSet<Vec<u64>>,
        ) {
            let Some(i) = p.instructions().iter().find(|i| i.address == pc) else {
                return;
            };
            path.push(pc);
            if pc == through {
                out.insert(path.clone());
            } else {
                let next = pc + u64::from(i.size);
                match i.control {
                    Control::Next => walk(p, next, through, path, out),
                    Control::Jump(to) => walk(p, to, through, path, out),
                    Control::Branch { target, .. } => {
                        walk(p, next, through, path, out);
                        if target != next {
                            walk(p, target, through, path, out);
                        }
                    }
                    Control::Return(_) => {}
                }
            }
            path.pop();
        }
        let options: Vec<Vec<_>> = (0..4)
            .map(|pc| {
                let mut choices = vec![Control::Return(Expr::Const(0))];
                if pc < 3 {
                    choices.push(Control::Next);
                }
                for to in (pc + 1)..4 {
                    choices.extend([
                        Control::Jump(to),
                        Control::Branch {
                            condition: Expr::Register(Reg(0)),
                            target: to,
                        },
                    ]);
                }
                choices
            })
            .collect();
        for a in &options[0] {
            for b in &options[1] {
                for c in &options[2] {
                    for d in &options[3] {
                        let p = program(vec![a.clone(), b.clone(), c.clone(), d.clone()]);
                        for through in 0..4 {
                            let mut expected = BTreeSet::new();
                            walk(&p, 0, through, &mut Vec::new(), &mut expected);
                            let actual = dag_prefixes_to(&p, through, 16)
                                .unwrap()
                                .into_iter()
                                .collect();
                            assert_eq!(expected, actual, "{through}: {:?}", p.instructions());
                        }
                    }
                }
            }
        }
    }
}

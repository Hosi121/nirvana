//! Check lexical C-transfer targets against the original projected CFG.
//! The producer chooses a flat event stream; this checker parses a tree and
//! computes continuations from its nested syntax instead of its flat offsets.
use super::*;

enum Item {
    Block(BlockId),
    Loop(BlockId, Vec<Item>),
}

fn parse(events: &[Event], at: &mut usize, header: Option<BlockId>) -> Option<Vec<Item>> {
    let mut items = Vec::new();
    while let Some(event) = events.get(*at) {
        *at += 1;
        match *event {
            Event::Block(id) => items.push(Item::Block(id)),
            Event::Open(id) => items.push(Item::Loop(id, parse(events, at, Some(id))?)),
            Event::Close(id) => {
                if header != Some(id)
                    || !matches!(items.first(), Some(Item::Block(first)) if *first == id)
                {
                    return None;
                }
                return Some(items);
            }
        }
    }
    header.is_none().then_some(items)
}

fn members(items: &[Item], out: &mut BTreeSet<BlockId>) -> bool {
    for item in items {
        match item {
            Item::Block(id) => {
                if !out.insert(*id) {
                    return false;
                }
            }
            Item::Loop(_, body) => {
                if !members(body, out) {
                    return false;
                }
            }
        }
    }
    true
}

fn genuine_loop(
    header: BlockId,
    body: &[Item],
    entry: BlockId,
    graph: &BTreeMap<BlockId, Vec<BlockId>>,
) -> bool {
    let mut set = BTreeSet::new();
    if !members(body, &mut set) || !set.contains(&header) || set.contains(&entry) && entry != header
    {
        return false;
    }
    let mut reverse: BTreeMap<BlockId, Vec<BlockId>> = BTreeMap::new();
    let mut returns = false;
    for (&from, targets) in graph {
        for &target in targets {
            if set.contains(&target) {
                if !set.contains(&from) && target != header {
                    return false;
                }
                if set.contains(&from) {
                    reverse.entry(target).or_default().push(from);
                    returns |= target == header;
                }
            }
        }
    }
    if !returns {
        return false;
    }
    for backwards in [false, true] {
        let mut seen = BTreeSet::new();
        let mut pending = vec![header];
        while let Some(id) = pending.pop() {
            if !seen.insert(id) {
                continue;
            }
            let successors = if backwards {
                reverse.get(&id)
            } else {
                graph.get(&id)
            };
            if let Some(next) = successors {
                pending.extend(next.iter().copied().filter(|id| set.contains(id)));
            }
        }
        if seen != set {
            return false;
        }
    }
    true
}

fn continuations(
    items: &[Item],
    mut next: Option<BlockId>,
    loops: &mut Vec<(BlockId, Option<BlockId>)>,
    graph: &BTreeMap<BlockId, Vec<BlockId>>,
    layout: &LoopLayout,
    checked: &mut BTreeSet<(BlockId, BlockId)>,
) -> Option<BlockId> {
    for item in items.iter().rev() {
        match item {
            Item::Block(id) => {
                for target in graph.get(id)? {
                    let actual = match layout.edges.get(&(*id, *target))? {
                        Transfer::Fallthrough => next,
                        Transfer::Continue => loops.last().map(|(header, _)| *header),
                        Transfer::Break => loops.last().and_then(|(_, exit)| *exit),
                        Transfer::Goto(id) => Some(*id),
                    };
                    if actual != Some(*target) {
                        return None;
                    }
                    checked.insert((*id, *target));
                }
                next = Some(*id);
            }
            Item::Loop(header, body) => {
                if !genuine_loop(*header, body, layout.entry, graph) {
                    return None;
                }
                loops.push((*header, next));
                let first = continuations(body, Some(*header), loops, graph, layout, checked)?;
                loops.pop();
                if first != *header {
                    return None;
                }
                next = Some(*header);
            }
        }
    }
    next
}

pub(super) fn validate(program: &Program, flat: &GotoLayout, layout: &LoopLayout) -> bool {
    if layout.events.len() > 3 * MAX_BLOCKS || layout.entry != flat.entry() {
        return false;
    }
    // Bind the assignment-free routing projection to this exact source, rather
    // than accepting a view that was computed for another Program's effects.
    let Some(expected_flat) = GotoLayout::compute(program) else {
        return false;
    };
    if flat.blocks != expected_flat.blocks
        || flat.entry != expected_flat.entry
        || flat.resolved != expected_flat.resolved
    {
        return false;
    }
    let Some(items) = parse(&layout.events, &mut 0, None) else {
        return false;
    };
    let mut seen = BTreeSet::new();
    let expected: BTreeSet<_> = flat.blocks().iter().copied().collect();
    if !members(&items, &mut seen) || seen != expected {
        return false;
    }
    let Some(graph) = seen
        .iter()
        .map(|&id| Some((id, successors(program, flat, id)?)))
        .collect::<Option<BTreeMap<_, _>>>()
    else {
        return false;
    };
    let mut checked = BTreeSet::new();
    continuations(&items, None, &mut Vec::new(), &graph, layout, &mut checked) == Some(layout.entry)
        && checked.len() == layout.edges.len()
}

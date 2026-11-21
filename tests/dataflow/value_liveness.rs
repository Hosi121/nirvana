use nirvana::cfg::Target;
use nirvana::ir::{Assignment, BinaryOp, Control, Expr, IrInstruction, Place, Program, Reg, Width};
use nirvana::ssa::{
    Definition, PhiInput, PointValues, RegisterValue, Site, SsaBlock, SsaError, SsaFunction,
    ValueId,
};
use nirvana::value_liveness::{self, Liveness, Use};
use std::collections::{BTreeMap, BTreeSet};

fn ins(address: u64, assignments: Vec<Assignment>, control: Control) -> IrInstruction {
    IrInstruction {
        address,
        size: 1,
        assignments,
        control,
    }
}
fn reg(index: usize) -> Expr {
    Expr::Register(Reg(index))
}
fn set(register: usize, value: Expr) -> Assignment {
    Assignment {
        destination: Reg(register).into(),
        value,
    }
}
fn site(instruction: u64, assignment: Option<usize>) -> Site {
    Site {
        instruction,
        assignment,
    }
}
fn point(
    instruction: u64,
    assignment: Option<usize>,
    definition: Option<usize>,
    reads: &[(usize, usize)],
) -> PointValues {
    PointValues {
        site: site(instruction, assignment),
        definition: definition.map(ValueId),
        reads: reads
            .iter()
            .map(|&(r, v)| RegisterValue {
                register: Reg(r),
                value: ValueId(v),
            })
            .collect(),
    }
}
fn initial(register: usize) -> Definition {
    Definition::Initial {
        register: Reg(register),
    }
}
fn assignment(instruction: u64, index: usize, register: usize) -> Definition {
    Definition::Assignment {
        site: site(instruction, Some(index)),
        register: Reg(register),
    }
}
fn phi(block: u64, register: usize, inputs: &[(Option<u64>, usize)]) -> Definition {
    Definition::Phi {
        block,
        register: Reg(register),
        inputs: inputs
            .iter()
            .map(|&(predecessor, value)| PhiInput {
                predecessor,
                value: ValueId(value),
            })
            .collect(),
    }
}
fn block(
    start: u64,
    phis: &[usize],
    points: Vec<PointValues>,
    exits: &[(usize, usize)],
) -> SsaBlock {
    SsaBlock {
        start,
        phis: phis.iter().copied().map(ValueId).collect(),
        points,
        exit_values: exits
            .iter()
            .map(|&(r, v)| RegisterValue {
                register: Reg(r),
                value: ValueId(v),
            })
            .collect(),
    }
}
fn ids(indices: &[usize]) -> Vec<ValueId> {
    indices.iter().copied().map(ValueId).collect()
}

fn diamond() -> (Program, SsaFunction) {
    let source = Program::new(
        0,
        2,
        vec![
            ins(
                0,
                vec![],
                Control::Branch {
                    condition: reg(0),
                    target: 2,
                },
            ),
            ins(1, vec![set(1, Expr::Const(11))], Control::Jump(3)),
            ins(2, vec![set(1, Expr::Const(22))], Control::Jump(3)),
            ins(3, vec![], Control::Return(reg(1))),
        ],
    )
    .unwrap();
    let graph = SsaFunction {
        entry: 0,
        register_count: 2,
        values: vec![
            initial(0),
            phi(0, 0, &[(None, 0)]),
            assignment(1, 0, 1),
            assignment(2, 0, 1),
            phi(3, 1, &[(Some(1), 2), (Some(2), 3)]),
        ],
        blocks: vec![
            block(0, &[1], vec![point(0, None, None, &[(0, 1)])], &[]),
            block(1, &[], vec![point(1, Some(0), Some(2), &[])], &[(1, 2)]),
            block(2, &[], vec![point(2, Some(0), Some(3), &[])], &[(1, 3)]),
            block(3, &[4], vec![point(3, None, None, &[(1, 4)])], &[]),
        ],
    };
    (source, graph)
}
fn entry_loop() -> (Program, SsaFunction) {
    let source = Program::new(
        0,
        2,
        vec![
            ins(
                0,
                vec![
                    set(0, Expr::binary(BinaryOp::Add, reg(0), Expr::Const(1))),
                    set(1, Expr::binary(BinaryOp::Add, reg(1), reg(0))),
                ],
                Control::Branch {
                    condition: reg(1),
                    target: 0,
                },
            ),
            ins(1, vec![], Control::Return(reg(0))),
        ],
    )
    .unwrap();
    let graph = SsaFunction {
        entry: 0,
        register_count: 2,
        values: vec![
            initial(0),
            initial(1),
            phi(0, 0, &[(None, 0), (Some(0), 4)]),
            phi(0, 1, &[(None, 1), (Some(0), 5)]),
            assignment(0, 0, 0),
            assignment(0, 1, 1),
            phi(1, 0, &[(Some(0), 4)]),
        ],
        blocks: vec![
            block(
                0,
                &[2, 3],
                vec![
                    point(0, Some(0), Some(4), &[(0, 2)]),
                    point(0, Some(1), Some(5), &[(1, 3), (0, 4)]),
                    point(0, None, None, &[(1, 5)]),
                ],
                &[(0, 4), (1, 5)],
            ),
            block(1, &[6], vec![point(1, None, None, &[(0, 6)])], &[]),
        ],
    };
    (source, graph)
}

#[derive(Default)]
struct Event {
    reads: BTreeSet<ValueId>,
    kills: BTreeSet<ValueId>,
    next: Vec<usize>,
}

// Independent oracle: from each observation and identity, search forward for
// a future use, stopping at its definition. This is not the production backward
// set algorithm, and finite visited sets handle arbitrary loops without unwind.
fn oracle(source: &Program, graph: &SsaFunction, result: &Liveness) {
    let mut events = Vec::<Event>::new();
    let mut gates = BTreeMap::new();
    let mut starts = BTreeMap::new();
    let mut ends = BTreeMap::new();
    let mut points = BTreeMap::new();
    for block in &graph.blocks {
        let gate = events.len();
        events.push(Event {
            kills: block.phis.iter().copied().collect(),
            ..Event::default()
        });
        gates.insert(block.start, gate);
        let mut chain = Vec::new();
        for point in &block.points {
            let index = events.len();
            events.push(Event {
                reads: point.reads.iter().map(|r| r.value).collect(),
                kills: point.definition.into_iter().collect(),
                next: Vec::new(),
            });
            points.insert(point.site, index);
            chain.push(index);
        }
        let end = events.len();
        events.push(Event::default());
        ends.insert(block.start, end);
        chain.push(end);
        starts.insert(block.start, chain[0]);
        events[gate].next.push(chain[0]);
        for pair in chain.windows(2) {
            events[pair[0]].next.push(pair[1]);
        }
    }
    let mut edges = BTreeMap::new();
    edges.insert((None, graph.entry), 0usize);
    for block in &graph.blocks {
        let id = source.cfg().block_at(block.start).unwrap();
        for edge in &source.cfg().block(id).successors {
            let Target::Block(to) = edge.target else {
                panic!("resolved test edge")
            };
            edges.insert((Some(block.start), source.cfg().block(to).start), 0);
        }
    }
    for (&(from, to), index) in &mut edges {
        *index = events.len();
        events.push(Event {
            next: vec![gates[&to]],
            ..Event::default()
        });
        if let Some(from) = from {
            events[ends[&from]].next.push(*index);
        }
    }
    for definition in &graph.values {
        if let Definition::Phi { block, inputs, .. } = definition {
            for input in inputs {
                events[edges[&(input.predecessor, *block)]]
                    .reads
                    .insert(input.value);
            }
        }
    }
    let live = |start: usize| -> Vec<ValueId> {
        (0..graph.values.len())
            .map(ValueId)
            .filter(|value| {
                let mut pending = vec![start];
                let mut seen = BTreeSet::new();
                while let Some(index) = pending.pop() {
                    if !seen.insert(index) {
                        continue;
                    }
                    if events[index].reads.contains(value) {
                        return true;
                    }
                    if !events[index].kills.contains(value) {
                        pending.extend(&events[index].next);
                    }
                }
                false
            })
            .collect()
    };
    let mut expected_blocks = vec![Vec::new(); graph.values.len()];
    let mut peak = 0;
    for block in &result.blocks {
        assert_eq!(
            block.live_in,
            live(starts[&block.start]),
            "block {} in",
            block.start
        );
        assert_eq!(
            block.live_out,
            live(ends[&block.start]),
            "block {} out",
            block.start
        );
        for point in &block.points {
            let event = points[&point.site];
            assert_eq!(point.before, live(event), "{:?} before", point.site);
            assert_eq!(
                point.after,
                live(events[event].next[0]),
                "{:?} after",
                point.site
            );
        }
        for set in [&block.live_in, &block.live_out]
            .into_iter()
            .chain(block.points.iter().flat_map(|p| [&p.before, &p.after]))
        {
            peak = peak.max(set.len());
            for value in set {
                if expected_blocks[value.0].last() != Some(&block.start) {
                    expected_blocks[value.0].push(block.start);
                }
            }
        }
    }
    assert_eq!(result.edges.len(), edges.len());
    for edge in &result.edges {
        assert_eq!(
            edge.live,
            live(edges[&(edge.from, edge.to)]),
            "edge {:?} -> {}",
            edge.from,
            edge.to
        );
        peak = peak.max(edge.live.len());
    }
    for (value, expected) in result.values.iter().zip(expected_blocks) {
        assert_eq!(value.live_blocks, expected);
    }
    assert_eq!(result.peak_live, peak);
}

fn read_registers(expr: &Expr, reads: &mut Vec<usize>) {
    match expr {
        Expr::Unary(_, value) => read_registers(value, reads),
        Expr::Const(_) => (),
        Expr::Register(Reg(r)) => reads.push(*r),
        Expr::Binary(_, a, b) => {
            read_registers(a, reads);
            read_registers(b, reads);
        }
        Expr::Load { address, .. } => read_registers(address, reads),
        Expr::Select {
            condition,
            taken,
            not_taken,
        } => {
            read_registers(condition, reads);
            read_registers(taken, reads);
            read_registers(not_taken, reads);
        }
    }
}
// A second oracle computes raw-register liveness directly from source syntax.
// Apply it to source-live phi graphs; intentionally unused phis add syntactic
// edge uses beyond the raw program's requirements and are tested separately.
fn raw_oracle(source: &Program, graph: &SsaFunction, result: &Liveness) {
    type RawPoint = (Site, Option<usize>, Vec<usize>);
    let mut points = BTreeMap::<u64, Vec<RawPoint>>::new();
    let mut successors = BTreeMap::<u64, BTreeSet<u64>>::new();
    for id in source.cfg().reachable_blocks() {
        let block = source.cfg().block(id);
        let mut raw = Vec::new();
        for ins in &source.instructions()[block.instructions.clone()] {
            for (index, assignment) in ins.assignments.iter().enumerate() {
                let mut reads = Vec::new();
                let write = match &assignment.destination {
                    Place::Register(Reg(r)) => Some(*r),
                    Place::Memory { address, .. } => {
                        read_registers(address, &mut reads);
                        None
                    }
                };
                read_registers(&assignment.value, &mut reads);
                raw.push((site(ins.address, Some(index)), write, reads));
            }
            if let Control::Branch { condition, .. } | Control::Return(condition) = &ins.control {
                let mut reads = Vec::new();
                read_registers(condition, &mut reads);
                raw.push((site(ins.address, None), None, reads));
            }
        }
        points.insert(block.start, raw);
        successors.insert(
            block.start,
            block
                .successors
                .iter()
                .map(|edge| {
                    let Target::Block(to) = edge.target else {
                        panic!("resolved")
                    };
                    source.cfg().block(to).start
                })
                .collect(),
        );
    }
    let mut input: BTreeMap<u64, BTreeSet<usize>> = points
        .keys()
        .map(|&start| (start, BTreeSet::new()))
        .collect();
    let transfer = |raw: &RawPoint, live: &mut BTreeSet<usize>| {
        if let Some(write) = raw.1 {
            live.remove(&write);
        }
        live.extend(raw.2.iter().copied());
    };
    loop {
        let previous = input.clone();
        for (&start, raw) in &points {
            let mut live: BTreeSet<_> = successors[&start]
                .iter()
                .flat_map(|next| &previous[next])
                .copied()
                .collect();
            for point in raw.iter().rev() {
                transfer(point, &mut live);
            }
            input.insert(start, live);
        }
        if input == previous {
            break;
        }
    }
    let project = |set: &[ValueId]| -> BTreeSet<usize> {
        set.iter()
            .map(|value| match &graph.values[value.0] {
                Definition::Initial { register }
                | Definition::Assignment { register, .. }
                | Definition::Phi { register, .. } => register.0,
            })
            .collect()
    };
    for block in &result.blocks {
        assert_eq!(project(&block.live_in), input[&block.start]);
        let mut live: BTreeSet<_> = successors[&block.start]
            .iter()
            .flat_map(|next| &input[next])
            .copied()
            .collect();
        assert_eq!(project(&block.live_out), live);
        assert_eq!(block.points.len(), points[&block.start].len());
        for (point, raw) in block.points.iter().zip(&points[&block.start]).rev() {
            assert_eq!(point.site, raw.0);
            assert_eq!(project(&point.after), live);
            transfer(raw, &mut live);
            assert_eq!(project(&point.before), live);
            assert_eq!(
                graph
                    .point(raw.0)
                    .unwrap()
                    .reads
                    .iter()
                    .map(|r| r.register.0)
                    .collect::<Vec<_>>(),
                raw.2
            );
        }
    }
    for edge in &result.edges {
        assert_eq!(project(&edge.live), input[&edge.to]);
    }
}

#[test]
fn predecessor_operands_stay_on_their_diamond_edges() {
    let (source, graph) = diamond();
    let result = value_liveness::analyze(&source, &graph).unwrap();
    oracle(&source, &graph, &result);
    raw_oracle(&source, &graph, &result);
    assert_eq!(
        result
            .edges
            .iter()
            .find(|e| e.from == Some(1) && e.to == 3)
            .unwrap()
            .live,
        ids(&[2])
    );
    assert_eq!(
        result
            .edges
            .iter()
            .find(|e| e.from == Some(2) && e.to == 3)
            .unwrap()
            .live,
        ids(&[3])
    );
    assert_eq!(result.blocks[3].live_in, ids(&[4]));
    assert_eq!(result.values[2].live_blocks, [1]);
    assert_eq!(result.values[3].live_blocks, [2]);
    assert_eq!(
        result.values[2].uses,
        [Use::Phi {
            value: ValueId(4),
            predecessor: Some(1)
        }]
    );
}

#[test]
fn loop_edges_include_virtual_entry_and_preserve_sequential_definitions() {
    let (source, graph) = entry_loop();
    let result = value_liveness::analyze(&source, &graph).unwrap();
    oracle(&source, &graph, &result);
    raw_oracle(&source, &graph, &result);
    assert_eq!(result.edges[0].from, None);
    assert_eq!(result.edges[0].live, ids(&[0, 1]));
    assert_eq!(
        result
            .edges
            .iter()
            .find(|e| e.from == Some(0) && e.to == 0)
            .unwrap()
            .live,
        ids(&[4, 5])
    );
    assert_eq!(result.blocks[0].live_in, ids(&[2, 3]));
    assert_eq!(result.blocks[0].points[0].before, ids(&[2, 3]));
    assert_eq!(result.blocks[0].points[0].after, ids(&[3, 4]));
    assert!(result.values[0].live_blocks.is_empty());
    assert_eq!(result.values[4].live_blocks, [0]);
}

#[test]
fn duplicate_select_arms_load_addresses_and_store_reads_are_all_uses() {
    let source = Program::new(
        0,
        2,
        vec![ins(
            0,
            vec![
                set(
                    1,
                    Expr::select(reg(0), reg(0), Expr::load(reg(0), Width::U8)),
                ),
                Assignment {
                    destination: Place::Memory {
                        address: Expr::binary(BinaryOp::Add, reg(1), reg(1)),
                        width: Width::U8,
                    },
                    value: Expr::binary(BinaryOp::Add, reg(1), reg(0)),
                },
                set(0, Expr::Const(7)),
            ],
            Control::Return(Expr::binary(BinaryOp::Add, reg(1), reg(1))),
        )],
    )
    .unwrap();
    let graph = SsaFunction::build(&source).unwrap();
    let result = value_liveness::analyze(&source, &graph).unwrap();
    oracle(&source, &graph, &result);
    raw_oracle(&source, &graph, &result);
    let old = graph.point(site(0, Some(0))).unwrap().reads[0].value;
    let new = graph.point(site(0, Some(0))).unwrap().definition.unwrap();
    assert_eq!(
        result.values[old.0].uses,
        vec![
            Use::Point {
                site: site(0, Some(0)),
                read: 0
            },
            Use::Point {
                site: site(0, Some(0)),
                read: 1
            },
            Use::Point {
                site: site(0, Some(0)),
                read: 2
            },
            Use::Point {
                site: site(0, Some(1)),
                read: 3
            },
        ]
    );
    assert_eq!(result.values[new.0].uses.len(), 5);
    assert_eq!(
        result.blocks[0].points[0].after,
        [old, new]
            .into_iter()
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect::<Vec<_>>()
    );
    assert_eq!(result.blocks[0].points[1].after, vec![new]);
    assert_eq!(result.blocks[0].points[2].before, vec![new]);
    assert_eq!(result.blocks[0].points[2].after, vec![new]);
    assert!(result.blocks[0].points[3].after.is_empty());
    let unused = graph.point(site(0, Some(2))).unwrap().definition.unwrap();
    assert!(result.values[unused.0].uses.is_empty());
    assert!(result.values[unused.0].live_blocks.is_empty());
}

#[test]
fn unused_phi_operand_still_has_a_syntactic_entry_use() {
    let source = Program::new(0, 1, vec![ins(0, vec![], Control::Return(Expr::Const(9)))]).unwrap();
    let graph = SsaFunction {
        entry: 0,
        register_count: 1,
        values: vec![initial(0), phi(0, 0, &[(None, 0)])],
        blocks: vec![block(0, &[1], vec![point(0, None, None, &[])], &[])],
    };
    let result = value_liveness::analyze(&source, &graph).unwrap();
    oracle(&source, &graph, &result);
    assert!(result.blocks[0].live_in.is_empty());
    assert_eq!(result.edges[0].live, ids(&[0]));
    assert_eq!(
        result.values[0].uses,
        [Use::Phi {
            value: ValueId(1),
            predecessor: None
        }]
    );
    assert!(result.values[1].uses.is_empty());
    assert_eq!(result.peak_live, 1);
}

#[test]
fn loop_phi_cycles_are_retained_without_raw_program_reads() {
    let source = Program::new(
        0,
        1,
        vec![
            ins(
                0,
                vec![],
                Control::Branch {
                    condition: Expr::Const(1),
                    target: 0,
                },
            ),
            ins(1, vec![], Control::Return(Expr::Const(0))),
        ],
    )
    .unwrap();
    let graph = SsaFunction {
        entry: 0,
        register_count: 1,
        values: vec![initial(0), phi(0, 0, &[(None, 0), (Some(0), 1)])],
        blocks: vec![
            block(0, &[1], vec![point(0, None, None, &[])], &[(0, 1)]),
            block(1, &[], vec![point(1, None, None, &[])], &[]),
        ],
    };
    let result = value_liveness::analyze(&source, &graph).unwrap();
    oracle(&source, &graph, &result);
    assert_eq!(result.blocks[0].live_in, ids(&[1]));
    assert_eq!(result.blocks[0].live_out, ids(&[1]));
    assert_eq!(
        result.values[1].uses,
        [Use::Phi {
            value: ValueId(1),
            predecessor: Some(0)
        }]
    );
    assert_eq!(result.values[1].live_blocks, [0]);
}

#[test]
fn multiple_loop_latches_match_source_and_path_oracles() {
    let source = Program::new(
        0,
        2,
        vec![
            ins(0, vec![set(1, Expr::Const(0))], Control::Jump(2)),
            ins(1, vec![], Control::Return(reg(1))),
            ins(
                2,
                vec![],
                Control::Branch {
                    condition: reg(0),
                    target: 4,
                },
            ),
            ins(
                3,
                vec![
                    set(0, Expr::binary(BinaryOp::Sub, reg(0), Expr::Const(1))),
                    set(1, Expr::binary(BinaryOp::Add, reg(1), reg(0))),
                ],
                Control::Jump(2),
            ),
            ins(
                4,
                vec![],
                Control::Branch {
                    condition: reg(1),
                    target: 1,
                },
            ),
            ins(
                5,
                vec![set(0, Expr::binary(BinaryOp::Add, reg(0), Expr::Const(1)))],
                Control::Jump(2),
            ),
        ],
    )
    .unwrap();
    let graph = SsaFunction::build(&source).unwrap();
    let result = value_liveness::analyze(&source, &graph).unwrap();
    oracle(&source, &graph, &result);
    raw_oracle(&source, &graph, &result);
    assert!(result.edges.iter().any(|e| e.from == Some(3) && e.to == 2));
    assert!(result.edges.iter().any(|e| e.from == Some(5) && e.to == 2));
}

#[test]
fn coincident_branch_arms_produce_one_edge_and_empty_blocks_are_retained() {
    let source = Program::new(
        0,
        1,
        vec![
            ins(
                0,
                vec![],
                Control::Branch {
                    condition: reg(0),
                    target: 1,
                },
            ),
            ins(1, vec![], Control::Jump(2)),
            ins(2, vec![], Control::Return(Expr::Const(0))),
        ],
    )
    .unwrap();
    let graph = SsaFunction::build(&source).unwrap();
    let result = value_liveness::analyze(&source, &graph).unwrap();
    oracle(&source, &graph, &result);
    raw_oracle(&source, &graph, &result);
    assert_eq!(result.edges.len(), 3);
    assert!(
        result
            .blocks
            .iter()
            .find(|b| b.start == 1)
            .unwrap()
            .points
            .is_empty()
    );
}

#[test]
fn zero_registers_and_unreachable_source_code_do_not_create_values() {
    let source = Program::new(
        0,
        0,
        vec![
            ins(0, vec![], Control::Return(Expr::Const(4))),
            ins(1, vec![], Control::Return(Expr::Const(99))),
        ],
    )
    .unwrap();
    let graph = SsaFunction::build(&source).unwrap();
    let result = value_liveness::analyze(&source, &graph).unwrap();
    oracle(&source, &graph, &result);
    assert!(result.values.is_empty());
    assert_eq!(result.blocks.len(), 1);
    assert_eq!(result.peak_live, 0);
}

#[test]
fn block_phi_and_input_permutations_have_deterministic_output() {
    let (source, mut graph) = entry_loop();
    let expected = value_liveness::analyze(&source, &graph).unwrap();
    graph.blocks.reverse();
    for block in &mut graph.blocks {
        block.phis.reverse();
    }
    for definition in &mut graph.values {
        if let Definition::Phi { inputs, .. } = definition {
            inputs.reverse();
        }
    }
    assert_eq!(value_liveness::analyze(&source, &graph).unwrap(), expected);
}

#[test]
fn malformed_indices_edge_ownership_and_source_mismatches_are_rejected() {
    let (source, graph) = diamond();
    let mut candidates = Vec::new();
    let mut bad = graph.clone();
    bad.blocks[0].points[0].reads[0].value = ValueId(usize::MAX);
    candidates.push(bad);
    let mut bad = graph.clone();
    let Definition::Phi { inputs, .. } = &mut bad.values[4] else {
        unreachable!()
    };
    inputs[0].predecessor = Some(0);
    candidates.push(bad);
    let mut bad = graph.clone();
    bad.blocks[1].points[0].definition = Some(ValueId(3));
    candidates.push(bad);
    let mut bad = graph.clone();
    bad.blocks[3].points[0].reads.push(RegisterValue {
        register: Reg(1),
        value: ValueId(4),
    });
    candidates.push(bad);
    for bad in candidates {
        assert!(matches!(
            std::panic::catch_unwind(|| value_liveness::analyze(&source, &bad))
                .expect("analysis must not panic"),
            Err(SsaError::Malformed(_))
        ));
    }
    let other = Program::new(
        0,
        2,
        vec![
            ins(
                0,
                vec![],
                Control::Branch {
                    condition: reg(1),
                    target: 2,
                },
            ),
            ins(1, vec![set(1, Expr::Const(11))], Control::Jump(3)),
            ins(2, vec![set(1, Expr::Const(22))], Control::Jump(3)),
            ins(3, vec![], Control::Return(reg(1))),
        ],
    )
    .unwrap();
    assert!(matches!(
        value_liveness::analyze(&other, &graph),
        Err(SsaError::Malformed(_))
    ));
}

#[test]
fn source_and_candidate_limits_are_checked_before_indexed_analysis() {
    let (source, mut graph) = diamond();
    graph
        .values
        .resize(nirvana::ssa::MAX_VALUES + 1, initial(0));
    assert!(matches!(
        value_liveness::analyze(&source, &graph),
        Err(SsaError::Unavailable(_))
    ));
    let source = Program::new(
        0,
        nirvana::ssa::MAX_REGISTERS + 1,
        vec![ins(0, vec![], Control::Return(Expr::Const(0)))],
    )
    .unwrap();
    assert!(matches!(
        value_liveness::analyze(&source, &graph),
        Err(SsaError::Unavailable(_))
    ));
}

fn sum_registers(start: usize, end: usize) -> Expr {
    if end == start + 1 {
        return reg(start);
    }
    let mid = (start + end) / 2;
    Expr::binary(
        BinaryOp::Add,
        sum_registers(start, mid),
        sum_registers(mid, end),
    )
}

#[test]
fn live_membership_exhaustion_declines_the_entire_analysis() {
    // Only ~2,500 syntax nodes and ~2,500 SSA definitions. The large product is
    // live identities across points, which SSA's own input caps do not bound.
    let source = Program::new(
        0,
        1001,
        vec![ins(
            0,
            (0..550).map(|i| set(1000, Expr::Const(i))).collect(),
            Control::Return(sum_registers(0, 1000)),
        )],
    )
    .unwrap();
    let graph = SsaFunction::build(&source).expect("bounded valid SSA fixture");
    assert_eq!(
        value_liveness::analyze(&source, &graph),
        Err(SsaError::Unavailable("liveness memberships"))
    );
}

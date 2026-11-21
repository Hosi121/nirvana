//! Per-function register value tracking with explicit opaque transfer boundaries.
//!
//! The private projection supplies events to SSA, not executable instructions.
//! Closed internal calls retain unchanged identities; other calls consume all
//! guest registers and produce fresh unknown values. Analysis
//! follows function entry and normal effect continuations; arbitrary PC reentry
//! still uses the full checked module state. Memory remains an ordered byte store.

use std::collections::BTreeMap;

use crate::call_footprint;
use crate::ir::{Assignment, Control, Expr, IrInstruction, Place, Program, Reg, Width};
use crate::module_ir::{self, Instruction, Target};
use crate::ssa::{self, Definition, RegisterValue, Site, SsaFunction};
use crate::value_liveness::{self, Liveness};

mod report;

const MAX_FUNCTIONS: usize = 512;
const MAX_MODULE_VALUES: usize = 131_072;
const MAX_MODULE_MEMBERS: usize = 2_000_000;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PointRole {
    Assignment { original: usize },
    VectorAssignment { original: usize },
    VectorGuard,
    DivideSource,
    Target,
    Input { register: Reg },
    OpaqueOutput { register: Reg },
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum BoundaryKind {
    StoreString {
        continuation: u64,
        width: Width,
        repeat: bool,
    },
    Call {
        continuation: u64,
    },
    Divide {
        continuation: u64,
        width: Width,
        signed: bool,
    },
    Tail,
    Return,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CallContract {
    Closed { callee: u64 },
    Opaque { reason: String },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Boundary {
    pub address: u64,
    pub kind: BoundaryKind,
    pub target_reads: Vec<RegisterValue>,
    pub operand_reads: Vec<RegisterValue>,
    /// Register inputs observed before an effect or exit.
    pub inputs: Vec<RegisterValue>,
    /// Fresh identities on a normal effect continuation; values are unknown.
    pub outputs: Vec<RegisterValue>,
    /// Live identities forwarded unchanged to a normal effect continuation.
    pub preserved: Vec<RegisterValue>,
    pub call_contract: Option<CallContract>,
}

#[derive(Clone, Debug)]
pub struct FunctionValues {
    graph: SsaFunction,
    lifetimes: Liveness,
    roles: BTreeMap<Site, PointRole>,
    boundaries: Vec<Boundary>,
    source_instructions: usize,
    guest_registers: usize,
    locals: Result<crate::ssa_destroy::Recovery, String>,
}

impl FunctionValues {
    /// SSA of analysis events. Opaque output assignments have no numeric facts.
    pub fn graph(&self) -> &SsaFunction {
        &self.graph
    }
    pub fn lifetimes(&self) -> &Liveness {
        &self.lifetimes
    }
    pub fn roles(&self) -> &BTreeMap<Site, PointRole> {
        &self.roles
    }
    pub fn boundaries(&self) -> &[Boundary] {
        &self.boundaries
    }
    pub fn source_instructions(&self) -> usize {
        self.source_instructions
    }
    pub fn guest_registers(&self) -> usize {
        self.guest_registers
    }
    pub fn local_recovery(&self) -> &Result<crate::ssa_destroy::Recovery, String> {
        &self.locals
    }
}

#[derive(Clone, Debug)]
pub struct FunctionAnalysis {
    pub function: module_ir::Function,
    /// A local resource or unresolved-control limit retains the function name
    /// and reason, so callers can distinguish unavailable analysis from no uses.
    pub result: Result<FunctionValues, String>,
}

#[derive(Clone, Debug)]
pub struct Analysis {
    pub functions: Vec<FunctionAnalysis>,
    pub call_summaries: call_footprint::Analysis,
}

impl Analysis {
    pub fn to_json(&self) -> Result<String, String> {
        report::render(self).ok_or_else(|| "module value report exceeds bounds".into())
    }
}

/// Analyze each lifted function without modifying the original module or code
/// generators. Individual failures are explicit; aggregate limits fail atomically.
pub fn analyze(program: &module_ir::Program) -> Result<Analysis, String> {
    if program.functions().len() > MAX_FUNCTIONS || program.register_count() >= ssa::MAX_REGISTERS {
        return Err("module value analysis source limit".into());
    }
    let mut functions = Vec::new();
    let mut total_values = 0usize;
    let mut total_members = 0usize;
    let call_summaries = call_footprint::analyze(program)?;
    for function in program.functions() {
        let result = analyze_function(program, function, &call_summaries);
        if let Ok(values) = &result {
            total_values = total_values
                .checked_add(values.graph.values.len())
                .filter(|n| *n <= MAX_MODULE_VALUES)
                .ok_or("module value identity limit")?;
            total_members = total_members
                .checked_add(members(values))
                .filter(|n| *n <= MAX_MODULE_MEMBERS)
                .ok_or("module value storage limit")?;
        }
        functions.push(FunctionAnalysis {
            function: function.clone(),
            result,
        });
    }
    Ok(Analysis {
        functions,
        call_summaries,
    })
}

fn members(values: &FunctionValues) -> usize {
    // Each component has already been bounded by SSA/liveness; account for all
    // retained sparse members across functions before retaining another result.
    values.locals.as_ref().map_or(0, |r| {
        r.plan.by_value.len()
            + r.edges
                .iter()
                .map(|e| e.parallel.len() + e.schedule.copies.len())
                .sum::<usize>()
    }) + values.graph.values.len()
        + values.roles.len()
        + values
            .graph
            .blocks
            .iter()
            .map(|b| {
                b.phis.len()
                    + b.exit_values.len()
                    + b.points.iter().map(|p| 1 + p.reads.len()).sum::<usize>()
            })
            .sum::<usize>()
        + values
            .graph
            .values
            .iter()
            .map(|d| match d {
                Definition::Phi { inputs, .. } => inputs.len(),
                _ => 0,
            })
            .sum::<usize>()
        + values
            .lifetimes
            .blocks
            .iter()
            .map(|b| {
                b.live_in.len()
                    + b.live_out.len()
                    + b.points
                        .iter()
                        .map(|p| p.before.len() + p.after.len())
                        .sum::<usize>()
            })
            .sum::<usize>()
        + values
            .lifetimes
            .edges
            .iter()
            .map(|e| e.live.len())
            .sum::<usize>()
        + values
            .lifetimes
            .values
            .iter()
            .map(|v| v.uses.len() + v.live_blocks.len())
            .sum::<usize>()
        + values
            .boundaries
            .iter()
            .map(|b| {
                b.inputs.len()
                    + b.outputs.len()
                    + b.target_reads.len()
                    + b.operand_reads.len()
                    + b.preserved.len()
            })
            .sum::<usize>()
}

struct Projection<'a> {
    instructions: Vec<IrInstruction>,
    roles: BTreeMap<Site, PointRole>,
    boundaries: Vec<(u64, BoundaryKind)>,
    assignments: usize,
    nodes: usize,
    guest_registers: usize,
    summaries: &'a call_footprint::Analysis,
    call_contracts: BTreeMap<u64, CallContract>,
}

impl Projection<'_> {
    fn expression(&mut self, expression: &Expr) -> Result<(), String> {
        let mut pending = vec![(expression, 1usize)];
        while let Some((e, depth)) = pending.pop() {
            self.nodes += 1;
            if self.nodes > ssa::MAX_NODES || depth > ssa::MAX_DEPTH {
                return Err("module value expression limit".into());
            }
            match e {
                Expr::Register(reg) if reg.0 >= self.guest_registers => {
                    return Err("invalid module value register".into());
                }
                Expr::Binary(_, a, b) => {
                    pending.push((b, depth + 1));
                    pending.push((a, depth + 1));
                }
                Expr::Load { address, .. } => pending.push((address, depth + 1)),
                Expr::Select {
                    condition,
                    taken,
                    not_taken,
                } => {
                    pending.push((not_taken, depth + 1));
                    pending.push((taken, depth + 1));
                    pending.push((condition, depth + 1));
                }
                _ => {}
            }
        }
        Ok(())
    }

    fn push(
        &mut self,
        address: u64,
        out: &mut Vec<Assignment>,
        a: Assignment,
        role: PointRole,
    ) -> Result<(), String> {
        if self.assignments >= ssa::MAX_ASSIGNMENTS {
            return Err("module value assignment limit".into());
        }
        self.assignments += 1;
        self.roles.insert(
            Site {
                instruction: address,
                assignment: Some(out.len()),
            },
            role,
        );
        out.push(a);
        Ok(())
    }

    fn read(
        &mut self,
        address: u64,
        out: &mut Vec<Assignment>,
        expression: Expr,
        role: PointRole,
    ) -> Result<(), String> {
        self.push(
            address,
            out,
            Assignment {
                destination: Reg(self.guest_registers).into(),
                value: expression,
            },
            role,
        )
    }

    fn copy_assignments(
        &mut self,
        address: u64,
        out: &mut Vec<Assignment>,
        source: &[Assignment],
        vector: bool,
    ) -> Result<(), String> {
        // Scan before cloning, including syntactically unselected expressions.
        for (original, assignment) in source.iter().enumerate() {
            if let Place::Memory { address, .. } = &assignment.destination {
                self.expression(address)?;
            }
            self.expression(&assignment.value)?;
            let role = if vector {
                PointRole::VectorAssignment { original }
            } else {
                PointRole::Assignment { original }
            };
            self.push(address, out, assignment.clone(), role)?;
        }
        Ok(())
    }

    fn observe(
        &mut self,
        address: u64,
        out: &mut Vec<Assignment>,
        registers: &[Reg],
    ) -> Result<(), String> {
        for &register in registers {
            self.read(
                address,
                out,
                Expr::Register(register),
                PointRole::Input { register },
            )?;
        }
        Ok(())
    }

    fn instruction(&mut self, instruction: &Instruction) -> Result<(), String> {
        let address = instruction.address();
        let mut assignments = Vec::new();
        let control = match instruction {
            Instruction::StoreString { width, repeat, .. } => {
                let mut inputs = vec![
                    Reg(crate::x86::RAX),
                    Reg(crate::x86::RDI),
                    Reg(crate::x86::DF),
                ];
                let mut outputs = vec![Reg(crate::x86::RDI)];
                if *repeat {
                    inputs.push(Reg(crate::x86::RCX));
                    outputs.push(Reg(crate::x86::RCX));
                }
                self.observe(address, &mut assignments, &inputs)?;
                for register in outputs {
                    self.push(
                        address,
                        &mut assignments,
                        Assignment {
                            destination: register.into(),
                            value: Expr::Const(0),
                        },
                        PointRole::OpaqueOutput { register },
                    )?;
                }
                let continuation = address
                    .checked_add(u64::from(instruction.size()))
                    .ok_or("string store continuation overflow")?;
                self.boundaries.push((
                    address,
                    BoundaryKind::StoreString {
                        continuation,
                        width: *width,
                        repeat: *repeat,
                    },
                ));
                Control::Jump(continuation)
            }
            Instruction::Divide {
                source,
                width,
                signed,
                ..
            } => {
                self.expression(source)?;
                self.read(
                    address,
                    &mut assignments,
                    source.clone(),
                    PointRole::DivideSource,
                )?;
                // Byte division reads AX and writes AL/AH, both within RAX.
                // Wider operations also read and write RDX. Full raw identities
                // include any preserved upper bits in the canonical result.
                let registers: &[Reg] = if *width == Width::U8 {
                    &[Reg(crate::x86::RAX)]
                } else {
                    &[Reg(crate::x86::RAX), Reg(crate::x86::RDX)]
                };
                self.observe(address, &mut assignments, registers)?;
                for &register in registers {
                    self.push(
                        address,
                        &mut assignments,
                        Assignment {
                            destination: register.into(),
                            value: Expr::Const(0),
                        },
                        PointRole::OpaqueOutput { register },
                    )?;
                }
                let continuation = address
                    .checked_add(u64::from(instruction.size()))
                    .ok_or("division continuation overflow")?;
                self.boundaries.push((
                    address,
                    BoundaryKind::Divide {
                        continuation,
                        width: *width,
                        signed: *signed,
                    },
                ));
                Control::Jump(continuation)
            }
            Instruction::Core(i) => {
                self.copy_assignments(address, &mut assignments, &i.assignments, false)?;
                if let Control::Branch { condition, .. } | Control::Return(condition) = &i.control {
                    self.expression(condition)?;
                }
                i.control.clone()
            }
            Instruction::Vector(i) => {
                if let Some(memory) = &i.memory {
                    self.expression(&memory.address)?;
                    self.read(
                        address,
                        &mut assignments,
                        memory.address.clone(),
                        PointRole::VectorGuard,
                    )?;
                }
                self.copy_assignments(address, &mut assignments, &i.assignments, true)?;
                Control::Next
            }
            Instruction::Transfer { target, link, .. } => {
                let summary = match target {
                    Target::Value(Expr::Const(callee)) => self.summaries.at(*callee),
                    _ => None,
                };
                let (reads, clobbers, contract) = if let Some(summary) =
                    summary.filter(|s| s.closed)
                {
                    (
                        summary.reads.clone(),
                        summary.clobbers.clone(),
                        CallContract::Closed {
                            callee: summary.address,
                        },
                    )
                } else {
                    let reason = match target {
                        Target::Plt(_) => "mutable PLT target".into(),
                        Target::Value(Expr::Const(_)) => summary
                            .and_then(|s| s.reason.clone())
                            .unwrap_or_else(|| "target lacks a closed function contract".into()),
                        Target::Value(_) => "dynamic target".into(),
                    };
                    let all: Vec<_> = (0..self.guest_registers).map(Reg).collect();
                    (all.clone(), all, CallContract::Opaque { reason })
                };
                let target_expression = match target {
                    Target::Value(e) => {
                        self.expression(e)?;
                        e.clone()
                    }
                    Target::Plt(address) => Expr::load(Expr::Const(*address), Width::U64),
                };
                self.read(
                    address,
                    &mut assignments,
                    target_expression,
                    PointRole::Target,
                )?;
                if let Some(continuation) = link {
                    self.observe(address, &mut assignments, &reads)?;
                    self.call_contracts.insert(address, contract);
                    // These are fresh opaque definitions. The placeholder RHS
                    // only allows SSA numbering; it supplies no constant fact.
                    for register in clobbers {
                        self.push(
                            address,
                            &mut assignments,
                            Assignment {
                                destination: register.into(),
                                value: Expr::Const(0),
                            },
                            PointRole::OpaqueOutput { register },
                        )?;
                    }
                    self.boundaries.push((
                        address,
                        BoundaryKind::Call {
                            continuation: *continuation,
                        },
                    ));
                    Control::Jump(*continuation)
                } else {
                    // Tail exits expose the entire guest register state, even
                    // when the target itself has a closed call contract.
                    let all: Vec<_> = (0..self.guest_registers).map(Reg).collect();
                    self.observe(address, &mut assignments, &all)?;
                    self.boundaries.push((address, BoundaryKind::Tail));
                    Control::Return(Expr::Const(0))
                }
            }
            Instruction::Return { .. } => {
                self.read(
                    address,
                    &mut assignments,
                    Expr::load(Expr::Register(Reg(crate::x86::RSP)), Width::U64),
                    PointRole::Target,
                )?;
                let all: Vec<_> = (0..self.guest_registers).map(Reg).collect();
                self.observe(address, &mut assignments, &all)?;
                self.boundaries.push((address, BoundaryKind::Return));
                Control::Return(Expr::Const(0))
            }
        };
        self.instructions.push(IrInstruction {
            address,
            size: instruction.size(),
            assignments,
            control,
        });
        Ok(())
    }
}

fn analyze_function(
    program: &module_ir::Program,
    function: &module_ir::Function,
    summaries: &call_footprint::Analysis,
) -> Result<FunctionValues, String> {
    let end = function
        .address
        .checked_add(function.size)
        .ok_or("function address overflow")?;
    let start_index = program
        .instructions()
        .partition_point(|i| i.address() < function.address);
    let end_index = program
        .instructions()
        .partition_point(|i| i.address() < end);
    let source = &program.instructions()[start_index..end_index];
    if source.len() > ssa::MAX_INSTRUCTIONS {
        return Err("module value instruction limit".into());
    }
    let mut projection = Projection {
        instructions: Vec::new(),
        roles: BTreeMap::new(),
        boundaries: Vec::new(),
        assignments: 0,
        nodes: 0,
        guest_registers: program.register_count(),
        summaries,
        call_contracts: BTreeMap::new(),
    };
    for instruction in source {
        projection.instruction(instruction)?;
    }
    let event_program = Program::new(
        function.address,
        program.register_count() + 1,
        projection.instructions,
    )
    .map_err(|e| e.to_string())?;
    let graph = SsaFunction::build(&event_program)
        .ok_or("module value SSA unavailable: control or resource limit")?;
    let lifetimes = value_liveness::analyze(&event_program, &graph).map_err(|e| e.to_string())?;
    let excluded_copies = projection
        .roles
        .iter()
        .filter_map(|(site, role)| {
            (!matches!(
                role,
                PointRole::Assignment { .. } | PointRole::VectorAssignment { .. }
            ))
            .then_some(*site)
        })
        .collect();
    // This remains analysis metadata: opaque module outputs have no executable
    // numeric interpretation. Only real source copies introduce affinities.
    let locals = crate::ssa_locals::analyze(&event_program, &graph, &excluded_copies)
        .map_err(|e| e.to_string())
        .and_then(|groups| {
            let plan = crate::ssa_storage::reuse(&event_program, &graph, &groups).unwrap_or(groups);
            crate::ssa_destroy::lower_with_plan(&event_program, &graph, plan)
                .map(|f| f.into_recovery())
        });
    let mut boundaries: BTreeMap<_, _> = projection
        .boundaries
        .into_iter()
        .map(|(address, kind)| {
            (
                address,
                Boundary {
                    address,
                    kind,
                    target_reads: Vec::new(),
                    operand_reads: Vec::new(),
                    inputs: Vec::new(),
                    outputs: Vec::new(),
                    preserved: Vec::new(),
                    call_contract: projection.call_contracts.remove(&address),
                },
            )
        })
        .collect();
    let mut reached = std::collections::BTreeSet::new();
    for point in graph.blocks.iter().flat_map(|b| &b.points) {
        if let Some(boundary) = boundaries.get_mut(&point.site.instruction) {
            reached.insert(boundary.address);
            match projection.roles.get(&point.site) {
                Some(PointRole::Target) => boundary.target_reads.extend(&point.reads),
                Some(PointRole::DivideSource) => boundary.operand_reads.extend(&point.reads),
                Some(PointRole::Input { .. }) => boundary.inputs.extend(&point.reads),
                Some(PointRole::OpaqueOutput { register }) => {
                    boundary.outputs.push(RegisterValue {
                        register: *register,
                        value: point.definition.ok_or("missing opaque definition")?,
                    })
                }
                _ => {}
            }
        }
    }
    // Effects terminate their projection block. Exit values already name the
    // identities needed on continuation edges, including unchanged registers.
    for block in &graph.blocks {
        if let Some(boundary) = block
            .points
            .last()
            .and_then(|p| boundaries.get_mut(&p.site.instruction))
        {
            let preserved = match boundary.kind {
                BoundaryKind::Divide { .. } | BoundaryKind::StoreString { .. } => None,
                _ => match boundary.call_contract {
                    Some(CallContract::Closed { callee }) => Some(
                        &summaries
                            .at(callee)
                            .ok_or("missing closed call summary")?
                            .preserved,
                    ),
                    _ => continue,
                },
            };
            boundary.preserved.extend(
                block
                    .exit_values
                    .iter()
                    .filter(|v| {
                        v.register.0 < program.register_count()
                            && preserved.map_or_else(
                                || !boundary.outputs.iter().any(|o| o.register == v.register),
                                |registers| {
                                    registers
                                        .binary_search_by_key(&v.register.0, |r| r.0)
                                        .is_ok()
                                },
                            )
                    })
                    .copied(),
            );
        }
    }
    let boundaries = boundaries
        .into_values()
        .filter(|b| reached.contains(&b.address))
        .collect();
    Ok(FunctionValues {
        graph,
        lifetimes,
        roles: projection.roles,
        boundaries,
        source_instructions: source.len(),
        guest_registers: program.register_count(),
        locals,
    })
}

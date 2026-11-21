use super::{
    CallInstruction, CallTarget, Instruction, Limits, Output, Program, PutsOutcome, Report, Status,
    Suspend, VOLATILE_REGISTERS,
};
use crate::binary::x86::{RAX, RDI, RSP};
use crate::model::ir::{Control, ExecutionError, Machine, Stop, Width};

impl Program {
    pub fn run(
        &self,
        input: &[u64],
        memory_base: u64,
        memory: &[u8],
        outcomes: &[PutsOutcome],
        limits: Limits,
    ) -> Result<Report, ExecutionError> {
        let machine = Machine::with_memory(
            self.register_count(),
            input,
            memory_base,
            memory,
            limits.instructions,
        )?;
        let mut run = Run {
            machine,
            outcomes,
            output: Vec::new(),
            consumed: 0,
            reads: limits.external_reads,
            limits,
        };
        let status = run.execute(self);
        Ok(Report {
            status,
            state: run.machine.snapshot(),
            output: run.output,
            consumed: run.consumed,
        })
    }
}

struct Run<'a> {
    machine: Machine,
    outcomes: &'a [PutsOutcome],
    output: Vec<u8>,
    consumed: usize,
    reads: usize,
    limits: Limits,
}

fn stop_status(stop: Stop) -> Status {
    match stop {
        Stop::Fault(fault) => Status::Fault(fault),
        Stop::Limit => Status::Suspended(Suspend::Instructions),
    }
}

impl Run<'_> {
    fn execute(&mut self, program: &Program) -> Status {
        match self.execute_inner(program) {
            Ok(value) => Status::Returned(value),
            Err(status) => status,
        }
    }

    fn execute_inner(&mut self, program: &Program) -> Result<u64, Status> {
        let mut address = program.entry();
        loop {
            let index = program
                .instructions()
                .binary_search_by_key(&address, Instruction::address)
                .expect("validated reachable instruction");
            match &program.instructions()[index] {
                Instruction::Core(instruction) => {
                    self.machine
                        .step(address, &instruction.assignments)
                        .map_err(stop_status)?;
                    address = match &instruction.control {
                        Control::Next => address + u64::from(instruction.size),
                        Control::Jump(target) => *target,
                        Control::Branch { condition, target } => {
                            if condition.evaluate(&self.machine).map_err(Status::Fault)? != 0 {
                                *target
                            } else {
                                address + u64::from(instruction.size)
                            }
                        }
                        Control::Return(value) => {
                            return value.evaluate(&self.machine).map_err(Status::Fault);
                        }
                    };
                }
                Instruction::Call(call) => {
                    self.machine.step(address, &[]).map_err(stop_status)?;
                    self.call(program, call)?;
                    if call.tail {
                        return Ok(self.machine.registers[RAX]);
                    }
                    address += u64::from(call.size);
                }
            }
        }
    }

    fn call(&mut self, program: &Program, call: &CallInstruction) -> Result<(), Status> {
        // CALL's operand is read before its stack write. A direct PLT call
        // instead reads the GOT after that write, inside the import stub.
        let mut target = match call.target {
            CallTarget::Direct(target) => target,
            CallTarget::Register(register) => self.machine.registers[register.0],
            CallTarget::Memory(address) => self
                .machine
                .load(address, Width::U64)
                .map_err(Status::Fault)?,
            CallTarget::Plt(_) => 0,
        };
        if !call.tail {
            self.machine.registers[RSP] = self.machine.registers[RSP].wrapping_sub(8);
            self.machine
                .store(
                    self.machine.registers[RSP],
                    Width::U64,
                    call.address + u64::from(call.size),
                )
                .map_err(Status::Fault)?;
        }
        if let CallTarget::Plt(address) = call.target {
            target = self
                .machine
                .load(address, Width::U64)
                .map_err(Status::Fault)?;
        }
        if target != program.puts_address() {
            return Err(Status::UnknownTarget(target));
        }
        if self.consumed == self.limits.calls {
            return Err(Status::Suspended(Suspend::Calls));
        }

        let mut string = Vec::new();
        let mut address = self.machine.registers[RDI];
        loop {
            if self.reads == 0 {
                return Err(Status::Suspended(Suspend::Reads));
            }
            self.reads -= 1;
            let byte = self
                .machine
                .load(address, Width::U8)
                .map_err(Status::Fault)? as u8;
            if byte == 0 {
                break;
            }
            string.push(byte);
            address = address.wrapping_add(1);
        }

        let outcome = self
            .outcomes
            .get(self.consumed)
            .ok_or(Status::EnvironmentExhausted)?;
        if outcome.registers[9..].iter().any(|&flag| flag > 1) {
            return Err(Status::InvalidOutcome);
        }
        let length = string.len().checked_add(1).ok_or(Status::InvalidOutcome)?;
        let written = match outcome.output {
            Output::All => length,
            Output::Prefix(written) if written <= length => written,
            Output::Prefix(_) => return Err(Status::InvalidOutcome),
        };
        if outcome.registers[0] as u32 as i32 >= 0 && written != length {
            return Err(Status::InvalidOutcome);
        }
        if self
            .output
            .len()
            .checked_add(written)
            .is_none_or(|length| length > self.limits.output_bytes)
        {
            return Err(Status::Suspended(Suspend::Output));
        }

        // Output, clobbers, outcome consumption and callee RET commit together.
        self.output
            .extend_from_slice(&string[..written.min(string.len())]);
        if written > string.len() {
            self.output.push(b'\n');
        }
        for (&register, &value) in VOLATILE_REGISTERS.iter().zip(&outcome.registers) {
            self.machine.registers[register] = value;
        }
        self.consumed += 1;
        self.machine.registers[RSP] = self.machine.registers[RSP].wrapping_add(8);
        Ok(())
    }
}

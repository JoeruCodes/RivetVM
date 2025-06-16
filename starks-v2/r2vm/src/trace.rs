use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TraceEntry {
    pub pc: u64,
    pub registers: [u64; 32],
}

#[derive(Serialize, Debug, Clone, Copy)]
pub struct VmInstruction {
    pub pc: u64,
    pub register: [u64; 32],
}

#[derive(Serialize, Debug, Clone, Copy, PartialEq, Eq)]
pub enum MemoryAccessType {
    Read,
    Write,
}

#[derive(Serialize, Debug, Clone, Copy)]
pub struct MemoryAccessLogEntry {
    pub pc: u64,
    pub address: u64,
    pub value: u64,
    pub access_type: MemoryAccessType,
}

#[derive(Serialize, Default)]
pub struct Tracer {
    pub entries: Vec<VmInstruction>,
    pub memory_entries: Vec<MemoryAccessLogEntry>,
}

impl Tracer {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn record(&mut self, pc: u64, register: &[u64; 32]) {
        self.entries.push(VmInstruction { pc, register: *register });
    }

    pub fn record_memory(
        &mut self,
        pc: u64,
        address: u64,
        value: u64,
        access_type: MemoryAccessType,
    ) {
        self.memory_entries.push(MemoryAccessLogEntry { pc, address, value, access_type });
    }
}

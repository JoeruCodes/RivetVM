use serde::{Deserialize, Serialize};
use std::collections::HashMap;

const GOLDILOCKS_PRIME: u128 = 18446744069414584321u128;

fn mod_pow(mut base: u128, mut exp: u128, modulus: u128) -> u128 {
    let mut result = 1u128;
    base %= modulus;
    while exp > 0 {
        if exp & 1 == 1 {
            result = result.wrapping_mul(base) % modulus;
        }
        base = base.wrapping_mul(base) % modulus;
        exp >>= 1;
    }
    result
}

fn mod_inv(value: u128, modulus: u128) -> u128 {
    mod_pow(value, modulus - 2, modulus)
}

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
    pub time_step: usize,
    pub pc: u64,
    pub address: u64,
    pub value: u64,
    pub access_type: MemoryAccessType,
}

#[derive(Serialize, Default)]
pub struct Tracer {
    pub entries: Vec<VmInstruction>,
    pub memory_entries: Vec<MemoryAccessLogEntry>,

    pub other_cols: Vec<Vec<u128>>,

    pub last_write: HashMap<u64, u64>,
}

impl Tracer {
    pub fn new_with_cols(num_other_cols: usize) -> Self {
        Self {
            entries: Vec::new(),
            memory_entries: Vec::new(),
            other_cols: vec![Vec::new(); num_other_cols],
            last_write: HashMap::new(),
        }
    }

    pub fn new() -> Self {
        Self::new_with_cols(0)
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
        let time_step = self.entries.len().saturating_sub(1);
        self.memory_entries.push(MemoryAccessLogEntry {
            time_step,
            pc,
            address,
            value,
            access_type,
        });

        #[cfg(feature = "trace")]
        {
            use crate::ssa_hook;

            ssa_hook::record(self, "mem_clk", time_step as u128);
            ssa_hook::record(self, "mem_addr", address as u128);
            ssa_hook::record(self, "mem_val", value as u128);
            ssa_hook::record(
                self,
                "mem_is_write",
                if access_type == MemoryAccessType::Write { 1 } else { 0 },
            );

            ssa_hook::record(self, "mem_sel", 1);
        }

        if self.memory_entries.len() >= 2 {
            let pair_idx = self.memory_entries.len() - 2;

            let prev = &self.memory_entries[pair_idx];
            let curr = &self.memory_entries[pair_idx + 1];

            let addr_diff = (curr.address as i128 - prev.address as i128)
                .rem_euclid(GOLDILOCKS_PRIME as i128) as u128;
            let is_addr_same = if addr_diff == 0 { 1u128 } else { 0u128 };
            let inv_addr_diff =
                if addr_diff == 0 { 0 } else { mod_inv(addr_diff, GOLDILOCKS_PRIME) };

            let clk_diff_raw = curr.time_step as i128 - prev.time_step as i128 - 1;
            let clk_diff = if clk_diff_raw >= 0 { clk_diff_raw as u128 } else { 0u128 };

            let base_other = 5 + pair_idx * 35;

            if base_other + 34 < self.other_cols.len() {
                let target_row = prev.time_step;

                self.record_other_at_row(base_other, target_row, is_addr_same);
                self.record_other_at_row(base_other + 1, target_row, inv_addr_diff);
                self.record_other_at_row(base_other + 2, target_row, clk_diff);

                for bit_idx in 0..32 {
                    let bit_val = (clk_diff >> bit_idx) & 1u128;
                    self.record_other_at_row(base_other + 3 + bit_idx, target_row, bit_val);
                }
            }
        }

        #[cfg(feature = "trace")]
        {
            use crate::ssa_hook;

            let last_val = *self.last_write.get(&address).unwrap_or(&0u64);

            let is_first_read = match access_type {
                MemoryAccessType::Read => {
                    let prev_addr = self
                        .memory_entries
                        .last()
                        .map(|e| e.address)
                        .unwrap_or(address.wrapping_add(1));
                    prev_addr != address
                }
                _ => false,
            };

            ssa_hook::record(self, "mem_last_write_val", last_val as u128);
            ssa_hook::record(self, "mem_is_first_read", if is_first_read { 1 } else { 0 });
        }

        if access_type == MemoryAccessType::Write {
            self.last_write.insert(address, value);
        }
    }

    fn ensure_col_len(&mut self, idx: usize, row: usize) -> Option<&mut Vec<u128>> {
        if idx >= self.other_cols.len() {
            self.other_cols.extend((0..=idx - self.other_cols.len()).map(|_| Vec::<u128>::new()));
        }
        let col_vec = &mut self.other_cols[idx];
        if col_vec.len() <= row {
            col_vec.resize(row + 1, 0);
        }
        Some(col_vec)
    }

    pub fn record_other(&mut self, idx: usize, value: u128) {
        let current_row = self.entries.len().saturating_sub(1);
        if let Some(col_vec) = self.ensure_col_len(idx, current_row) {
            col_vec[current_row] = value;
        }
    }

    pub fn record_other_at_row(&mut self, idx: usize, row: usize, value: u128) {
        if let Some(col_vec) = self.ensure_col_len(idx, row) {
            col_vec[row] = value;
        }
    }
}

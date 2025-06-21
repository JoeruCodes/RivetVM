use serde::{Deserialize, Serialize};
use std::collections::HashSet;
use std::fs;

use crate::{
    llvm::air::codegen::{constraint_provider::AirConstraintProvider, AirCodegen},
    mod_pow, ConstraintProvider, Field, Unity,
};
use lang::ctx::RangeProofGroup;
pub mod witness;

#[derive(Debug, Deserialize)]
pub struct TraceEntry {
    pub pc: u64,
    pub register: Vec<u64>,
}

#[derive(Debug, Deserialize)]
pub struct MemoryTraceEntry {
    pub time_step: usize,
    pub pc: u64,
    pub address: u64,
    pub value: u64,
    pub access_type: MemoryAccessType,
}

#[derive(Debug, Deserialize)]
pub enum MemoryAccessType {
    Read,
    Write,
}

#[derive(Clone, Copy, Debug)]
pub struct GoldilocksField;

impl Field for GoldilocksField {
    const PRIME: u128 = 18446744069414584321;

    fn get_prime() -> u128 {
        Self::PRIME
    }

    fn get_nth_root_of_unity(&self, n: usize) -> Unity {
        let p_minus_1 = Self::PRIME - 1;
        let n_u128 = n as u128;

        if p_minus_1 % n_u128 != 0 {
            panic!(
                "A primitive {}-th root of unity does not exist in this field.",
                n
            );
        }

        let generator = 2717u128;

        let exponent = p_minus_1 / n_u128;
        let root = mod_pow(generator, exponent, Self::PRIME);

        Unity { generator: root }
    }
}

mod test {
    use crate::vm::TraceEntry;

    use super::witness::{evaluate_constraints, generate_vm_witness};

    #[test]
    fn test_vm_trace() {
        let llvm_ir = include_str!("../../../r2vm/hello.ll");

        let trace_data = include_str!("../../../r2vm/trace.json");
        let memory_trace_data = include_str!("../../../r2vm/memory_trace.json");
        let other_cols_raw = include_bytes!("../../../r2vm/other_cols.json");

        let trace: Vec<TraceEntry> = serde_json::from_str(trace_data).unwrap();
        let trace_len = trace.len();

        let trace_columns =
            generate_vm_witness(llvm_ir, trace_data, memory_trace_data, other_cols_raw).unwrap();

        evaluate_constraints(trace_columns, llvm_ir, trace_len).unwrap();
    }
}

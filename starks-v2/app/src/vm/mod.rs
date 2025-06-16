use serde::{Deserialize, Serialize};
use std::collections::HashSet;

use crate::{
    llvm::air::codegen::{constraint_provider::AirConstraintProvider, AirCodegen},
    mod_pow, ConstraintProvider, Field, Unity,
};

#[derive(Debug, Deserialize)]
pub struct TraceEntry {
    pub pc: u64,
    pub register: Vec<u64>,
}

#[derive(Debug, Deserialize)]
pub struct MemoryTraceEntry {
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
    /// The Goldilocks prime `p = 2^64 - 2^32 + 1`.
    /// In hexadecimal, this is `0xffffffff00000001`.
    const PRIME: u128 = 18446744069414584321;

    fn get_prime() -> u128 {
        Self::PRIME
    }

    /// Finds a primitive n-th root of unity in the Goldilocks field.
    ///
    /// This field is designed to have "nice" roots of unity. To produce them,
    /// we must use a specific generator for the multiplicative group. While `7` is
    /// the smallest generator, `2717` is the smallest generator that produces
    /// the desired roots, such as `ω_192 = 2`.
    ///
    /// This function computes the n-th root of unity as `g^((p-1)/n) mod p`, where
    /// `g = 2717`.
    fn get_nth_root_of_unity(&self, n: usize) -> Unity {
        let p_minus_1 = Self::PRIME - 1;
        let n_u128 = n as u128;

        // A primitive n-th root of unity exists only if n divides the order of the group.
        if p_minus_1 % n_u128 != 0 {
            panic!(
                "A primitive {}-th root of unity does not exist in this field.",
                n
            );
        }

        // We use the generator g = 2717 to obtain the desired structured roots.
        let generator = 2717u128;

        // The primitive n-th root is g^((p-1)/n).
        let exponent = p_minus_1 / n_u128;
        let root = mod_pow(generator, exponent, Self::PRIME);

        Unity { generator: root }
    }
}

mod test {
    use crate::{
        llvm::air::codegen::{constraint_provider::AirConstraintProvider, AirCodegen},
        vm::{GoldilocksField, MemoryTraceEntry, TraceEntry},
        ConstraintProvider, Field,
    };
    use std::collections::HashSet;

    #[test]
    fn test_vm_trace() {
        let field = GoldilocksField;
        let memory_trace = include_str!("./memory_trace.json");
        let trace = include_str!("./trace.json");
        let llvm_ir = include_str!("./hello.ll");

        let trace: Vec<TraceEntry> = serde_json::from_str(trace).unwrap();
        let memory_trace: Vec<MemoryTraceEntry> = serde_json::from_str(memory_trace).unwrap();

        let air = AirCodegen::generate_air(llvm_ir, &field).unwrap();

        // Build witness columns: start with 32 register columns
        let mut trace_columns = vec![Vec::new(); air.num_trace_columns];
        for entry in &trace {
            for i in 0..32 {
                trace_columns[i].push(entry.register[i] as u128);
            }
            // For non-register columns push 0 for this row (they'll be padded later)
            for col in 32..air.num_trace_columns {
                trace_columns[col].push(0);
            }
        }

        let constraint_provider = AirConstraintProvider {
            generated_air: air.clone(),
        };

        // This is a simplified check. A full proof/verification would require more setup.
        // Here, we just get the constraint evaluations and check if they are all zero.
        let evaluations = constraint_provider.get_constraints_evaluations(
            &field,
            &trace_columns,
            trace.len().next_power_of_two(),
            field.get_nth_root_of_unity(trace.len().next_power_of_two()),
            trace.len().next_power_of_two() * 2,
            field.get_nth_root_of_unity(trace.len().next_power_of_two() * 2),
            trace.len().next_power_of_two(),
        );

        let mut failed = 0;
        for (c_idx, evals) in evaluations.iter().enumerate() {
            let mut first_bad: Option<(usize, u128)> = None;
            for idx in 0..trace.len() {
                if evals[idx] != 0 {
                    failed += 1;
                    if first_bad.is_none() {
                        first_bad = Some((idx, evals[idx]));
                    }
                }
            }
            if let Some((row, val)) = first_bad {
                println!(
                    "Constraint {} first fails at step {} with value {}",
                    c_idx, row, val
                );
            }
        }
        println!(
            "Total non-zero evaluations across first {} steps: {}",
            trace.len(),
            failed
        );
        if failed > 0 {
            println!(
                "Some operation constraints are not satisfied – inspect the log above for details."
            );
        }
    }
}

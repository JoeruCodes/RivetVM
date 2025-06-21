use crate::Field;
use lang::ctx::RangeProofGroup;
pub use lang::{
    constraints::{AirExpression, AirTraceVariable, RowOffset},
    ConstraintSystemVariable, IntPredicate as LangIntPredicate, Operand, StructuredAirConstraint,
};
use lang::{process_llvm_ir, MemoryAccessLogEntry};
use serde_json;
use std::collections::HashMap;
use std::marker::PhantomData;
use std::path::Path;
pub mod constraint_provider;
pub mod memory;
pub mod preprocessors;
pub mod resolvers;

pub struct PreprocessedStructuredConstraints {
    pub phi_condition_map: HashMap<(String, String), ConstraintSystemVariable>,
    pub switch_instructions: Vec<StructuredAirConstraint>,
}

pub struct PreprocessedPhiTransitions {
    pub loop_phi_transitions: HashMap<(String, String), Vec<(ConstraintSystemVariable, Operand)>>,
}

#[derive(Debug, Clone)]
pub struct GeneratedAir<F: Field> {
    pub constraints: Vec<AirExpression>,
    pub num_trace_columns: usize,
    pub memory_trace_columns: Vec<usize>,
    pub ssa_column_map: HashMap<String, usize>,
    pub range_proof_groups: Vec<RangeProofGroup>,
    pub _phantom_field: PhantomData<F>,
}

pub struct AirCodegen {
    pub ctx: lang::ctx::AirGenContext,
}

impl AirCodegen {
    fn new(initial_max_var_id: usize) -> Self {
        AirCodegen {
            ctx: lang::ctx::AirGenContext::new(initial_max_var_id),
        }
    }

    pub fn generate_air<F: Field + Clone>(
        llvm_ir_string: &str,
        _field: &F,
    ) -> Result<GeneratedAir<F>, String> {
        match process_llvm_ir(llvm_ir_string) {
            Ok((structured_constraints, mut memory_log)) => {
                let mut max_var_id = 0;
                for entry in &memory_log {
                    if let Operand::Var(csv) = entry.value {
                        max_var_id = max_var_id.max(csv.0);
                    }
                    max_var_id = max_var_id.max(entry.time_step.0);
                    if let Operand::Var(csv_addr) = entry.address {
                        max_var_id = max_var_id.max(csv_addr.0);
                    }
                }

                let mut air_codegen = AirCodegen::new(max_var_id);

                if air_codegen.ctx.next_available_trace_col < 32 {
                    air_codegen.ctx.next_available_trace_col = 32;
                }

                println!(
                    "AIR Codegen: Context initialized with next_available_trace_col = {}.",
                    air_codegen.ctx.next_available_trace_col
                );

                let preprocessed_data =
                    AirCodegen::preprocess_structured_constraints(&structured_constraints);
                let PreprocessedStructuredConstraints {
                    phi_condition_map,
                    switch_instructions,
                } = preprocessed_data;

                let preprocessed_phi_transitions =
                    AirCodegen::preprocess_phi_transitions(&structured_constraints);

                let mut air_constraints: Vec<AirExpression> = air_codegen
                    .resolve_structured_constraints(
                        structured_constraints,
                        &phi_condition_map,
                        &switch_instructions,
                    );
                println!(
                    "AIR Codegen: Resolved {} AIR constraints from structured ops.",
                    air_constraints.len()
                );

                air_constraints.extend(air_codegen.ctx.drain_internal_constraints());
                println!(
                    "AIR Codegen: Drained internal constraints. Total after structured ops: {}.",
                    air_constraints.len()
                );

                memory_log.sort_unstable();
                println!(
                    "AIR Codegen: Sorted {} memory log entries.",
                    memory_log.len()
                );

                let mem_start_col = air_codegen.ctx.next_available_trace_col.max(64);

                let (
                    mut memory_air_constraints,
                    memory_trace_columns,
                    next_trace_col_idx_after_memory,
                ) = memory::generate_memory_air_constraints(
                    &memory_log,
                    &mut air_codegen.ctx,
                    mem_start_col,
                );

                air_constraints.append(&mut memory_air_constraints);
                air_codegen.ctx.next_available_trace_col = air_codegen
                    .ctx
                    .next_available_trace_col
                    .max(next_trace_col_idx_after_memory);

                println!(
                    "AIR Codegen: Added {} memory AIR constraints. Next available trace col from context: {}.",
                    memory_air_constraints.len(),
                    air_codegen.ctx.next_available_trace_col
                );

                let loop_phi_air_constraints = air_codegen
                    .resolve_phi_transitions(preprocessed_phi_transitions.loop_phi_transitions);
                air_constraints.extend(loop_phi_air_constraints);

                let memory_trace_column_indices = vec![
                    memory_trace_columns.clk.0,
                    memory_trace_columns.addr.0,
                    memory_trace_columns.val.0,
                    memory_trace_columns.is_write.0,
                    memory_trace_columns.last_write_val.0,
                    memory_trace_columns.is_first_read.0,
                ];

                let mut final_map = air_codegen.ctx.ssa_column_map().clone();

                for reg_idx in 0..32 {
                    final_map.insert(format!("reg{}", reg_idx), reg_idx);
                }

                final_map.insert("mem_clk".to_string(), memory_trace_columns.clk.0);
                final_map.insert("mem_addr".to_string(), memory_trace_columns.addr.0);
                final_map.insert("mem_val".to_string(), memory_trace_columns.val.0);
                final_map.insert("mem_is_write".to_string(), memory_trace_columns.is_write.0);

                final_map.insert(
                    "mem_last_write_val".to_string(),
                    memory_trace_columns.last_write_val.0,
                );
                final_map.insert(
                    "mem_is_first_read".to_string(),
                    memory_trace_columns.is_first_read.0,
                );

                Ok(GeneratedAir {
                    constraints: air_constraints,
                    num_trace_columns: air_codegen.ctx.next_available_trace_col,
                    memory_trace_columns: memory_trace_column_indices,
                    ssa_column_map: final_map,
                    range_proof_groups: air_codegen.ctx.range_proof_groups().clone(),
                    _phantom_field: PhantomData,
                })
            }
            Err(e) => Err(format!("LLVM IR processing failed: {}", e)),
        }
    }
}

impl<F: Field> GeneratedAir<F> {
    pub fn write_mapping_json(&self, path: &Path) -> std::io::Result<()> {
        std::fs::write(path, serde_json::to_string(&self.ssa_column_map)?)
    }

    pub fn write_range_proofs_json(&self, path: &Path) -> std::io::Result<()> {
        std::fs::write(path, serde_json::to_string(&self.range_proof_groups)?)
    }
}

use super::types::GeneratedAir;
use crate::Field;
pub use lang::{
    ConstraintSystemVariable, IntPredicate as LangIntPredicate, Operand, StructuredAirConstraint,
};
use lang::{MemoryAccessLogEntry, constraints::AirExpression, process_llvm_ir};
use std::collections::HashMap;
use std::marker::PhantomData;

pub mod memory;
pub mod preprocessors;
pub mod resolvers;

#[derive(Debug, Clone)]
pub struct AirCodegen {
    pub ctx: lang::ctx::AirGenContext,
}

pub struct PreprocessedStructuredConstraints {
    pub phi_condition_map: HashMap<(String, String), ConstraintSystemVariable>,
    pub switch_instructions: Vec<StructuredAirConstraint>,
}

pub struct PreprocessedPhiTransitions {
    pub loop_phi_transitions: HashMap<(String, String), Vec<(ConstraintSystemVariable, Operand)>>,
}

impl AirCodegen {
    pub fn new(initial_max_var_id: usize) -> Self {
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
                for constraint in &structured_constraints {
                    if let StructuredAirConstraint::Add(v) = constraint {
                        max_var_id = max_var_id.max(v.result.0);
                    }
                }
                for entry in &memory_log {
                    if let Operand::Var(csv) = entry.value {
                        max_var_id = max_var_id.max(csv.0);
                    }
                    if let Operand::Var(csv_addr) = entry.address {
                        max_var_id = max_var_id.max(csv_addr.0);
                    }
                }

                let mut air_codegen = AirCodegen::new(max_var_id);

                let preprocessed_data =
                    AirCodegen::preprocess_structured_constraints(&structured_constraints);

                let mut air_constraints: Vec<AirExpression> = air_codegen
                    .resolve_structured_constraints(
                        structured_constraints,
                        &preprocessed_data.phi_condition_map,
                        &preprocessed_data.switch_instructions,
                    );

                air_constraints.extend(air_codegen.ctx.drain_internal_constraints());

                memory_log.sort_unstable();

                let next_trace_col = air_codegen.ctx.next_available_trace_col;
                let (mut memory_air_constraints, _memory_trace_columns, next_trace_col_idx) =
                    memory::generate_memory_air_constraints(
                        &memory_log,
                        &mut air_codegen.ctx,
                        next_trace_col,
                    );

                air_constraints.append(&mut memory_air_constraints);
                air_codegen.ctx.next_available_trace_col = air_codegen
                    .ctx
                    .next_available_trace_col
                    .max(next_trace_col_idx);

                Ok(GeneratedAir {
                    num_trace_columns: air_codegen.ctx.next_available_trace_col,
                    constraints: air_constraints,
                    _phantom_field: PhantomData,
                })
            }
            Err(e) => Err(format!("LLVM IR processing failed: {}", e)),
        }
    }
}

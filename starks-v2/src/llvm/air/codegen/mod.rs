use crate::Field;
use lang::ConstraintSystemVariable as LangVariable;
use lang::constraints::{AirExpression, AirTraceVariable, RowOffset};
use lang::ctx::AirGenContext;
use lang::process_llvm_ir;
pub use lang::{
    ConstraintSystemVariable, IntPredicate as LangIntPredicate, Operand, StructuredAirConstraint,
};
use std::collections::HashMap;
use std::marker::PhantomData;
pub mod ctx;
pub mod resolvers;
use super::types::GeneratedAir;
pub mod memory;
pub mod preprocessors;

pub struct AirCodegen {
    pub ctx: AirGenContext,
}

pub struct PreprocessedStructuredConstraints {
    phi_condition_map: HashMap<(String, String), ConstraintSystemVariable>,
    switch_instructions: Vec<StructuredAirConstraint>,
}

pub struct PreprocessedPhiTransitions {
    loop_phi_transitions: HashMap<(String, String), Vec<(ConstraintSystemVariable, Operand)>>,
}

impl AirCodegen {
    pub fn new(initial_max_var_id: usize) -> Self {
        AirCodegen {
            ctx: AirGenContext::new(initial_max_var_id),
        }
    }

    pub fn generate_air<F: Field + Clone>(
        llvm_ir_string: &str,
        _field: &F,
    ) -> Result<GeneratedAir<F>, String> {
        match process_llvm_ir(llvm_ir_string) {
            Ok((structured_constraints, mut memory_log)) => {
                println!(
                    "LANG Processing: Found {} structured constraints and {} memory log entries.",
                    structured_constraints.len(),
                    memory_log.len()
                );

                let mut max_var_id = 0;
                for constraint in &structured_constraints {
                    match constraint {
                        StructuredAirConstraint::Add(v) => max_var_id = max_var_id.max(v.result.0),
                        StructuredAirConstraint::Sub(v) => max_var_id = max_var_id.max(v.result.0),
                        StructuredAirConstraint::Multiply(v) => {
                            max_var_id = max_var_id.max(v.result.0)
                        }
                        StructuredAirConstraint::SDiv(v) => max_var_id = max_var_id.max(v.result.0),
                        StructuredAirConstraint::UDiv(v) => max_var_id = max_var_id.max(v.result.0),
                        StructuredAirConstraint::Shl(v) => max_var_id = max_var_id.max(v.result.0),
                        StructuredAirConstraint::Shr(v) => max_var_id = max_var_id.max(v.result.0),
                        StructuredAirConstraint::AShr(v) => max_var_id = max_var_id.max(v.result.0),
                        StructuredAirConstraint::And(v) => max_var_id = max_var_id.max(v.result.0),
                        StructuredAirConstraint::Or(v) => max_var_id = max_var_id.max(v.result.0),
                        StructuredAirConstraint::Xor(v) => max_var_id = max_var_id.max(v.result.0),
                        StructuredAirConstraint::Icmp(v) => max_var_id = max_var_id.max(v.result.0),
                        StructuredAirConstraint::Phi(v) => max_var_id = max_var_id.max(v.result.0),
                        StructuredAirConstraint::Alloca { ptr_result, .. } => {
                            max_var_id = max_var_id.max(ptr_result.0)
                        }
                        StructuredAirConstraint::SRem(v) => max_var_id = max_var_id.max(v.result.0),
                        StructuredAirConstraint::URem(v) => max_var_id = max_var_id.max(v.result.0),
                        StructuredAirConstraint::FAdd(v) => max_var_id = max_var_id.max(v.result.0),
                        _ => {}
                    }
                }
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

                let initial_next_trace_col_for_memory = air_codegen.ctx.next_available_trace_col;
                let (
                    mut memory_air_constraints,
                    _memory_trace_columns,
                    next_trace_col_idx_after_memory,
                ) = memory::generate_memory_air_constraints(
                    &memory_log,
                    &mut air_codegen.ctx,
                    initial_next_trace_col_for_memory,
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

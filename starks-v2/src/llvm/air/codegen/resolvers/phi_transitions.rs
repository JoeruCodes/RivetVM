use std::collections::HashMap;

use lang::Operand;
use lang::constraints::lang_operand_to_air_expression;

use crate::llvm::air::codegen::AirCodegen;
use crate::llvm::air::codegen::LangVariable;
use lang::constraints::{AirExpression, AirTraceVariable, RowOffset};
use lang::ctx::AirGenContext;

impl AirCodegen {
    pub fn resolve_phi_transitions(
        &self,
        loop_phi_transitions: HashMap<(String, String), Vec<(LangVariable, Operand)>>,
    ) -> Vec<AirExpression> {
        let mut air_constraints = Vec::new();

        for ((header_block, _latch_block), transitions) in loop_phi_transitions {
            for (phi_res_in_header, val_from_latch_op) in transitions {
                let phi_res_air_var = AirTraceVariable(phi_res_in_header.0);
                let val_from_latch_expr = lang_operand_to_air_expression(val_from_latch_op);

                let transition_constraint = AirExpression::Sub(
                    Box::new(AirExpression::Trace(phi_res_air_var, RowOffset::Next)),
                    Box::new(val_from_latch_expr),
                );
                air_constraints.push(transition_constraint.clone());
                println!(
                    "  Loop PHI Transition: Added Next Row constraint for {:?} in block '{}': {:?}_next - {:?}_current = 0",
                    phi_res_in_header, header_block, phi_res_air_var, val_from_latch_op
                );
            }
        }

        air_constraints
    }
}

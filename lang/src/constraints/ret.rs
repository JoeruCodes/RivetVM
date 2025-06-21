use std::collections::HashMap;

use crate::{
    constraints::ResolveConstraint, ctx::AirGenContext, ConstraintSystemVariable, Operand,
    StructuredAirConstraint,
};

use super::{lang_operand_to_air_expression, AirExpression, AirTraceVariable, RowOffset};

#[derive(Debug, Clone)]
pub struct Ret {
    pub value: Option<Operand>,
    pub block_name: String,
    pub time_step: ConstraintSystemVariable,
}

impl ResolveConstraint for Ret {
    fn resolve(
        &self,
        air_constraints: &mut Vec<AirExpression>,
        ctx: &mut AirGenContext,
        _phi_condition_map: &HashMap<(String, String), ConstraintSystemVariable>,
        _switch_instructions: &Vec<StructuredAirConstraint>,
    ) {
        if let Some(frame) = ctx.call_stack.pop() {
            if let (Some(return_value), Some(dest_var)) = (self.value, frame.return_value_dest) {
                let dest_expr =
                    AirExpression::Trace(AirTraceVariable(dest_var.0), RowOffset::Current);
                let src_expr = ctx.expr_for_operand(return_value);
                air_constraints.push(dest_expr - src_expr);
            }
            ctx.set_next_block(Some(frame.return_to_block));
        } else {
            ctx.set_next_block(None);
        }
    }
}

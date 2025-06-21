use std::collections::HashMap;

use crate::{
    constraints::{
        lang_operand_to_air_expression, AirExpression, AirTraceVariable, ResolveConstraint,
        RowOffset,
    },
    ctx::AirGenContext,
    ConstraintSystemVariable, Operand, StructuredAirConstraint,
};

#[derive(Debug, Clone)]
pub struct AtomicCmpXchg {
    pub ptr: Operand,
    pub cmp: Operand,
    pub new: Operand,
    pub result_val: ConstraintSystemVariable,
    pub result_success: ConstraintSystemVariable,
    pub block_name: String,
    pub time_step: ConstraintSystemVariable,
}

impl ResolveConstraint for AtomicCmpXchg {
    fn resolve(
        &self,
        constraints: &mut Vec<AirExpression>,
        ctx: &mut AirGenContext,
        _phi_condition_map: &HashMap<(String, String), ConstraintSystemVariable>,
        _switch_instructions: &Vec<StructuredAirConstraint>,
    ) {
        let loaded_val_expr =
            AirExpression::Trace(AirTraceVariable(self.result_val.0), RowOffset::Current);
        let cmp_expr = ctx.expr_for_operand(self.cmp);
        let success_expr =
            AirExpression::Trace(AirTraceVariable(self.result_success.0), RowOffset::Current);
        constraints.push((loaded_val_expr.clone() - cmp_expr.clone()) * success_expr.clone());

        let new_val_expr = ctx.expr_for_operand(self.new);
        let value_to_write_expr = (success_expr.clone() * new_val_expr)
            + ((AirExpression::Constant(1) - success_expr) * loaded_val_expr);

        let written_val_var = ctx.new_aux_variable();
        let written_val_expr = AirExpression::Trace(written_val_var, RowOffset::Current);
        constraints.push(written_val_expr - value_to_write_expr);
    }
}

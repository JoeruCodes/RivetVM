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
pub struct ReturnAddress {
    pub operand1: Operand,
    pub operand2: Operand,
    pub result: ConstraintSystemVariable,
    pub block_name: String,
}

impl ResolveConstraint for ReturnAddress {
    fn resolve(
        &self,
        constraints: &mut Vec<AirExpression>,
        ctx: &mut AirGenContext,
        phi_condition_map: &HashMap<(String, String), ConstraintSystemVariable>,
        switch_instructions: &Vec<StructuredAirConstraint>,
    ) {
        let reg_col_opt = ctx.col_for_ssa(self.result);

        let dest_col = ctx.new_aux_variable();
        ctx.bind_ssa_var(self.result, dest_col.0);

        let operand1_expr = ctx.expr_for_operand(self.operand1);
        let operand2_expr = ctx.expr_for_operand(self.operand2);
        let result_expr = AirExpression::Trace(dest_col, RowOffset::Current);

        constraints.push((operand1_expr + operand2_expr) - result_expr.clone());

        if let Some(reg_col) = reg_col_opt {
            let selector = ctx.new_row_selector();
            let reg_expr = AirExpression::Trace(AirTraceVariable(reg_col), RowOffset::Current);
            let diff = AirExpression::Sub(Box::new(result_expr), Box::new(reg_expr));
            ctx.add_row_gated_constraint(selector, diff);
        }
    }
}

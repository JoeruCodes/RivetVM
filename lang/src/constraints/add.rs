use std::collections::HashMap;

use crate::{
    constraints::{AirExpression, ResolveConstraint, RowOffset},
    ConstraintSystemVariable, Operand, StructuredAirConstraint,
};

#[derive(Debug, Clone)]
pub struct Add {
    pub operand1: Operand,
    pub operand2: Operand,
    pub result: ConstraintSystemVariable,
    pub block_name: String,
}

impl ResolveConstraint for Add {
    fn resolve(
        &self,
        constraints: &mut Vec<super::AirExpression>,
        ctx: &mut crate::ctx::AirGenContext,
        phi_condition_map: &HashMap<(String, String), ConstraintSystemVariable>,
        switch_instructions: &Vec<StructuredAirConstraint>,
    ) {
        let op1_expr = ctx.expr_for_operand(self.operand1);
        let op2_expr = ctx.expr_for_operand(self.operand2);

        let reg_col_opt = ctx.col_for_ssa(self.result);

        let dest_col = ctx.new_aux_variable();
        ctx.bind_ssa_var(self.result, dest_col.0);
        let res_expr = AirExpression::Trace(dest_col, RowOffset::Current);

        let sum_expr = AirExpression::Add(Box::new(op1_expr), Box::new(op2_expr));
        let final_expr = AirExpression::Sub(Box::new(sum_expr), Box::new(res_expr.clone()));
        constraints.push(final_expr);

        if let Some(reg_col) = reg_col_opt {
            use crate::constraints::{AirExpression, AirTraceVariable};
            let reg_expr = AirExpression::Trace(AirTraceVariable(reg_col), RowOffset::Current);
            let selector_expr = ctx.new_row_selector();
            let eq_expr = AirExpression::Sub(Box::new(res_expr), Box::new(reg_expr));
            ctx.add_row_gated_constraint(selector_expr, eq_expr);
        }
    }
}

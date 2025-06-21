use std::collections::HashMap;

use crate::{
    constraints::{lang_operand_to_air_expression, AirExpression, ResolveConstraint, RowOffset},
    ConstraintSystemVariable, Operand, StructuredAirConstraint,
};

#[derive(Debug, Clone)]
pub struct Select {
    pub condition: Operand,
    pub true_value: Operand,
    pub false_value: Operand,
    pub result: ConstraintSystemVariable,
    pub block_name: String,
}

impl ResolveConstraint for Select {
    fn resolve(
        &self,
        constraints: &mut Vec<super::AirExpression>,
        ctx: &mut crate::ctx::AirGenContext,
        phi_condition_map: &HashMap<(String, String), ConstraintSystemVariable>,
        switch_instructions: &Vec<StructuredAirConstraint>,
    ) {
        let reg_col_opt = ctx.col_for_ssa(self.result);

        let dest_col = ctx.new_aux_variable();
        ctx.bind_ssa_var(self.result, dest_col.0);

        let cond_expr = ctx.expr_for_operand(self.condition);
        let true_val_expr = ctx.expr_for_operand(self.true_value);
        let false_val_expr = ctx.expr_for_operand(self.false_value);
        let res_expr = AirExpression::Trace(dest_col, RowOffset::Current);

        let term1 = AirExpression::Mul(Box::new(cond_expr.clone()), Box::new(true_val_expr));

        let one_minus_cond =
            AirExpression::Sub(Box::new(AirExpression::Constant(1)), Box::new(cond_expr));
        let term2 = AirExpression::Mul(Box::new(one_minus_cond), Box::new(false_val_expr));

        let selected_value_expr = AirExpression::Add(Box::new(term1), Box::new(term2));

        let final_expr =
            AirExpression::Sub(Box::new(selected_value_expr), Box::new(res_expr.clone()));
        constraints.push(final_expr);

        if let Some(reg_col) = reg_col_opt {
            use crate::constraints::{AirExpression, AirTraceVariable};
            let selector_expr = ctx.new_row_selector();
            let reg_expr = AirExpression::Trace(AirTraceVariable(reg_col), RowOffset::Current);
            let eq_expr = AirExpression::Sub(Box::new(res_expr), Box::new(reg_expr));
            ctx.add_row_gated_constraint(selector_expr, eq_expr);
        }
    }
}

use std::collections::HashMap;

use crate::{
    constraints::{AirExpression, ResolveConstraint, RowOffset},
    ConstraintSystemVariable, Operand, StructuredAirConstraint,
};
#[derive(Debug, Clone)]
pub struct Or {
    pub operand1: Operand,
    pub operand2: Operand,
    pub result: ConstraintSystemVariable,
    pub block_name: String,
    pub is_fp: bool,
    pub operand_bitwidth: u32,
}

impl ResolveConstraint for Or {
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

        let op1_decomped =
            ctx.add_unsigned_range_proof_constraints(op1_expr.clone(), self.operand_bitwidth);

        let op2_decomped =
            ctx.add_unsigned_range_proof_constraints(op2_expr.clone(), self.operand_bitwidth);
        let res_decomped =
            ctx.add_unsigned_range_proof_constraints(res_expr.clone(), self.operand_bitwidth);

        let final_constraints = op1_decomped
            .into_iter()
            .zip(op2_decomped)
            .zip(res_decomped)
            .map(|((o1, o2), res)| {
                let op1_expr = AirExpression::Trace(o1, RowOffset::Current);
                let op2_expr = AirExpression::Trace(o2, RowOffset::Current);
                let res_expr = AirExpression::Trace(res, RowOffset::Current);

                let a_plus_b =
                    AirExpression::Add(Box::new(op1_expr.clone()), Box::new(op2_expr.clone()));
                let a_times_b = AirExpression::Mul(Box::new(op1_expr), Box::new(op2_expr));
                let or_val_expr = AirExpression::Sub(Box::new(a_plus_b), Box::new(a_times_b));
                let final_expr = AirExpression::Sub(Box::new(or_val_expr), Box::new(res_expr));
                final_expr
            });

        constraints.extend(final_constraints);

        if let Some(reg_col) = reg_col_opt {
            use crate::constraints::{AirExpression, AirTraceVariable};
            let selector_expr = ctx.new_row_selector();
            let reg_expr = AirExpression::Trace(AirTraceVariable(reg_col), RowOffset::Current);
            let eq_expr = AirExpression::Sub(Box::new(res_expr.clone()), Box::new(reg_expr));
            ctx.add_row_gated_constraint(selector_expr, eq_expr);
        }
    }
}

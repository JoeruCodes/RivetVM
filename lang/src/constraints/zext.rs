use std::collections::HashMap;

use crate::{
    constraints::{
        lang_operand_to_air_expression, AirExpression, AirTraceVariable, ResolveConstraint,
        RowOffset,
    },
    ConstraintSystemVariable, Operand, StructuredAirConstraint,
};

#[derive(Debug, Clone)]
pub struct ZExt {
    pub operand: Operand,
    pub result: ConstraintSystemVariable,
    pub operand_bitwidth: u32,
    pub block_name: String,
}

impl ResolveConstraint for ZExt {
    fn resolve(
        &self,
        constraints: &mut Vec<super::AirExpression>,
        ctx: &mut crate::ctx::AirGenContext,
        phi_condition_map: &HashMap<(String, String), ConstraintSystemVariable>,
        switch_instructions: &Vec<StructuredAirConstraint>,
    ) {
        let op_expr = ctx.expr_for_operand(self.operand);

        let reg_col_opt = ctx.col_for_ssa(self.result);

        let dest_col = ctx.new_aux_variable();
        ctx.bind_ssa_var(self.result, dest_col.0);
        let res_expr = AirExpression::Trace(dest_col, RowOffset::Current);

        ctx.add_unsigned_range_proof_constraints(op_expr.clone(), self.operand_bitwidth);

        constraints.push(AirExpression::Sub(
            Box::new(res_expr.clone()),
            Box::new(op_expr),
        ));

        if let Some(reg_col) = reg_col_opt {
            let sel = ctx.new_row_selector();
            let reg_expr = AirExpression::Trace(AirTraceVariable(reg_col), RowOffset::Current);
            let diff = AirExpression::Sub(Box::new(res_expr), Box::new(reg_expr));
            ctx.add_row_gated_constraint(sel, diff);
        }
    }
}

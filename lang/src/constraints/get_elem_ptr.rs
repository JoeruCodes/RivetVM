use std::collections::HashMap;

use crate::{
    constraints::{
        lang_operand_to_air_expression, AirExpression, AirTraceVariable, ResolveConstraint,
        RowOffset,
    },
    ConstraintSystemVariable, Operand, StructuredAirConstraint,
};
#[derive(Debug, Clone)]
pub struct GetElementPtr {
    pub base: Operand,
    pub index: Operand,
    pub element_size_bytes: u64,
    pub result: ConstraintSystemVariable,
    pub block_name: String,
}

impl ResolveConstraint for GetElementPtr {
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

        let base_expr = ctx.expr_for_operand(self.base);
        let index_expr = ctx.expr_for_operand(self.index);
        let res_expr = AirExpression::Trace(dest_col, RowOffset::Current);

        let size_expr = AirExpression::Constant(self.element_size_bytes as u128);

        let offset_expr = AirExpression::Mul(Box::new(index_expr), Box::new(size_expr));

        let addr_expr = AirExpression::Add(Box::new(base_expr), Box::new(offset_expr));

        constraints.push(AirExpression::Sub(
            Box::new(res_expr.clone()),
            Box::new(addr_expr),
        ));

        if let Some(reg_col) = reg_col_opt {
            let sel = ctx.new_row_selector();
            let reg_expr = AirExpression::Trace(AirTraceVariable(reg_col), RowOffset::Current);
            let diff = AirExpression::Sub(Box::new(res_expr), Box::new(reg_expr));
            ctx.add_row_gated_constraint(sel, diff);
        }
    }
}

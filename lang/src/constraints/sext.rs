use std::collections::HashMap;

use crate::{
    constraints::{
        lang_operand_to_air_expression, AirExpression, AirTraceVariable, ResolveConstraint,
        RowOffset,
    },
    ConstraintSystemVariable, Operand, StructuredAirConstraint,
};

#[derive(Debug, Clone)]
pub struct SExt {
    pub operand: Operand,
    pub result: ConstraintSystemVariable,
    pub operand_bitwidth: u32,
    pub result_bitwidth: u32,
    pub block_name: String,
}

impl ResolveConstraint for SExt {
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

        let (_op_bits, op_msb_expr_opt) =
            ctx.add_signed_range_proof_constraints(op_expr.clone(), self.operand_bitwidth);
        let op_msb_expr = op_msb_expr_opt.expect("Signed range proof should provide the sign bit");

        let extension_const = (1u128 << self.result_bitwidth) - (1u128 << self.operand_bitwidth);
        let extension_val = AirExpression::Mul(
            Box::new(op_msb_expr),
            Box::new(AirExpression::Constant(extension_const)),
        );

        let sext_val = AirExpression::Add(Box::new(op_expr), Box::new(extension_val));
        constraints.push(AirExpression::Sub(
            Box::new(res_expr.clone()),
            Box::new(sext_val),
        ));

        if let Some(reg_col) = reg_col_opt {
            let selector = ctx.new_row_selector();
            let reg_expr = AirExpression::Trace(AirTraceVariable(reg_col), RowOffset::Current);
            let diff = AirExpression::Sub(Box::new(res_expr), Box::new(reg_expr));
            ctx.add_row_gated_constraint(selector, diff);
        }
    }
}

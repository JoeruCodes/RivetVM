use std::collections::HashMap;

use crate::{
    constraints::{lang_operand_to_air_expression, AirExpression, ResolveConstraint, RowOffset},
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
        let op_expr = lang_operand_to_air_expression(self.operand);
        let res_expr =
            AirExpression::Trace(super::AirTraceVariable(self.result.0), RowOffset::Current);

        let (_op_bits, op_msb_expr_opt) =
            ctx.add_signed_range_proof_constraints(op_expr.clone(), self.operand_bitwidth);
        let op_msb_expr = op_msb_expr_opt.expect("Signed range proof should provide the sign bit");

        let extension_const = (1u128 << self.result_bitwidth) - (1u128 << self.operand_bitwidth);
        let extension_val = AirExpression::Mul(
            Box::new(op_msb_expr),
            Box::new(AirExpression::Constant(extension_const)),
        );

        let sext_val = AirExpression::Add(Box::new(op_expr), Box::new(extension_val));
        constraints.push(AirExpression::Sub(Box::new(res_expr), Box::new(sext_val)));
    }
}

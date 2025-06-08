use std::collections::HashMap;

use crate::{
    constraints::{lang_operand_to_air_expression, AirExpression, ResolveConstraint, RowOffset},
    ConstraintSystemVariable, Operand, StructuredAirConstraint,
};

#[derive(Debug, Clone)]
pub struct And {
    pub operand1: Operand,
    pub operand2: Operand,
    pub result: ConstraintSystemVariable,
    pub block_name: String,
    pub is_fp: bool,
    pub operand_bitwidth: u32,
}

impl ResolveConstraint for And {
    fn resolve(
        &self,
        constraints: &mut Vec<super::AirExpression>,
        ctx: &mut crate::ctx::AirGenContext,
        phi_condition_map: &HashMap<(String, String), ConstraintSystemVariable>,
        switch_instructions: &Vec<StructuredAirConstraint>,
    ) {
        let op1_expr = lang_operand_to_air_expression(self.operand1);
        let op2_expr = lang_operand_to_air_expression(self.operand2);
        let res_expr =
            AirExpression::Trace(super::AirTraceVariable(self.result.0), RowOffset::Current);

        let op1_decomped =
            ctx.add_unsigned_range_proof_constraints(op1_expr.clone(), self.operand_bitwidth);

        let op2_decomped =
            ctx.add_unsigned_range_proof_constraints(op2_expr.clone(), self.operand_bitwidth);
        let res_decomped =
            ctx.add_unsigned_range_proof_constraints(res_expr, self.operand_bitwidth);

        let final_constraints = op1_decomped
            .into_iter()
            .zip(op2_decomped)
            .zip(res_decomped)
            .map(|((o1, o2), res)| {
                AirExpression::Sub(
                    Box::new(AirExpression::Mul(
                        Box::new(AirExpression::Trace(o1, RowOffset::Current)),
                        Box::new(AirExpression::Trace(o2, RowOffset::Current)),
                    )),
                    Box::new(AirExpression::Trace(res, RowOffset::Current)),
                )
            });
        constraints.extend(final_constraints);
    }
}

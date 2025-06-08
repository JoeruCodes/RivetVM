use std::collections::HashMap;

use crate::{
    constraints::{lang_operand_to_air_expression, AirExpression, ResolveConstraint, RowOffset},
    ConstraintSystemVariable, Operand, StructuredAirConstraint,
};

#[derive(Debug, Clone)]
pub struct Xor {
    pub operand1: Operand,
    pub operand2: Operand,
    pub result: ConstraintSystemVariable,
    pub block_name: String,
    pub is_fp: bool,
    pub operand_bitwidth: u32,
}

impl ResolveConstraint for Xor {
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

        let final_constaints = op1_decomped
            .into_iter()
            .zip(op2_decomped)
            .zip(res_decomped)
            .map(|((o1, o2), res)| {
                let op1_expr = AirExpression::Trace(o1, RowOffset::Current);
                let op2_expr = AirExpression::Trace(o2, RowOffset::Current);
                let res = AirExpression::Trace(res, RowOffset::Current);
                let a_plus_b =
                    AirExpression::Add(Box::new(op1_expr.clone()), Box::new(op2_expr.clone()));
                let a_times_b =
                    AirExpression::Mul(Box::new(op1_expr.clone()), Box::new(op2_expr.clone()));
                let two_const = AirExpression::Constant(2);
                let two_a_b = AirExpression::Mul(Box::new(two_const), Box::new(a_times_b));
                let xor_val_expr = AirExpression::Sub(Box::new(a_plus_b), Box::new(two_a_b));
                let final_expr = AirExpression::Sub(Box::new(xor_val_expr), Box::new(res));

                final_expr
            });

        constraints.extend(final_constaints);
    }
}

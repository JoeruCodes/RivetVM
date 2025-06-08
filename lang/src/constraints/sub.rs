use std::collections::HashMap;

use crate::{
    constraints::{lang_operand_to_air_expression, AirExpression, ResolveConstraint, RowOffset},
    ConstraintSystemVariable, Operand, StructuredAirConstraint,
};

#[derive(Debug, Clone)]
pub struct Sub {
    pub operand1: Operand,
    pub operand2: Operand,
    pub result: ConstraintSystemVariable,
    pub block_name: String,
}

impl ResolveConstraint for Sub {
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

        let op1_minus_op2_expr = AirExpression::Sub(Box::new(op1_expr), Box::new(op2_expr));
        let final_expr = AirExpression::Sub(Box::new(res_expr), Box::new(op1_minus_op2_expr));
        constraints.push(final_expr);
    }
}

use std::collections::HashMap;

use crate::{
    constraints::{lang_operand_to_air_expression, AirExpression, ResolveConstraint, RowOffset},
    ctx::AirGenContext,
    ConstraintSystemVariable, Operand, StructuredAirConstraint,
};

#[derive(Debug, Clone)]
pub struct ReturnAddress {
    pub operand1: Operand,
    pub operand2: Operand,
    pub result: ConstraintSystemVariable,
    pub block_name: String,
}

impl ResolveConstraint for ReturnAddress {
    fn resolve(
        &self,
        constraints: &mut Vec<AirExpression>,
        ctx: &mut AirGenContext,
        phi_condition_map: &HashMap<(String, String), ConstraintSystemVariable>,
        switch_instructions: &Vec<StructuredAirConstraint>,
    ) {
        let operand1_expr = lang_operand_to_air_expression(self.operand1);
        let operand2_expr = lang_operand_to_air_expression(self.operand2);
        let result_expr =
            AirExpression::Trace(super::AirTraceVariable(self.result.0), RowOffset::Current);

        constraints.push((operand1_expr + operand2_expr) - result_expr);
    }
}

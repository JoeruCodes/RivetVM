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
        let cond_expr = lang_operand_to_air_expression(self.condition);
        let true_val_expr = lang_operand_to_air_expression(self.true_value);
        let false_val_expr = lang_operand_to_air_expression(self.false_value);
        let res_expr =
            AirExpression::Trace(super::AirTraceVariable(self.result.0), RowOffset::Current);

        let term1 = AirExpression::Mul(Box::new(cond_expr.clone()), Box::new(true_val_expr));

        let one_minus_cond =
            AirExpression::Sub(Box::new(AirExpression::Constant(1)), Box::new(cond_expr));
        let term2 = AirExpression::Mul(Box::new(one_minus_cond), Box::new(false_val_expr));

        let selected_value_expr = AirExpression::Add(Box::new(term1), Box::new(term2));

        let final_expr = AirExpression::Sub(Box::new(selected_value_expr), Box::new(res_expr));
        constraints.push(final_expr);
    }
}

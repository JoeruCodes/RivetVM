use std::collections::HashMap;

use crate::{
    constraints::{lang_operand_to_air_expression, AirExpression, ResolveConstraint, RowOffset},
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
        let base_expr = lang_operand_to_air_expression(self.base);
        let index_expr = lang_operand_to_air_expression(self.index);
        let res_expr =
            AirExpression::Trace(super::AirTraceVariable(self.result.0), RowOffset::Current);

        let size_expr = AirExpression::Constant(self.element_size_bytes as u128);

        let offset_expr = AirExpression::Mul(Box::new(index_expr), Box::new(size_expr));

        let addr_expr = AirExpression::Add(Box::new(base_expr), Box::new(offset_expr));

        constraints.push(AirExpression::Sub(Box::new(res_expr), Box::new(addr_expr)));
    }
}

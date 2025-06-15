use std::collections::HashMap;

use crate::{
    constraints::{lang_operand_to_air_expression, AirExpression, ResolveConstraint},
    ConstraintSystemVariable, Operand, StructuredAirConstraint,
};

#[derive(Debug, Clone)]
pub struct Assign {
    pub dest: ConstraintSystemVariable,
    pub src: Operand,
    pub block_name: String,
}

impl ResolveConstraint for Assign {
    fn resolve(
        &self,
        constraints: &mut Vec<super::AirExpression>,
        _ctx: &mut crate::ctx::AirGenContext,
        _phi_condition_map: &HashMap<(String, String), ConstraintSystemVariable>,
        _switch_instructions: &Vec<StructuredAirConstraint>,
    ) {
        let dest_expr = AirExpression::Trace(
            super::AirTraceVariable(self.dest.0),
            super::RowOffset::Current,
        );
        let src_expr = lang_operand_to_air_expression(self.src);
        let final_expr = AirExpression::Sub(Box::new(dest_expr), Box::new(src_expr));
        constraints.push(final_expr);
    }
}

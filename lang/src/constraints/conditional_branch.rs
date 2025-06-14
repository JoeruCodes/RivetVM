use std::collections::HashMap;

use crate::{
    constraints::{lang_operand_to_air_expression, ResolveConstraint},
    ctx::AirGenContext,
    ConstraintSystemVariable, StructuredAirConstraint,
};

use super::AirExpression;

#[derive(Debug, Clone)]
pub struct ConditionalBranch {
    pub condition: ConstraintSystemVariable,
    pub true_block_name: String,
    pub false_block_name: String,
    pub block_name: String,
}

impl ResolveConstraint for ConditionalBranch {
    fn resolve(
        &self,
        _constraints: &mut Vec<AirExpression>,
        ctx: &mut AirGenContext,
        _phi_condition_map: &HashMap<(String, String), ConstraintSystemVariable>,
        _switch_instructions: &Vec<StructuredAirConstraint>,
    ) {
        ctx.set_conditional_next_block(
            self.condition,
            self.true_block_name.clone(),
            self.false_block_name.clone(),
        );
    }
}

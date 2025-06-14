use std::collections::HashMap;

use crate::{
    constraints::ResolveConstraint, ctx::AirGenContext, ConstraintSystemVariable, Operand,
    StructuredAirConstraint,
};

use super::AirExpression;

#[derive(Debug, Clone)]
pub struct Switch {
    pub condition_operand: Operand,
    pub default_target_block_name: String,
    pub cases: Vec<(Operand, String)>,
    pub block_name: String,
}

impl ResolveConstraint for Switch {
    fn resolve(
        &self,
        _constraints: &mut Vec<AirExpression>,
        ctx: &mut AirGenContext,
        _phi_condition_map: &HashMap<(String, String), ConstraintSystemVariable>,
        _switch_instructions: &Vec<StructuredAirConstraint>,
    ) {
        ctx.set_switch_next_block(
            self.condition_operand,
            self.default_target_block_name.clone(),
            self.cases.clone(),
        );
    }
}

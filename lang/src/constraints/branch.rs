use std::collections::HashMap;

use crate::{
    constraints::ResolveConstraint, ctx::AirGenContext, ConstraintSystemVariable,
    StructuredAirConstraint,
};

use super::AirExpression;

#[derive(Debug, Clone)]
pub struct Branch {
    pub target_block_name: String,
    pub block_name: String,
}

impl ResolveConstraint for Branch {
    fn resolve(
        &self,
        _constraints: &mut Vec<AirExpression>,
        ctx: &mut AirGenContext,
        _phi_condition_map: &HashMap<(String, String), ConstraintSystemVariable>,
        _switch_instructions: &Vec<StructuredAirConstraint>,
    ) {
        ctx.set_next_block(Some(self.target_block_name.clone()));
    }
}

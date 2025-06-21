use std::collections::HashMap;

use crate::{
    constraints::{AirExpression, ResolveConstraint, RowOffset},
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
        ctx: &mut crate::ctx::AirGenContext,
        _phi_condition_map: &HashMap<(String, String), ConstraintSystemVariable>,
        _switch_instructions: &Vec<StructuredAirConstraint>,
    ) {
        let dest_col = ctx.new_aux_variable();
        ctx.bind_ssa_var(self.dest, dest_col.0);
        let dest_expr =
            AirExpression::Trace(super::AirTraceVariable(dest_col.0), RowOffset::Current);
        let src_expr = ctx.expr_for_operand(self.src);
        let final_expr = AirExpression::Sub(Box::new(dest_expr), Box::new(src_expr));
        constraints.push(final_expr);
    }
}

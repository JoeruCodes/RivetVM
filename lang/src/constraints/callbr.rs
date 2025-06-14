use crate::{
    constraints::{call_stack::CallFrame, ResolveConstraint},
    ctx::AirGenContext,
    ConstraintSystemVariable, Operand, StructuredAirConstraint,
};
use std::collections::HashMap;

use super::AirExpression;

#[derive(Debug, Clone)]
pub struct CallBr {
    pub function_name: String,
    pub args: Vec<Operand>,
    pub result: Option<ConstraintSystemVariable>,
    pub fallthrough_block_name: String,
    pub other_block_names: Vec<String>,
    pub block_name: String,
    pub time_step: ConstraintSystemVariable,
}

impl ResolveConstraint for CallBr {
    fn resolve(
        &self,
        _constraints: &mut Vec<AirExpression>,
        ctx: &mut AirGenContext,
        _phi_condition_map: &HashMap<(String, String), ConstraintSystemVariable>,
        _switch_instructions: &Vec<StructuredAirConstraint>,
    ) {
        let mut param_to_arg_map = HashMap::new();
        let function_data = ctx
            .functions
            .get(&self.function_name)
            .expect("Function not found in AirGenContext");

        for (param_var, arg_op) in function_data.parameters.iter().zip(self.args.iter()) {
            param_to_arg_map.insert(*param_var, *arg_op);
        }

        let return_to_block = self.fallthrough_block_name.clone();

        let frame = CallFrame {
            function_name: self.function_name.clone(),
            return_to_block,
            param_to_arg_map,
            return_value_dest: self.result,
        };

        ctx.call_stack.push(frame);

        let target_block_name = function_data
            .entry_block
            .clone()
            .expect("Function must have an entry block.");
        ctx.set_next_block(Some(target_block_name));
    }
}

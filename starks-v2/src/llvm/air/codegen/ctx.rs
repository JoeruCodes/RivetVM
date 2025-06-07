use crate::llvm::air::types::{AirExpression, AirTraceVariable, RowOffset};

pub struct AirGenContext {
    pub next_available_trace_col: usize,
    internal_constraints: Vec<AirExpression>,
}

impl AirGenContext {
    pub fn new(initial_max_var_id: usize) -> Self {
        AirGenContext {
            next_available_trace_col: initial_max_var_id + 1,
            internal_constraints: Vec::new(),
        }
    }

    pub fn new_aux_variable(&mut self) -> AirTraceVariable {
        let var = AirTraceVariable(self.next_available_trace_col);
        self.next_available_trace_col += 1;
        var
    }

    pub fn add_unsigned_range_proof_constraints(
        &mut self,
        var_expr: AirExpression,
        bitwidth: u32,
    ) -> Vec<AirTraceVariable> {
        let mut bit_vars = Vec::with_capacity(bitwidth as usize);
        let mut sum_of_bit_terms = AirExpression::Constant(0);

        for i in 0..bitwidth {
            let bit_var = self.new_aux_variable();
            bit_vars.push(bit_var);
            let bit_var_expr = AirExpression::Trace(bit_var, RowOffset::Current);

            self.internal_constraints.push(AirExpression::Mul(
                Box::new(bit_var_expr.clone()),
                Box::new(AirExpression::Sub(
                    Box::new(bit_var_expr.clone()),
                    Box::new(AirExpression::Constant(1)),
                )),
            ));

            sum_of_bit_terms = AirExpression::Add(
                Box::new(sum_of_bit_terms),
                Box::new(AirExpression::Mul(
                    Box::new(bit_var_expr.clone()),
                    Box::new(AirExpression::Constant(1u128 << i)),
                )),
            );
        }

        self.internal_constraints.push(AirExpression::Sub(
            Box::new(var_expr),
            Box::new(sum_of_bit_terms),
        ));

        bit_vars
    }

    pub fn add_signed_range_proof_constraints(
        &mut self,
        var_expr: AirExpression,
        bitwidth: u32,
    ) -> Vec<AirTraceVariable> {
        if bitwidth == 0 {
            return Vec::new();
        }
        if bitwidth == 1 {
            let one = AirExpression::Constant(1);
            let shifted_var = AirExpression::Add(Box::new(var_expr.clone()), Box::new(one));

            return self.add_unsigned_range_proof_constraints(shifted_var, 1);
        }

        let offset_val = 1u128 << (bitwidth - 1);
        let offset_expr = AirExpression::Constant(offset_val);
        let shifted_var_expr = AirExpression::Add(Box::new(var_expr), Box::new(offset_expr));

        self.add_unsigned_range_proof_constraints(shifted_var_expr, bitwidth)
    }

    pub fn drain_internal_constraints(&mut self) -> Vec<AirExpression> {
        std::mem::take(&mut self.internal_constraints)
    }
}

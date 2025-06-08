use crate::constraints::{AirExpression, AirTraceVariable, RowOffset};

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
    ) -> (Vec<AirExpression>, Option<AirExpression>) {
        self.generate_signed_range_proof_constraints(&var_expr, bitwidth, "signed_range_proof")
    }

    fn generate_signed_range_proof_constraints(
        &mut self,
        x_signed_expr: &AirExpression,
        bitwidth: u32,
        var_name: &str,
    ) -> (Vec<AirExpression>, Option<AirExpression>) {
        if bitwidth == 0 {
            println!(
                "    SDIV Range Proof for {}: bitwidth is 0, skipping.",
                var_name
            );
            return (Vec::new(), None);
        }
        println!(
            "    SDIV: Generating signed {}-bit range proof for {}",
            bitwidth, var_name
        );

        let pow_2_k_minus_1 = 1u128 << (bitwidth - 1);
        let x_unsigned_offset_val = AirExpression::Constant(pow_2_k_minus_1);

        let x_unsigned_expr = AirExpression::Add(
            Box::new(x_signed_expr.clone()),
            Box::new(x_unsigned_offset_val),
        );
        println!(
            "      {}_unsigned = {} + 2^({}-1) = {:?}",
            var_name, var_name, bitwidth, x_unsigned_expr
        );

        let mut bit_vars_exprs = Vec::new();
        let mut sum_terms = Vec::new();

        for i in 0..bitwidth {
            let bit_aux_var = self.new_aux_variable();
            let bit_expr = AirExpression::Trace(bit_aux_var, RowOffset::Current);

            let bit_minus_one = AirExpression::Sub(
                Box::new(bit_expr.clone()),
                Box::new(AirExpression::Constant(1)),
            );
            self.internal_constraints.push(AirExpression::Mul(
                Box::new(bit_expr.clone()),
                Box::new(bit_minus_one),
            ));
            bit_vars_exprs.push(bit_expr.clone());

            let power_of_2 = 1u128 << i;
            sum_terms.push(AirExpression::Mul(
                Box::new(bit_expr.clone()),
                Box::new(AirExpression::Constant(power_of_2)),
            ));
            println!(
                "        {}_bit_{} (trace col {}) created for {}. Booleanity added.",
                var_name, i, bit_aux_var.0, var_name
            );
        }

        let sum_from_bits = sum_terms
            .into_iter()
            .reduce(|acc, term| AirExpression::Add(Box::new(acc), Box::new(term)))
            .unwrap_or_else(|| AirExpression::Constant(0));

        self.internal_constraints.push(AirExpression::Sub(
            Box::new(x_unsigned_expr),
            Box::new(sum_from_bits),
        ));
        println!(
            "      {}_unsigned decomposition constraint added for {}.
    ",
            var_name, var_name
        );

        let msb_expr_opt = bit_vars_exprs.last().cloned();
        (bit_vars_exprs, msb_expr_opt)
    }

    pub fn drain_internal_constraints(&mut self) -> Vec<AirExpression> {
        std::mem::take(&mut self.internal_constraints)
    }
}

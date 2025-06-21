use crate::{
    constraints::{
        lang_operand_to_air_expression, AirExpression, AirTraceVariable, ResolveConstraint,
        RowOffset,
    },
    ConstraintSystemVariable, Operand,
};

#[derive(Debug, Clone)]
pub struct Trunc {
    pub operand: Operand,
    pub result: ConstraintSystemVariable,
    pub block_name: String,
    pub operand_bitwidth: u32,
    pub result_bitwidth: u32,
}

impl ResolveConstraint for Trunc {
    fn resolve(
        &self,
        constraints: &mut Vec<super::AirExpression>,
        ctx: &mut crate::ctx::AirGenContext,
        phi_condition_map: &std::collections::HashMap<(String, String), ConstraintSystemVariable>,
        switch_instructions: &Vec<crate::StructuredAirConstraint>,
    ) {
        println!(
            "  TRUNC: op={:?}, res={:?} ({}->{} bits)",
            self.operand, self.result, self.operand_bitwidth, self.result_bitwidth
        );

        let op_expr = ctx.expr_for_operand(self.operand);

        let reg_col_opt = ctx.col_for_ssa(self.result);

        let dest_col = ctx.new_aux_variable();
        ctx.bind_ssa_var(self.result, dest_col.0);
        let res_expr = AirExpression::Trace(dest_col, RowOffset::Current);
        let upper_bits_bitwidth = self.operand_bitwidth - self.result_bitwidth;

        let upper_bits_vars = (0..upper_bits_bitwidth)
            .map(|_| {
                let bit_var = ctx.new_aux_variable();
                let bit_expr = AirExpression::Trace(bit_var.clone(), RowOffset::Current);

                let bit_constraint = AirExpression::Mul(
                    Box::new(bit_expr.clone()),
                    Box::new(AirExpression::Sub(
                        Box::new(bit_expr),
                        Box::new(AirExpression::Constant(1)),
                    )),
                );
                constraints.push(bit_constraint);
                bit_var
            })
            .collect::<Vec<_>>();

        let mut upper_bits_expr = AirExpression::Constant(0);
        for (i, bit_var) in upper_bits_vars.iter().enumerate() {
            let bit_expr = AirExpression::Trace(bit_var.clone(), RowOffset::Current);
            let bit_shift = AirExpression::Constant(1u128 << i);
            let bit_term = AirExpression::Mul(Box::new(bit_expr), Box::new(bit_shift));
            upper_bits_expr = AirExpression::Add(Box::new(upper_bits_expr), Box::new(bit_term));
        }

        let upper_bits_shift = AirExpression::Constant(1u128 << self.result_bitwidth);
        let upper_bits_term =
            AirExpression::Mul(Box::new(upper_bits_expr), Box::new(upper_bits_shift));
        let trunc_expr = AirExpression::Add(Box::new(res_expr), Box::new(upper_bits_term));
        let final_expr = AirExpression::Sub(Box::new(op_expr), Box::new(trunc_expr));
        constraints.push(final_expr);
        println!("      TRUNC: Main constraint added.");

        if let Some(reg_col) = reg_col_opt {
            let sel = ctx.new_row_selector();
            let reg_expr = AirExpression::Trace(AirTraceVariable(reg_col), RowOffset::Current);
            let res_again = AirExpression::Trace(dest_col.clone(), RowOffset::Current);
            let diff = AirExpression::Sub(Box::new(res_again), Box::new(reg_expr));
            ctx.add_row_gated_constraint(sel, diff);
        }
    }
}

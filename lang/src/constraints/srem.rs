use crate::{
    constraints::{
        lang_operand_to_air_expression, AirExpression, AirTraceVariable, ResolveConstraint,
        RowOffset,
    },
    ConstraintSystemVariable, Operand,
};

#[derive(Debug, Clone)]
pub struct SRem {
    pub operand1: Operand,
    pub operand2: Operand,
    pub result: ConstraintSystemVariable,
    pub block_name: String,
    pub operand_bitwidth: u32,
}

impl ResolveConstraint for SRem {
    fn resolve(
        &self,
        constraints: &mut Vec<super::AirExpression>,
        ctx: &mut crate::ctx::AirGenContext,
        phi_condition_map: &std::collections::HashMap<(String, String), ConstraintSystemVariable>,
        switch_instructions: &Vec<crate::StructuredAirConstraint>,
    ) {
        let a_expr = ctx.expr_for_operand(self.operand1);
        let b_expr = ctx.expr_for_operand(self.operand2);

        let reg_col_opt = ctx.col_for_ssa(self.result);
        let dest_col = ctx.new_aux_variable();
        ctx.bind_ssa_var(self.result, dest_col.0);
        let r_expr = AirExpression::Trace(dest_col, RowOffset::Current);

        let q_aux_var = ctx.new_aux_variable();
        let q_expr = AirExpression::Trace(q_aux_var, RowOffset::Current);
        println!(
                "  SREM: dividend(a)={:?}, divisor(b)={:?}, remainder(r)={:?}, quotient_aux(q)={:?} (bitwidth {})",
                self.operand1, self.operand2, self.result, q_aux_var, self.operand_bitwidth
            );

        let (_a_bits, a_msb_expr_opt) =
            ctx.add_signed_range_proof_constraints(a_expr.clone(), self.operand_bitwidth);
        let (_b_bits, b_msb_expr_opt) =
            ctx.add_signed_range_proof_constraints(b_expr.clone(), self.operand_bitwidth);
        let (_q_bits, _q_msb_expr_opt) =
            ctx.add_signed_range_proof_constraints(q_expr.clone(), self.operand_bitwidth);
        let (_r_bits, r_msb_expr_opt) =
            ctx.add_signed_range_proof_constraints(r_expr.clone(), self.operand_bitwidth);

        let q_times_b = AirExpression::Mul(Box::new(q_expr.clone()), Box::new(b_expr.clone()));
        let qb_plus_r = AirExpression::Add(Box::new(q_times_b), Box::new(r_expr.clone()));
        constraints.push(AirExpression::Sub(
            Box::new(a_expr.clone()),
            Box::new(qb_plus_r),
        ));
        println!("    SREM: Constraint a-(q*b+r)=0 added.");

        let is_a_zero_aux = ctx.new_aux_variable();
        let is_a_zero_expr = AirExpression::Trace(is_a_zero_aux, RowOffset::Current);
        constraints.push(AirExpression::Mul(
            Box::new(is_a_zero_expr.clone()),
            Box::new(AirExpression::Sub(
                Box::new(is_a_zero_expr.clone()),
                Box::new(AirExpression::Constant(1)),
            )),
        ));
        constraints.push(AirExpression::Mul(
            Box::new(is_a_zero_expr.clone()),
            Box::new(a_expr.clone()),
        ));

        if let (Some(a_msb_expr_val), Some(r_msb_expr_val)) =
            (a_msb_expr_opt.as_ref(), r_msb_expr_opt.as_ref())
        {
            let one_minus_is_a_zero = AirExpression::Sub(
                Box::new(AirExpression::Constant(1)),
                Box::new(is_a_zero_expr.clone()),
            );
            let a_msb_minus_r_msb = AirExpression::Sub(
                Box::new(a_msb_expr_val.clone()),
                Box::new(r_msb_expr_val.clone()),
            );
            constraints.push(AirExpression::Mul(
                Box::new(one_minus_is_a_zero),
                Box::new(a_msb_minus_r_msb),
            ));
            constraints.push(AirExpression::Mul(
                Box::new(is_a_zero_expr.clone()),
                Box::new(r_expr.clone()),
            ));
            println!("    SREM: Remainder sign constraints added.");
        } else {
            println!("    SREM: WARN - MSBs for a or r not available for sign constraint.");
        }

        if let (Some(r_msb_expr_val_mag), Some(b_msb_expr_val_mag)) =
            (r_msb_expr_opt.as_ref(), b_msb_expr_opt.as_ref())
        {
            let one_const = AirExpression::Constant(1);
            let two_const = AirExpression::Constant(2);

            let one_minus_two_r_msb = AirExpression::Sub(
                Box::new(one_const.clone()),
                Box::new(AirExpression::Mul(
                    Box::new(two_const.clone()),
                    Box::new(r_msb_expr_val_mag.clone()),
                )),
            );
            let abs_r_expr =
                AirExpression::Mul(Box::new(r_expr.clone()), Box::new(one_minus_two_r_msb));

            let one_minus_two_b_msb = AirExpression::Sub(
                Box::new(one_const.clone()),
                Box::new(AirExpression::Mul(
                    Box::new(two_const.clone()),
                    Box::new(b_msb_expr_val_mag.clone()),
                )),
            );
            let abs_b_expr =
                AirExpression::Mul(Box::new(b_expr.clone()), Box::new(one_minus_two_b_msb));

            let ult_res_abs_r_lt_abs_b_var = ctx.new_aux_variable();
            let ult_res_abs_r_lt_abs_b_expr =
                AirExpression::Trace(ult_res_abs_r_lt_abs_b_var, RowOffset::Current);

            constraints.push(AirExpression::Mul(
                Box::new(ult_res_abs_r_lt_abs_b_expr.clone()),
                Box::new(AirExpression::Sub(
                    Box::new(ult_res_abs_r_lt_abs_b_expr.clone()),
                    Box::new(AirExpression::Constant(1)),
                )),
            ));
            constraints.push(AirExpression::Sub(
                Box::new(ult_res_abs_r_lt_abs_b_expr.clone()),
                Box::new(AirExpression::Constant(1)),
            ));

            let mut d_sum_bit_vars_ult_mag = Vec::new();
            if self.operand_bitwidth > 0 {
                for _ in 0..self.operand_bitwidth {
                    let bit_aux_var = ctx.new_aux_variable();
                    let bit_expr_d = AirExpression::Trace(bit_aux_var, RowOffset::Current);
                    constraints.push(AirExpression::Mul(
                        Box::new(bit_expr_d.clone()),
                        Box::new(AirExpression::Sub(
                            Box::new(bit_expr_d.clone()),
                            Box::new(AirExpression::Constant(1)),
                        )),
                    ));
                    d_sum_bit_vars_ult_mag.push(bit_expr_d);
                }
            }
            let d_sum_air_ult_mag = d_sum_bit_vars_ult_mag.iter().enumerate().fold(
                AirExpression::Constant(0),
                |acc, (i, bit_e)| {
                    AirExpression::Add(
                        Box::new(acc),
                        Box::new(AirExpression::Mul(
                            Box::new(bit_e.clone()),
                            Box::new(AirExpression::Constant(1u128 << i)),
                        )),
                    )
                },
            );

            let b_abs_minus_a_abs_minus_1 = AirExpression::Sub(
                Box::new(AirExpression::Sub(
                    Box::new(abs_b_expr.clone()),
                    Box::new(abs_r_expr.clone()),
                )),
                Box::new(AirExpression::Constant(1)),
            );
            let ult_final_constraint = AirExpression::Sub(
                Box::new(b_abs_minus_a_abs_minus_1),
                Box::new(d_sum_air_ult_mag.clone()),
            );
            constraints.push(ult_final_constraint);
            println!("    SREM: Remainder magnitude constraints added.");
        } else {
            println!("    SREM: WARN - MSBs for r or b not available for magnitude constraint.");
        }

        if let Some(reg_col) = reg_col_opt {
            let selector_expr = ctx.new_row_selector();
            let reg_expr = AirExpression::Trace(AirTraceVariable(reg_col), RowOffset::Current);
            let eq_expr = AirExpression::Sub(Box::new(r_expr.clone()), Box::new(reg_expr));
            ctx.add_row_gated_constraint(selector_expr, eq_expr);
        }
    }
}

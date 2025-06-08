use std::collections::HashMap;

use crate::{
    constraints::{
        lang_operand_to_air_expression, AirExpression, AirTraceVariable, ResolveConstraint,
        RowOffset,
    },
    ConstraintSystemVariable, Operand, StructuredAirConstraint,
};

#[derive(Debug, Clone)]
pub struct Shr {
    pub operand1: Operand,
    pub operand2: Operand,
    pub result: ConstraintSystemVariable,
    pub block_name: String,
    pub operand_bitwidth: u32,
}

impl ResolveConstraint for Shr {
    fn resolve(
        &self,
        constraints: &mut Vec<super::AirExpression>,
        ctx: &mut crate::ctx::AirGenContext,
        phi_condition_map: &HashMap<(String, String), ConstraintSystemVariable>,
        switch_instructions: &Vec<StructuredAirConstraint>,
    ) {
        let op1_expr = lang_operand_to_air_expression(self.operand1);
        let op2_expr = lang_operand_to_air_expression(self.operand2);
        let res_expr = AirExpression::Trace(AirTraceVariable(self.result.0), RowOffset::Current);

        let rem_aux_var = ctx.new_aux_variable();
        let rem_expr = AirExpression::Trace(rem_aux_var, RowOffset::Current);
        println!(
            "  SHR: op1={:?}, op2={:?}, res={:?}, rem_aux_var={:?}, operand_bitwidth={}",
            op1_expr, op2_expr, res_expr, rem_aux_var, self.operand_bitwidth
        );

        let mut rem_bit_sum_terms = Vec::new();
        println!(
            "    SHR: Decomposing remainder rem_expr ({:?}) into {} bits",
            rem_expr, self.operand_bitwidth
        );
        for i in 0..self.operand_bitwidth {
            let bit_aux = ctx.new_aux_variable();
            let bit_expr = AirExpression::Trace(bit_aux, RowOffset::Current);
            constraints.push(AirExpression::Mul(
                Box::new(bit_expr.clone()),
                Box::new(AirExpression::Sub(
                    Box::new(bit_expr.clone()),
                    Box::new(AirExpression::Constant(1)),
                )),
            ));
            rem_bit_sum_terms.push(AirExpression::Mul(
                Box::new(bit_expr.clone()),
                Box::new(AirExpression::Constant(1u128 << i)),
            ));
            println!(
                "      rem_bit_{} (trace col {}) created for remainder decomposition",
                i, bit_aux.0
            );
        }
        let rem_reconstructed = rem_bit_sum_terms
            .into_iter()
            .reduce(|acc, term| AirExpression::Add(Box::new(acc), Box::new(term)))
            .unwrap_or_else(|| AirExpression::Constant(0));
        constraints.push(AirExpression::Sub(
            Box::new(rem_expr.clone()),
            Box::new(rem_reconstructed),
        ));
        println!("    SHR: Remainder rem_expr decomposition constraint added.");

        if let AirExpression::Constant(s_const_val) = op2_expr {
            if s_const_val >= self.operand_bitwidth.into() {
                constraints.push(res_expr.clone());

                constraints.push(AirExpression::Sub(
                    Box::new(rem_expr.clone()),
                    Box::new(op1_expr.clone()),
                ));
                println!(
                    "    SHR: op2 is const {} >= bitwidth {}. res=0, rem=op1.",
                    s_const_val, self.operand_bitwidth
                );
            } else {
                let power_of_2_s_val = 1u128.wrapping_shl(s_const_val as u32);
                let power_of_2_s_expr = AirExpression::Constant(power_of_2_s_val);

                let res_times_power_of_2 = AirExpression::Mul(
                    Box::new(res_expr.clone()),
                    Box::new(power_of_2_s_expr.clone()),
                );
                let res_term_plus_rem =
                    AirExpression::Add(Box::new(res_times_power_of_2), Box::new(rem_expr.clone()));
                constraints.push(AirExpression::Sub(
                    Box::new(op1_expr.clone()),
                    Box::new(res_term_plus_rem),
                ));
                println!(
                    "    SHR: op2 is const {}. Algebraic constraint op1 - (res*2^{} + rem) = 0 added.",
                    s_const_val, s_const_val
                );
            }
        } else {
            println!("    SHR: op2 is variable: {:?}", op2_expr);
            let num_shift_bits = if self.operand_bitwidth == 1 {
                1
            } else {
                (self.operand_bitwidth - 1).ilog2() + 1
            };

            let mut s_bit_exprs = Vec::new();
            let mut op2_sum_terms_recon = Vec::new();
            for i in 0..num_shift_bits {
                let bit_aux_var = ctx.new_aux_variable();
                let bit_expr = AirExpression::Trace(bit_aux_var, RowOffset::Current);
                constraints.push(AirExpression::Mul(
                    Box::new(bit_expr.clone()),
                    Box::new(AirExpression::Sub(
                        Box::new(bit_expr.clone()),
                        Box::new(AirExpression::Constant(1)),
                    )),
                ));
                s_bit_exprs.push(bit_expr.clone());
                op2_sum_terms_recon.push(AirExpression::Mul(
                    Box::new(bit_expr.clone()),
                    Box::new(AirExpression::Constant(1u128 << i)),
                ));
            }
            let op2_reconstructed_expr = op2_sum_terms_recon
                .into_iter()
                .reduce(|acc, term| AirExpression::Add(Box::new(acc), Box::new(term)))
                .unwrap_or_else(|| AirExpression::Constant(0));
            constraints.push(AirExpression::Sub(
                Box::new(op2_expr.clone()),
                Box::new(op2_reconstructed_expr),
            ));

            let mut factor_exprs_for_prod = Vec::new();
            println!("      SHR: (Variable s) Calculating factors for 2^s term...");
            for i in 0..num_shift_bits {
                let s_i_expr = &s_bit_exprs[i as usize];
                let exp_base_power = 1u128 << i;
                let exp_val_i = if exp_base_power >= 128 {
                    0
                } else {
                    1u128.wrapping_shl(exp_base_power as u32)
                };

                let factor_i_aux_var = ctx.new_aux_variable();
                let factor_i_expr_aux = AirExpression::Trace(factor_i_aux_var, RowOffset::Current);
                let exp_val_i_minus_1 = exp_val_i.saturating_sub(1);
                let term_mul_factor = AirExpression::Mul(
                    Box::new(s_i_expr.clone()),
                    Box::new(AirExpression::Constant(exp_val_i_minus_1)),
                );
                let term_sum_factor = AirExpression::Add(
                    Box::new(term_mul_factor),
                    Box::new(AirExpression::Constant(1)),
                );
                constraints.push(AirExpression::Sub(
                    Box::new(factor_i_expr_aux.clone()),
                    Box::new(term_sum_factor),
                ));
                factor_exprs_for_prod.push(factor_i_expr_aux.clone());
                println!(
                    "        factor_s_{} (trace col {}) for s_{} (using exp_val_i=2^(2^{})={}) created.",
                    i, factor_i_aux_var.0, i, i, exp_val_i
                );
            }

            let mut final_power_of_2_op2_expr = AirExpression::Constant(1);
            if !factor_exprs_for_prod.is_empty() {
                final_power_of_2_op2_expr = factor_exprs_for_prod[0].clone();
                println!(
                    "      SHR: (Variable s) Product for 2^s: init with factor_0 ({:?})",
                    final_power_of_2_op2_expr
                );
                for i in 1..factor_exprs_for_prod.len() {
                    let prev_product_expr_val = final_power_of_2_op2_expr.clone();
                    let factor_val_expr = &factor_exprs_for_prod[i];
                    let next_product_aux_var = ctx.new_aux_variable();
                    final_power_of_2_op2_expr =
                        AirExpression::Trace(next_product_aux_var, RowOffset::Current);
                    let product_term_step = AirExpression::Mul(
                        Box::new(prev_product_expr_val),
                        Box::new(factor_val_expr.clone()),
                    );
                    constraints.push(AirExpression::Sub(
                        Box::new(final_power_of_2_op2_expr.clone()),
                        Box::new(product_term_step),
                    ));
                    println!(
                        "        prod_step_s_{} (trace col {}): from prev_prod * factor_{}",
                        i, next_product_aux_var.0, i
                    );
                }
            }
            println!(
                "      SHR: (Variable s) final_power_of_2_op2_expr (2^s) = {:?}",
                final_power_of_2_op2_expr
            );

            let res_times_power_of_2 = AirExpression::Mul(
                Box::new(res_expr.clone()),
                Box::new(final_power_of_2_op2_expr.clone()),
            );
            let res_term_plus_rem =
                AirExpression::Add(Box::new(res_times_power_of_2), Box::new(rem_expr.clone()));
            constraints.push(AirExpression::Sub(
                Box::new(op1_expr.clone()),
                Box::new(res_term_plus_rem),
            ));
            println!(
                "    SHR: op2 is variable. Algebraic constraint op1 - (res*2^s + rem) = 0 added."
            );

            let ult_rem_lt_pow2s_res_var = ctx.new_aux_variable();
            let ult_rem_lt_pow2s_res_expr =
                AirExpression::Trace(ult_rem_lt_pow2s_res_var, RowOffset::Current);
            println!(
                "    SHR: ult_rem_lt_pow2s_res_var for (rem < 2^s) is {:?} (trace col {})",
                ult_rem_lt_pow2s_res_var, ult_rem_lt_pow2s_res_var.0
            );

            constraints.push(AirExpression::Mul(
                Box::new(ult_rem_lt_pow2s_res_expr.clone()),
                Box::new(AirExpression::Sub(
                    Box::new(ult_rem_lt_pow2s_res_expr.clone()),
                    Box::new(AirExpression::Constant(1)),
                )),
            ));
            constraints.push(AirExpression::Sub(
                Box::new(ult_rem_lt_pow2s_res_expr.clone()),
                Box::new(AirExpression::Constant(1)),
            ));
            println!(
                "    SHR: Booleanity and assertion (must be 1) for ult_rem_lt_pow2s_res_expr added."
            );

            let mut pow2s_bit_exprs = Vec::new();
            let mut pow2s_sum_terms = Vec::new();
            println!(
                "    SHR: Decomposing finals_power_of_2_op2_expr ({:?}) into {} bits for ULT",
                final_power_of_2_op2_expr, self.operand_bitwidth
            );
            for i in 0..self.operand_bitwidth {
                let bit_aux = ctx.new_aux_variable();
                let bit_expr = AirExpression::Trace(bit_aux, RowOffset::Current);
                constraints.push(AirExpression::Mul(
                    Box::new(bit_expr.clone()),
                    Box::new(AirExpression::Sub(
                        Box::new(bit_expr.clone()),
                        Box::new(AirExpression::Constant(1)),
                    )),
                ));
                pow2s_bit_exprs.push(bit_expr.clone());
                pow2s_sum_terms.push(AirExpression::Mul(
                    Box::new(bit_expr.clone()),
                    Box::new(AirExpression::Constant(1u128 << i)),
                ));
                println!(
                    "      pow2s_bit_{} (trace col {}) created for ULT decomposition",
                    i, bit_aux.0
                );
            }
            let pow2s_reconstructed = pow2s_sum_terms
                .into_iter()
                .reduce(|acc, term| AirExpression::Add(Box::new(acc), Box::new(term)))
                .unwrap_or_else(|| AirExpression::Constant(0));
            constraints.push(AirExpression::Sub(
                Box::new(final_power_of_2_op2_expr.clone()),
                Box::new(pow2s_reconstructed),
            ));
            println!("    SHR: final_power_of_2_op2_expr decomposition constraint added for ULT.");

            let mut d_sum_bit_vars_ult_rem_pow2s = Vec::new();
            println!(
                "    SHR: Decomposing for D_sum in ULT(rem, 2^s) ({} bits)",
                self.operand_bitwidth
            );
            for i in 0..self.operand_bitwidth {
                let bit_aux_var = ctx.new_aux_variable();
                let bit_expr_d = AirExpression::Trace(bit_aux_var, RowOffset::Current);
                constraints.push(AirExpression::Mul(
                    Box::new(bit_expr_d.clone()),
                    Box::new(AirExpression::Sub(
                        Box::new(bit_expr_d.clone()),
                        Box::new(AirExpression::Constant(1)),
                    )),
                ));
                d_sum_bit_vars_ult_rem_pow2s.push(bit_expr_d);
                println!(
                    "      ULT(rem, 2^s) D_sum bit_{} (trace col {}) created",
                    i, bit_aux_var.0
                );
            }
            let d_sum_air_ult_rem_pow2s = d_sum_bit_vars_ult_rem_pow2s.iter().enumerate().fold(
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
            println!(
                "    SHR: D_sum_air for ULT(rem, 2^s) constructed: {:?}",
                d_sum_air_ult_rem_pow2s
            );

            let b_minus_a_minus_1_ult = AirExpression::Sub(
                Box::new(AirExpression::Sub(
                    Box::new(final_power_of_2_op2_expr.clone()),
                    Box::new(rem_expr.clone()),
                )),
                Box::new(AirExpression::Constant(1)),
            );
            let term1_val_ult = AirExpression::Sub(
                Box::new(b_minus_a_minus_1_ult),
                Box::new(d_sum_air_ult_rem_pow2s.clone()),
            );
            constraints.push(AirExpression::Mul(
                Box::new(ult_rem_lt_pow2s_res_expr.clone()),
                Box::new(term1_val_ult),
            ));
            println!("    SHR: ULT(rem, 2^s) selector1 (res=1 path) constraint added.");

            let one_minus_ult_res = AirExpression::Sub(
                Box::new(AirExpression::Constant(1)),
                Box::new(ult_rem_lt_pow2s_res_expr.clone()),
            );
            let a_minus_b_ult = AirExpression::Sub(
                Box::new(rem_expr.clone()),
                Box::new(final_power_of_2_op2_expr.clone()),
            );
            let term2_val_ult = AirExpression::Sub(
                Box::new(a_minus_b_ult),
                Box::new(d_sum_air_ult_rem_pow2s.clone()),
            );
            constraints.push(AirExpression::Mul(
                Box::new(one_minus_ult_res),
                Box::new(term2_val_ult),
            ));
            println!("    SHR: ULT(rem, 2^s) selector2 (res=0 path) constraint added.");
        }
    }
}

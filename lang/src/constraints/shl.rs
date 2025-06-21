use std::collections::HashMap;

use crate::{
    constraints::{
        lang_operand_to_air_expression, AirExpression, AirTraceVariable, ResolveConstraint,
        RowOffset,
    },
    ConstraintSystemVariable, Operand, StructuredAirConstraint,
};

#[derive(Debug, Clone)]
pub struct Shl {
    pub operand1: Operand,
    pub operand2: Operand,
    pub result: ConstraintSystemVariable,
    pub block_name: String,
    pub operand_bitwidth: u32,
}

impl ResolveConstraint for Shl {
    fn resolve(
        &self,
        constraints: &mut Vec<super::AirExpression>,
        ctx: &mut crate::ctx::AirGenContext,
        phi_condition_map: &HashMap<(String, String), ConstraintSystemVariable>,
        switch_instructions: &Vec<StructuredAirConstraint>,
    ) {
        let op1_expr = ctx.expr_for_operand(self.operand1);
        let op2_expr = ctx.expr_for_operand(self.operand2);

        let reg_col_opt = ctx.col_for_ssa(self.result);

        let dest_col = ctx.new_aux_variable();
        ctx.bind_ssa_var(self.result, dest_col.0);
        let res_expr = AirExpression::Trace(dest_col, RowOffset::Current);
        println!(
            "  SHL: op1={:?}, op2={:?}, res={:?}, operand_bitwidth={}",
            op1_expr, op2_expr, res_expr, self.operand_bitwidth
        );

        if let AirExpression::Constant(s_const_val) = op2_expr {
            if s_const_val >= self.operand_bitwidth.into() {
                constraints.push(res_expr.clone());
                println!(
                    "    SHL: op2 is const {} >= bitwidth {}, result set to 0",
                    s_const_val, self.operand_bitwidth
                );
            } else {
                let power_of_2_s_val = 1u128.wrapping_shl(s_const_val as u32);
                let power_of_2_s_expr = AirExpression::Constant(power_of_2_s_val);
                let product =
                    AirExpression::Mul(Box::new(op1_expr.clone()), Box::new(power_of_2_s_expr));
                constraints.push(AirExpression::Sub(
                    Box::new(res_expr.clone()),
                    Box::new(product),
                ));
                println!(
                    "    SHL: op2 is const {}, 2^{} = {}, res = op1 * {}",
                    s_const_val, s_const_val, power_of_2_s_val, power_of_2_s_val
                );
            }
        } else {
            println!("    SHL: op2 is variable: {:?}", op2_expr);

            let num_shift_bits = if self.operand_bitwidth == 1 {
                1
            } else {
                (self.operand_bitwidth - 1).ilog2() + 1
            };
            println!("      SHL: num_shift_bits_for_op2 = {}", num_shift_bits);

            let mut s_bit_exprs = Vec::new();
            let mut op2_sum_terms_recon = Vec::new();
            println!(
                "      SHL: Decomposing op2_expr into {} bits...",
                num_shift_bits
            );
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

                let power_of_2_val = 1u128 << i;
                op2_sum_terms_recon.push(AirExpression::Mul(
                    Box::new(bit_expr.clone()),
                    Box::new(AirExpression::Constant(power_of_2_val)),
                ));
                println!(
                    "        s_bit_{} (trace col {}) created for op2 decomposition",
                    i, bit_aux_var.0
                );
            }

            let op2_reconstructed_expr = op2_sum_terms_recon
                .into_iter()
                .reduce(|acc, term| AirExpression::Add(Box::new(acc), Box::new(term)))
                .unwrap_or_else(|| AirExpression::Constant(0));

            constraints.push(AirExpression::Sub(
                Box::new(op2_expr.clone()),
                Box::new(op2_reconstructed_expr),
            ));
            println!("      SHL: op2 decomposition constraint added.");

            let mut factor_exprs_for_prod = Vec::new();
            println!("      SHL: Calculating factors for 2^op2 term...");
            for i in 0..num_shift_bits {
                let s_i_expr: &AirExpression = &s_bit_exprs[i as usize];

                let exp_base_power = 1u128 << i;

                let exp_val_i = if exp_base_power >= 128 {
                    0
                } else {
                    1u128.wrapping_shl(exp_base_power as u32)
                };
                if exp_base_power >= 128 && exp_val_i != 0 {
                    println!(
                        "        WARN: Large exp_base_power {} resulted in exp_val_i {}. This might be an issue.",
                        exp_base_power, exp_val_i
                    );
                }

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
                    "        factor_{} (trace col {}) for s_{} (using exp_val_i=2^(2^{})={}) created.",
                    i, factor_i_aux_var.0, i, i, exp_val_i
                );
            }

            let mut final_power_of_2_op2_expr = AirExpression::Constant(1);
            if !factor_exprs_for_prod.is_empty() {
                final_power_of_2_op2_expr = factor_exprs_for_prod[0].clone();
                println!(
                    "      SHL: Product for 2^op2: init with factor_0 ({:?})",
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
                        "        prod_step_{} (trace col {}): from prev_prod * factor_{}",
                        i, next_product_aux_var.0, i
                    );
                }
            }
            println!(
                "      SHL: final_power_of_2_op2_expr = {:?}",
                final_power_of_2_op2_expr
            );

            let main_prod_term = AirExpression::Mul(
                Box::new(op1_expr.clone()),
                Box::new(final_power_of_2_op2_expr.clone()),
            );
            constraints.push(AirExpression::Sub(
                Box::new(res_expr.clone()),
                Box::new(main_prod_term),
            ));
            println!("      SHL: Main constraint (res - op1 * 2^op2 = 0) added.");
        }

        if let Some(reg_col) = reg_col_opt {
            use crate::constraints::{AirExpression, AirTraceVariable};
            let selector_expr = ctx.new_row_selector();
            let reg_expr = AirExpression::Trace(AirTraceVariable(reg_col), RowOffset::Current);
            let eq_expr = AirExpression::Sub(Box::new(res_expr.clone()), Box::new(reg_expr));
            ctx.add_row_gated_constraint(selector_expr, eq_expr);
        }
    }
}

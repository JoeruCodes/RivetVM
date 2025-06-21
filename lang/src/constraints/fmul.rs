use crate::utils::*;
use crate::{
    constraints::{AirExpression, AirTraceVariable, ResolveConstraint, RowOffset},
    ConstraintSystemVariable, Operand,
};

#[derive(Debug, Clone)]
pub struct FMul {
    pub operand1: Operand,
    pub operand2: Operand,
    pub result: ConstraintSystemVariable,
    pub block_name: String,
    pub operand_bitwidth: u32,
}

impl ResolveConstraint for FMul {
    fn resolve(
        &self,
        constraints: &mut Vec<super::AirExpression>,
        ctx: &mut crate::ctx::AirGenContext,
        phi_condition_map: &std::collections::HashMap<(String, String), ConstraintSystemVariable>,
        switch_instructions: &Vec<crate::StructuredAirConstraint>,
    ) {
        println!(
            "  FMUL: op1={:?}, op2={:?}, res={:?} (bitwidth {}) - Setting up S/E/M aux vars.",
            self.operand1, self.operand2, self.result, self.operand_bitwidth
        );

        let reg_col_opt = ctx.col_for_ssa(self.result);

        let dest_col = ctx.new_aux_variable();
        ctx.bind_ssa_var(self.result, dest_col.0);
        let res_expr = AirExpression::Trace(dest_col, RowOffset::Current);

        let (s_bit_count, exp_bit_count, mant_bit_count) = match self.operand_bitwidth {
            16 => (1u32, 5u32, 10u32),
            32 => (1u32, 8u32, 23u32),
            64 => (1u32, 11u32, 52u32),
            80 => (1u32, 15u32, 63u32),
            128 => (1u32, 15u32, 112u32),
            _ => panic!(
                "Unsupported self.operand_bitwidth {} for FMul S/E/M decomposition.",
                self.operand_bitwidth
            ),
        };

        let (op1_s_var, op1_e_var, op1_m_var) = setup_sem_aux_vars(
            self.operand1,
            "op1",
            ctx,
            s_bit_count,
            exp_bit_count,
            mant_bit_count,
            constraints,
        );
        let (op2_s_var, op2_e_var, op2_m_var) = setup_sem_aux_vars(
            self.operand2,
            "op2_fmul",
            ctx,
            s_bit_count,
            exp_bit_count,
            mant_bit_count,
            constraints,
        );
        let (res_s_var, res_e_var, res_m_var) = setup_sem_aux_vars(
            Operand::Var(self.result),
            "res",
            ctx,
            s_bit_count,
            exp_bit_count,
            mant_bit_count,
            constraints,
        );

        let op1_s_expr = AirExpression::Trace(op1_s_var, RowOffset::Current);
        let op1_e_val_expr = AirExpression::Trace(op1_e_var, RowOffset::Current);
        let op1_m_val_expr = AirExpression::Trace(op1_m_var, RowOffset::Current);

        let op2_s_expr = AirExpression::Trace(op2_s_var, RowOffset::Current);
        let op2_e_val_expr = AirExpression::Trace(op2_e_var, RowOffset::Current);
        let op2_m_val_expr = AirExpression::Trace(op2_m_var, RowOffset::Current);

        let res_s_expr = AirExpression::Trace(res_s_var, RowOffset::Current);
        let res_e_val_expr = AirExpression::Trace(res_e_var, RowOffset::Current);
        let res_m_val_expr = AirExpression::Trace(res_m_var, RowOffset::Current);

        let op1_is_nan = fp_is_nan(
            &op1_e_val_expr,
            &op1_m_val_expr,
            exp_bit_count,
            mant_bit_count,
            ctx,
            constraints,
            "op1_fmul",
        );
        let op2_is_nan = fp_is_nan(
            &op2_e_val_expr,
            &op2_m_val_expr,
            exp_bit_count,
            mant_bit_count,
            ctx,
            constraints,
            "op2_fmul",
        );

        let op1_is_inf = fp_is_inf(
            &op1_e_val_expr,
            &op1_m_val_expr,
            exp_bit_count,
            mant_bit_count,
            ctx,
            constraints,
            "op1_fmul",
        );
        let op2_is_inf = fp_is_inf(
            &op2_e_val_expr,
            &op2_m_val_expr,
            exp_bit_count,
            mant_bit_count,
            ctx,
            constraints,
            "op2_fmul",
        );

        let op1_is_true_zero = fp_is_true_zero(
            &op1_e_val_expr,
            &op1_m_val_expr,
            exp_bit_count,
            mant_bit_count,
            ctx,
            constraints,
            "op1_fmul",
        );
        let op2_is_true_zero = fp_is_true_zero(
            &op2_e_val_expr,
            &op2_m_val_expr,
            exp_bit_count,
            mant_bit_count,
            ctx,
            constraints,
            "op2_fmul",
        );

        let qnan_sign = AirExpression::Constant(0);
        let qnan_exp = AirExpression::Constant((1u128 << exp_bit_count) - 1);
        let qnan_mant = AirExpression::Constant(1u128 << (mant_bit_count - 1));

        let res_is_nan_due_to_op_nan = fp_logical_or(
            &op1_is_nan,
            &op2_is_nan,
            ctx,
            constraints,
            "res_is_nan_from_op_fmul",
        );

        let op1_zero_op2_inf = fp_logical_and(
            &op1_is_true_zero,
            &op2_is_inf,
            ctx,
            constraints,
            "op1z_op2inf_fmul",
        );
        let op1_inf_op2_zero = fp_logical_and(
            &op1_is_inf,
            &op2_is_true_zero,
            ctx,
            constraints,
            "op1inf_op2z_fmul",
        );
        let res_is_nan_due_to_zero_inf = fp_logical_or(
            &op1_zero_op2_inf,
            &op1_inf_op2_zero,
            ctx,
            constraints,
            "res_nan_zero_inf_fmul",
        );

        let final_res_is_nan = fp_logical_or(
            &res_is_nan_due_to_op_nan,
            &res_is_nan_due_to_zero_inf,
            ctx,
            constraints,
            "final_res_is_nan_fmul",
        );

        let calculated_res_sign_if_not_nan = fp_icmp_neq(
            &op1_s_expr,
            &op2_s_expr,
            ctx,
            constraints,
            "calc_res_sign_fmul",
        );

        let general_case_res_s_expr =
            AirExpression::Trace(ctx.new_aux_variable(), RowOffset::Current);
        let general_case_res_e_expr =
            AirExpression::Trace(ctx.new_aux_variable(), RowOffset::Current);
        let general_case_res_m_expr =
            AirExpression::Trace(ctx.new_aux_variable(), RowOffset::Current);
        constraints.push(AirExpression::Mul(
            Box::new(general_case_res_s_expr.clone()),
            Box::new(AirExpression::Sub(
                Box::new(general_case_res_s_expr.clone()),
                Box::new(AirExpression::Constant(1)),
            )),
        ));

        let op1_is_inf_not_nan = fp_logical_and(
            &op1_is_inf,
            &fp_logical_not(&op1_is_nan, ctx, constraints, "op1_inf_nn_fmul"),
            ctx,
            constraints,
            "op1_inf_not_nan_fmul",
        );
        let op2_is_inf_not_nan = fp_logical_and(
            &op2_is_inf,
            &fp_logical_not(&op2_is_nan, ctx, constraints, "op2_inf_nn_fmul"),
            ctx,
            constraints,
            "op2_inf_not_nan_fmul",
        );

        let op1_is_finite_non_zero = fp_logical_and(
            &fp_logical_not(
                &op1_is_true_zero,
                ctx,
                constraints,
                "op1_not_zero_for_fin_fmul",
            ),
            &fp_logical_not(
                &op1_is_inf_not_nan,
                ctx,
                constraints,
                "op1_not_inf_for_fin_fmul",
            ),
            ctx,
            constraints,
            "op1_is_fin_nz_fmul",
        );
        let op1_is_finite_non_zero = fp_logical_and(
            &op1_is_finite_non_zero,
            &fp_logical_not(&op1_is_nan, ctx, constraints, "op1_not_nan_for_fin_fmul"),
            ctx,
            constraints,
            "op1_is_fin_nz_not_nan_fmul",
        );

        let op2_is_finite_non_zero = fp_logical_and(
            &fp_logical_not(
                &op2_is_true_zero,
                ctx,
                constraints,
                "op2_not_zero_for_fin_fmul",
            ),
            &fp_logical_not(
                &op2_is_inf_not_nan,
                ctx,
                constraints,
                "op2_not_inf_for_fin_fmul",
            ),
            ctx,
            constraints,
            "op2_is_fin_nz_fmul",
        );
        let op2_is_finite_non_zero = fp_logical_and(
            &op2_is_finite_non_zero,
            &fp_logical_not(&op2_is_nan, ctx, constraints, "op2_not_nan_for_fin_fmul"),
            ctx,
            constraints,
            "op2_is_fin_nz_not_nan_fmul",
        );

        let inf_x_inf = fp_logical_and(
            &op1_is_inf_not_nan,
            &op2_is_inf_not_nan,
            ctx,
            constraints,
            "inf_x_inf_fmul",
        );
        let inf_x_finite = fp_logical_and(
            &op1_is_inf_not_nan,
            &op2_is_finite_non_zero,
            ctx,
            constraints,
            "inf_x_finite_fmul",
        );
        let finite_x_inf = fp_logical_and(
            &op1_is_finite_non_zero,
            &op2_is_inf_not_nan,
            ctx,
            constraints,
            "finite_x_inf_fmul",
        );

        let is_inf_result_scenario = fp_logical_or(
            &inf_x_inf,
            &inf_x_finite,
            ctx,
            constraints,
            "is_inf_res_interim_fmul",
        );
        let is_inf_result_scenario = fp_logical_or(
            &is_inf_result_scenario,
            &finite_x_inf,
            ctx,
            constraints,
            "is_inf_res_scenario_fmul",
        );

        let inter_res_s_if_inf = calculated_res_sign_if_not_nan.clone();
        let inter_res_e_if_inf = qnan_exp.clone();
        let inter_res_m_if_inf = AirExpression::Constant(0);

        let op1_is_zero_not_special = fp_logical_and(
            &op1_is_true_zero,
            &fp_logical_not(&op1_is_nan, ctx, constraints, "op1_not_nan_z_fmul"),
            ctx,
            constraints,
            "op1_zero_not_nan_fmul",
        );
        let op1_is_zero_not_special = fp_logical_and(
            &op1_is_zero_not_special,
            &fp_logical_not(&op1_is_inf, ctx, constraints, "op1_not_inf_z_fmul"),
            ctx,
            constraints,
            "op1_zero_not_spec_fmul",
        );

        let op2_is_zero_not_special = fp_logical_and(
            &op2_is_true_zero,
            &fp_logical_not(&op2_is_nan, ctx, constraints, "op2_not_nan_z_fmul"),
            ctx,
            constraints,
            "op2_zero_not_nan_fmul",
        );
        let op2_is_zero_not_special = fp_logical_and(
            &op2_is_zero_not_special,
            &fp_logical_not(&op2_is_inf, ctx, constraints, "op2_not_inf_z_fmul"),
            ctx,
            constraints,
            "op2_zero_not_spec_fmul",
        );

        let op1_zero_op2_finite_not_inf_nan = fp_logical_and(
            &op1_is_zero_not_special,
            &fp_logical_not(
                &op2_is_inf_not_nan,
                ctx,
                constraints,
                "op2_nn_ni_for_z_fmul",
            ),
            ctx,
            constraints,
            "op1z_op2fin1_fmul",
        );
        let op1_zero_op2_finite_not_inf_nan = fp_logical_and(
            &op1_zero_op2_finite_not_inf_nan,
            &fp_logical_not(&op2_is_nan, ctx, constraints, "op1z_op2fin2_fmul"),
            ctx,
            constraints,
            "op1z_op2fin_fmul",
        );

        let op2_zero_op1_finite_not_inf_nan = fp_logical_and(
            &op2_is_zero_not_special,
            &fp_logical_not(
                &op1_is_inf_not_nan,
                ctx,
                constraints,
                "op1_nn_ni_for_z_fmul",
            ),
            ctx,
            constraints,
            "op2z_op1fin1_fmul",
        );
        let op2_zero_op1_finite_not_inf_nan = fp_logical_and(
            &op2_zero_op1_finite_not_inf_nan,
            &fp_logical_not(&op1_is_nan, ctx, constraints, "op2z_op1fin2_fmul"),
            ctx,
            constraints,
            "op2z_op1fin_fmul",
        );
        let is_zero_result_scenario = fp_logical_or(
            &op1_zero_op2_finite_not_inf_nan,
            &op2_zero_op1_finite_not_inf_nan,
            ctx,
            constraints,
            "is_zero_res_scenario_fmul",
        );

        let inter_res_s_if_zero = calculated_res_sign_if_not_nan.clone();
        let inter_res_e_if_zero = AirExpression::Constant(0);
        let inter_res_m_if_zero = AirExpression::Constant(0);

        let implicit_mant_bit_pos = mant_bit_count;
        let all_ones_exp_biased = (1u128 << exp_bit_count) - 1;
        let min_exp_biased_val = 1u128;
        let zero_exp_biased_val = 0u128;
        let bias_val = (1u128 << (exp_bit_count - 1)) - 1;

        let op1_is_denormal = fp_is_value_equal(
            &op1_e_val_expr,
            &AirExpression::Constant(zero_exp_biased_val),
            ctx,
            constraints,
            "op1_is_denorm_e_check_fmul",
        );
        let op2_is_denormal = fp_is_value_equal(
            &op2_e_val_expr,
            &AirExpression::Constant(zero_exp_biased_val),
            ctx,
            constraints,
            "op2_is_denorm_e_check_fmul",
        );

        let implicit_bit_val_op1 =
            fp_logical_not(&op1_is_denormal, ctx, constraints, "op1_implicit_bit_fmul");
        let implicit_bit_val_op2 =
            fp_logical_not(&op2_is_denormal, ctx, constraints, "op2_implicit_bit_fmul");

        let full_significand_op1 = fp_add(
            &op1_m_val_expr,
            &fp_mul(
                &implicit_bit_val_op1,
                &AirExpression::Constant(1u128 << implicit_mant_bit_pos),
                ctx,
                constraints,
                "op1_impl_shifted_fmul",
            ),
            ctx,
            constraints,
            "full_sig_op1_fmul",
        );
        let full_significand_op2 = fp_add(
            &op2_m_val_expr,
            &fp_mul(
                &implicit_bit_val_op2,
                &AirExpression::Constant(1u128 << implicit_mant_bit_pos),
                ctx,
                constraints,
                "op2_impl_shifted_fmul",
            ),
            ctx,
            constraints,
            "full_sig_op2_fmul",
        );

        let effective_exp_op1 = fp_select(
            &op1_is_denormal,
            &AirExpression::Constant(min_exp_biased_val),
            &op1_e_val_expr,
            ctx,
            constraints,
            "eff_exp_op1_fmul",
        );
        let effective_exp_op2 = fp_select(
            &op2_is_denormal,
            &AirExpression::Constant(min_exp_biased_val),
            &op2_e_val_expr,
            ctx,
            constraints,
            "eff_exp_op2_fmul",
        );

        let unbiased_exp1 = fp_sub(
            &effective_exp_op1,
            &AirExpression::Constant(bias_val),
            ctx,
            constraints,
            "unbiased_e1_fmul",
        );
        let unbiased_exp2 = fp_sub(
            &effective_exp_op2,
            &AirExpression::Constant(bias_val),
            ctx,
            constraints,
            "unbiased_e2_fmul",
        );
        let sum_unbiased_exps = fp_add(
            &unbiased_exp1,
            &unbiased_exp2,
            ctx,
            constraints,
            "sum_unbiased_exp_fmul",
        );
        let initial_biased_exp_for_norm = fp_add(
            &sum_unbiased_exps,
            &AirExpression::Constant(bias_val),
            ctx,
            constraints,
            "init_biased_exp_fmul",
        );

        let significand_product = fp_mul(
            &full_significand_op1,
            &full_significand_op2,
            ctx,
            constraints,
            "sig_prod_fmul",
        );

        let (
            normalized_sign,
            adjusted_biased_exp,
            normalized_significand,
            _is_true_zero_after_norm_round,
        ) = fp_normalize_and_round_significand(
            &significand_product,
            &calculated_res_sign_if_not_nan,
            &initial_biased_exp_for_norm,
            &AirExpression::Constant(0),
            &AirExpression::Constant(0),
            &AirExpression::Constant(0),
            mant_bit_count,
            exp_bit_count,
            ctx,
            constraints,
            "fmul_norm_round",
        );

        let exp_overflows = fp_icmp_ule(
            &AirExpression::Constant(all_ones_exp_biased),
            &adjusted_biased_exp,
            exp_bit_count + 1,
            ctx,
            constraints,
            "exp_overflows_fmul",
        );
        let exp_underflows_to_zero = fp_icmp_ule(
            &adjusted_biased_exp,
            &AirExpression::Constant(zero_exp_biased_val),
            exp_bit_count + 1,
            ctx,
            constraints,
            "exp_underflows_fmul",
        );

        let gen_case_s_val = normalized_sign.clone();
        let gen_case_intermediate_e_val = fp_select(
            &exp_underflows_to_zero,
            &AirExpression::Constant(zero_exp_biased_val),
            &adjusted_biased_exp,
            ctx,
            constraints,
            "gen_e_undf_fmul",
        );
        let gen_case_e_val = fp_select(
            &exp_overflows,
            &AirExpression::Constant(all_ones_exp_biased),
            &gen_case_intermediate_e_val,
            ctx,
            constraints,
            "gen_e_ovf_fmul",
        );

        let gen_case_intermediate_m_val = fp_select(
            &exp_underflows_to_zero,
            &AirExpression::Constant(0),
            &normalized_significand,
            ctx,
            constraints,
            "gen_m_undf_fmul",
        );
        let gen_case_m_val = fp_select(
            &exp_overflows,
            &AirExpression::Constant(0),
            &gen_case_intermediate_m_val,
            ctx,
            constraints,
            "gen_m_ovf_fmul",
        );

        let res_s_if_not_inf = fp_select(
            &is_zero_result_scenario,
            &inter_res_s_if_zero,
            &general_case_res_s_expr,
            ctx,
            constraints,
            "s_not_inf_zero_vs_gen_fmul",
        );
        let res_e_if_not_inf = fp_select(
            &is_zero_result_scenario,
            &inter_res_e_if_zero,
            &general_case_res_e_expr,
            ctx,
            constraints,
            "e_not_inf_zero_vs_gen_fmul",
        );
        let res_m_if_not_inf = fp_select(
            &is_zero_result_scenario,
            &inter_res_m_if_zero,
            &general_case_res_m_expr,
            ctx,
            constraints,
            "m_not_inf_zero_vs_gen_fmul",
        );

        let res_s_if_not_nan = fp_select(
            &is_inf_result_scenario,
            &inter_res_s_if_inf,
            &res_s_if_not_inf,
            ctx,
            constraints,
            "s_not_nan_inf_vs_else_fmul",
        );
        let res_e_if_not_nan = fp_select(
            &is_inf_result_scenario,
            &inter_res_e_if_inf,
            &res_e_if_not_inf,
            ctx,
            constraints,
            "e_not_nan_inf_vs_else_fmul",
        );
        let res_m_if_not_nan = fp_select(
            &is_inf_result_scenario,
            &inter_res_m_if_inf,
            &res_m_if_not_inf,
            ctx,
            constraints,
            "m_not_nan_inf_vs_else_fmul",
        );

        let final_res_s_val = fp_select(
            &final_res_is_nan,
            &qnan_sign,
            &res_s_if_not_nan,
            ctx,
            constraints,
            "final_s_fmul",
        );
        let final_res_e_val = fp_select(
            &final_res_is_nan,
            &qnan_exp,
            &res_e_if_not_nan,
            ctx,
            constraints,
            "final_e_fmul",
        );
        let final_res_m_val = fp_select(
            &final_res_is_nan,
            &qnan_mant,
            &res_m_if_not_nan,
            ctx,
            constraints,
            "final_m_fmul",
        );

        constraints.push(AirExpression::Sub(
            Box::new(res_s_expr),
            Box::new(final_res_s_val),
        ));
        constraints.push(AirExpression::Sub(
            Box::new(res_e_val_expr),
            Box::new(final_res_e_val),
        ));
        constraints.push(AirExpression::Sub(
            Box::new(res_m_val_expr),
            Box::new(final_res_m_val),
        ));

        let not_final_nan_cond = fp_logical_not(
            &final_res_is_nan,
            ctx,
            constraints,
            "not_final_nan_for_gen_fmul",
        );
        let not_inf_res_cond = fp_logical_not(
            &is_inf_result_scenario,
            ctx,
            constraints,
            "not_inf_res_for_gen_fmul",
        );
        let not_zero_res_cond = fp_logical_not(
            &is_zero_result_scenario,
            ctx,
            constraints,
            "not_zero_res_for_gen_fmul",
        );
        let is_general_case_cond_pt1 = fp_logical_and(
            &not_final_nan_cond,
            &not_inf_res_cond,
            ctx,
            constraints,
            "gen_case_pt1_fmul",
        );
        let is_general_case_condition = fp_logical_and(
            &is_general_case_cond_pt1,
            &not_zero_res_cond,
            ctx,
            constraints,
            "is_general_case_fmul",
        );

        let gen_s_val_diff = fp_sub(
            &general_case_res_s_expr,
            &gen_case_s_val,
            ctx,
            constraints,
            "gen_s_val_diff_fmul",
        );
        let gen_s_constraint = fp_mul(
            &is_general_case_condition,
            &gen_s_val_diff,
            ctx,
            constraints,
            "gen_s_constr_mul_fmul",
        );
        constraints.push(gen_s_constraint);

        let gen_e_val_diff = fp_sub(
            &general_case_res_e_expr,
            &gen_case_e_val,
            ctx,
            constraints,
            "gen_e_val_diff_fmul",
        );
        let gen_e_constraint = fp_mul(
            &is_general_case_condition,
            &gen_e_val_diff,
            ctx,
            constraints,
            "gen_e_constr_mul_fmul",
        );
        constraints.push(gen_e_constraint);

        let gen_m_val_diff = fp_sub(
            &general_case_res_m_expr,
            &gen_case_m_val,
            ctx,
            constraints,
            "gen_m_val_diff_fmul",
        );
        let gen_m_constraint = fp_mul(
            &is_general_case_condition,
            &gen_m_val_diff,
            ctx,
            constraints,
            "gen_m_constr_mul_fmul",
        );
        constraints.push(gen_m_constraint);

        if let Some(reg_col) = reg_col_opt {
            let selector_expr = ctx.new_row_selector();
            let reg_expr = AirExpression::Trace(AirTraceVariable(reg_col), RowOffset::Current);
            let eq_expr = AirExpression::Sub(Box::new(res_expr.clone()), Box::new(reg_expr));
            ctx.add_row_gated_constraint(selector_expr, eq_expr);
        }
    }
}

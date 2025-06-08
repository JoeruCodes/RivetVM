use crate::constraints::{AirExpression, RowOffset};
use crate::{constraints::ResolveConstraint, Operand};
use crate::{utils::*, ConstraintSystemVariable};

#[derive(Debug, Clone)]
pub struct FDiv {
    pub operand1: Operand,
    pub operand2: Operand,
    pub result: ConstraintSystemVariable,
    pub block_name: String,
    pub operand_bitwidth: u32,
}

impl ResolveConstraint for FDiv {
    fn resolve(
        &self,
        constraints: &mut Vec<super::AirExpression>,
        ctx: &mut crate::ctx::AirGenContext,
        phi_condition_map: &std::collections::HashMap<
            (String, String),
            crate::ConstraintSystemVariable,
        >,
        switch_instructions: &Vec<crate::StructuredAirConstraint>,
    ) {
        println!(
            "  FDIV: op1={:?}, op2={:?}, res={:?} (bitwidth {}) - Setting up S/E/M aux vars.",
            self.operand1, self.operand2, self.result, self.operand_bitwidth
        );

        let (s_bit_count, exp_bit_count, mant_bit_count) = match self.operand_bitwidth {
            16 => (1u32, 5u32, 10u32),
            32 => (1u32, 8u32, 23u32),
            64 => (1u32, 11u32, 52u32),
            80 => (1u32, 15u32, 63u32),
            128 => (1u32, 15u32, 112u32),
            _ => panic!(
                "Unsupported self.operand_bitwidth {} for FDiv S/E/M decomposition.",
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
            "op2_fdiv",
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
            "op1_fdiv",
        );
        let op2_is_nan = fp_is_nan(
            &op2_e_val_expr,
            &op2_m_val_expr,
            exp_bit_count,
            mant_bit_count,
            ctx,
            constraints,
            "op2_fdiv",
        );

        let op1_is_inf = fp_is_inf(
            &op1_e_val_expr,
            &op1_m_val_expr,
            exp_bit_count,
            mant_bit_count,
            ctx,
            constraints,
            "op1_fdiv",
        );
        let op2_is_inf = fp_is_inf(
            &op2_e_val_expr,
            &op2_m_val_expr,
            exp_bit_count,
            mant_bit_count,
            ctx,
            constraints,
            "op2_fdiv",
        );

        let op1_is_true_zero = fp_is_true_zero(
            &op1_e_val_expr,
            &op1_m_val_expr,
            exp_bit_count,
            mant_bit_count,
            ctx,
            constraints,
            "op1_fdiv",
        );
        let op2_is_true_zero = fp_is_true_zero(
            &op2_e_val_expr,
            &op2_m_val_expr,
            exp_bit_count,
            mant_bit_count,
            ctx,
            constraints,
            "op2_fdiv",
        );

        let qnan_sign = AirExpression::Constant(0);
        let qnan_exp = AirExpression::Constant((1u128 << exp_bit_count) - 1);
        let qnan_mant = AirExpression::Constant(1u128 << (mant_bit_count - 1));

        let res_is_nan_due_to_op_nan = fp_logical_or(
            &op1_is_nan,
            &op2_is_nan,
            ctx,
            constraints,
            "res_is_nan_from_op_fdiv",
        );

        let op1_zero_op2_zero = fp_logical_and(
            &op1_is_true_zero,
            &op2_is_true_zero,
            ctx,
            constraints,
            "op1z_op2z_fdiv",
        );
        let op1_inf_op2_inf = fp_logical_and(
            &op1_is_inf,
            &op2_is_inf,
            ctx,
            constraints,
            "op1inf_op2inf_fdiv",
        );
        let res_is_nan_due_to_undef = fp_logical_or(
            &op1_zero_op2_zero,
            &op1_inf_op2_inf,
            ctx,
            constraints,
            "res_nan_undef_fdiv",
        );

        let final_res_is_nan = fp_logical_or(
            &res_is_nan_due_to_op_nan,
            &res_is_nan_due_to_undef,
            ctx,
            constraints,
            "final_res_is_nan_fdiv",
        );

        let calculated_res_sign_if_not_nan = fp_icmp_neq(
            &op1_s_expr,
            &op2_s_expr,
            ctx,
            constraints,
            "calc_res_sign_fdiv",
        );

        let op1_is_finite_non_zero = fp_logical_and(
            &fp_logical_not(
                &op1_is_true_zero,
                ctx,
                constraints,
                "op1_not_zero_for_fin_fdiv",
            ),
            &fp_logical_not(&op1_is_inf, ctx, constraints, "op1_not_inf_for_fin_fdiv"),
            ctx,
            constraints,
            "op1_is_fin_nz_fdiv",
        );
        let op2_is_finite_non_zero = fp_logical_and(
            &fp_logical_not(
                &op2_is_true_zero,
                ctx,
                constraints,
                "op2_not_zero_for_fin_fdiv",
            ),
            &fp_logical_not(&op2_is_inf, ctx, constraints, "op2_not_inf_for_fin_fdiv"),
            ctx,
            constraints,
            "op2_is_fin_nz_fdiv",
        );

        let finite_div_zero = fp_logical_and(
            &op1_is_finite_non_zero,
            &op2_is_true_zero,
            ctx,
            constraints,
            "fin_div_zero_fdiv",
        );
        let inf_div_finite = fp_logical_and(
            &op1_is_inf,
            &op2_is_finite_non_zero,
            ctx,
            constraints,
            "inf_div_fin_fdiv",
        );
        let is_inf_result_scenario = fp_logical_or(
            &finite_div_zero,
            &inf_div_finite,
            ctx,
            constraints,
            "is_inf_res_scenario_fdiv",
        );

        let inter_res_s_if_inf = calculated_res_sign_if_not_nan.clone();
        let inter_res_e_if_inf = qnan_exp.clone();
        let inter_res_m_if_inf = AirExpression::Constant(0);

        let zero_div_finite = fp_logical_and(
            &op1_is_true_zero,
            &op2_is_finite_non_zero,
            ctx,
            constraints,
            "zero_div_fin_fdiv",
        );
        let finite_div_inf = fp_logical_and(
            &op1_is_finite_non_zero,
            &op2_is_inf,
            ctx,
            constraints,
            "fin_div_inf_fdiv",
        );
        let is_zero_result_scenario = fp_logical_or(
            &zero_div_finite,
            &finite_div_inf,
            ctx,
            constraints,
            "is_zero_res_scenario_fdiv",
        );

        let inter_res_s_if_zero = calculated_res_sign_if_not_nan.clone();
        let inter_res_e_if_zero = AirExpression::Constant(0);
        let inter_res_m_if_zero = AirExpression::Constant(0);

        let implicit_mant_bit_pos = mant_bit_count;
        let all_ones_exp_biased = (1u128 << exp_bit_count) - 1;
        let min_exp_biased_val = 1u128;
        let zero_exp_biased_val = 0u128;
        let bias_val = (1u128 << (exp_bit_count - 1)) - 1;

        let res_is_denormal = fp_is_value_equal(
            &res_e_val_expr,
            &AirExpression::Constant(zero_exp_biased_val),
            ctx,
            constraints,
            "res_is_denorm_e_check_fdiv",
        );
        let op2_is_denormal = fp_is_value_equal(
            &op2_e_val_expr,
            &AirExpression::Constant(zero_exp_biased_val),
            ctx,
            constraints,
            "op2_is_denorm_e_check_fdiv",
        );

        let implicit_bit_val_res =
            fp_logical_not(&res_is_denormal, ctx, constraints, "res_implicit_bit_fdiv");
        let implicit_bit_val_op2 =
            fp_logical_not(&op2_is_denormal, ctx, constraints, "op2_implicit_bit_fdiv");

        let full_significand_res = fp_add(
            &res_m_val_expr,
            &fp_mul(
                &implicit_bit_val_res,
                &AirExpression::Constant(1u128 << implicit_mant_bit_pos),
                ctx,
                constraints,
                "res_impl_shifted_fdiv",
            ),
            ctx,
            constraints,
            "full_sig_res_fdiv",
        );
        let full_significand_op2 = fp_add(
            &op2_m_val_expr,
            &fp_mul(
                &implicit_bit_val_op2,
                &AirExpression::Constant(1u128 << implicit_mant_bit_pos),
                ctx,
                constraints,
                "op2_impl_shifted_fdiv",
            ),
            ctx,
            constraints,
            "full_sig_op2_fdiv",
        );

        let effective_exp_res = fp_select(
            &res_is_denormal,
            &AirExpression::Constant(min_exp_biased_val),
            &res_e_val_expr,
            ctx,
            constraints,
            "eff_exp_res_fdiv",
        );
        let effective_exp_op2 = fp_select(
            &op2_is_denormal,
            &AirExpression::Constant(min_exp_biased_val),
            &op2_e_val_expr,
            ctx,
            constraints,
            "eff_exp_op2_fdiv",
        );

        let unbiased_exp_res = fp_sub(
            &effective_exp_res,
            &AirExpression::Constant(bias_val),
            ctx,
            constraints,
            "unbiased_eres_fdiv",
        );
        let unbiased_exp_op2 = fp_sub(
            &effective_exp_op2,
            &AirExpression::Constant(bias_val),
            ctx,
            constraints,
            "unbiased_e2_fdiv",
        );
        let sum_unbiased_exps = fp_add(
            &unbiased_exp_res,
            &unbiased_exp_op2,
            ctx,
            constraints,
            "sum_unbiased_exp_fdiv",
        );
        let initial_biased_exp_for_norm = fp_add(
            &sum_unbiased_exps,
            &AirExpression::Constant(bias_val),
            ctx,
            constraints,
            "init_biased_exp_fdiv",
        );

        let significand_product = fp_mul(
            &full_significand_res,
            &full_significand_op2,
            ctx,
            constraints,
            "sig_prod_fdiv",
        );

        let calculated_op1_sign = fp_icmp_neq(
            &res_s_expr,
            &op2_s_expr,
            ctx,
            constraints,
            "calc_op1_sign_fdiv",
        );

        let (_normalized_sign, adjusted_biased_exp, normalized_significand, _) =
            fp_normalize_and_round_significand(
                &significand_product,
                &calculated_op1_sign,
                &initial_biased_exp_for_norm,
                &AirExpression::Constant(0),
                &AirExpression::Constant(0),
                &AirExpression::Constant(0),
                mant_bit_count,
                exp_bit_count,
                ctx,
                constraints,
                "fdiv_norm_round",
            );

        let exp_overflows = fp_icmp_ule(
            &AirExpression::Constant(all_ones_exp_biased),
            &adjusted_biased_exp,
            exp_bit_count + 1,
            ctx,
            constraints,
            "exp_overflows_fdiv",
        );
        let exp_underflows_to_zero = fp_icmp_ule(
            &adjusted_biased_exp,
            &AirExpression::Constant(zero_exp_biased_val),
            exp_bit_count + 1,
            ctx,
            constraints,
            "exp_underflows_fdiv",
        );

        let gen_case_op1_intermediate_e = fp_select(
            &exp_underflows_to_zero,
            &AirExpression::Constant(zero_exp_biased_val),
            &adjusted_biased_exp,
            ctx,
            constraints,
            "gen_op1_e_undf_fdiv",
        );
        let gen_case_op1_e = fp_select(
            &exp_overflows,
            &AirExpression::Constant(all_ones_exp_biased),
            &gen_case_op1_intermediate_e,
            ctx,
            constraints,
            "gen_op1_e_ovf_fdiv",
        );

        let gen_case_op1_intermediate_m = fp_select(
            &exp_underflows_to_zero,
            &AirExpression::Constant(0),
            &normalized_significand,
            ctx,
            constraints,
            "gen_op1_m_undf_fdiv",
        );
        let gen_case_op1_m = fp_select(
            &exp_overflows,
            &AirExpression::Constant(0),
            &gen_case_op1_intermediate_m,
            ctx,
            constraints,
            "gen_op1_m_ovf_fdiv",
        );

        let res_s_if_not_inf = fp_select(
            &is_zero_result_scenario,
            &inter_res_s_if_zero,
            &res_s_expr,
            ctx,
            constraints,
            "s_not_inf_zero_vs_gen_fdiv",
        );
        let res_e_if_not_inf = fp_select(
            &is_zero_result_scenario,
            &inter_res_e_if_zero,
            &res_e_val_expr,
            ctx,
            constraints,
            "e_not_inf_zero_vs_gen_fdiv",
        );
        let res_m_if_not_inf = fp_select(
            &is_zero_result_scenario,
            &inter_res_m_if_zero,
            &res_m_val_expr,
            ctx,
            constraints,
            "m_not_inf_zero_vs_gen_fdiv",
        );

        let res_s_if_not_nan = fp_select(
            &is_inf_result_scenario,
            &inter_res_s_if_inf,
            &res_s_if_not_inf,
            ctx,
            constraints,
            "s_not_nan_inf_vs_else_fdiv",
        );
        let res_e_if_not_nan = fp_select(
            &is_inf_result_scenario,
            &inter_res_e_if_inf,
            &res_e_if_not_inf,
            ctx,
            constraints,
            "e_not_nan_inf_vs_else_fdiv",
        );
        let res_m_if_not_nan = fp_select(
            &is_inf_result_scenario,
            &inter_res_m_if_inf,
            &res_m_if_not_inf,
            ctx,
            constraints,
            "m_not_nan_inf_vs_else_fdiv",
        );

        let final_res_s_val = fp_select(
            &final_res_is_nan,
            &qnan_sign,
            &res_s_if_not_nan,
            ctx,
            constraints,
            "final_s_fdiv",
        );
        let final_res_e_val = fp_select(
            &final_res_is_nan,
            &qnan_exp,
            &res_e_if_not_nan,
            ctx,
            constraints,
            "final_e_fdiv",
        );
        let final_res_m_val = fp_select(
            &final_res_is_nan,
            &qnan_mant,
            &res_m_if_not_nan,
            ctx,
            constraints,
            "final_m_fdiv",
        );

        constraints.push(AirExpression::Sub(
            Box::new(res_s_expr.clone()),
            Box::new(final_res_s_val),
        ));
        constraints.push(AirExpression::Sub(
            Box::new(res_e_val_expr.clone()),
            Box::new(final_res_e_val),
        ));
        constraints.push(AirExpression::Sub(
            Box::new(res_m_val_expr.clone()),
            Box::new(final_res_m_val),
        ));

        let not_final_nan_cond = fp_logical_not(
            &final_res_is_nan,
            ctx,
            constraints,
            "not_final_nan_for_gen_fdiv",
        );
        let not_inf_res_cond = fp_logical_not(
            &is_inf_result_scenario,
            ctx,
            constraints,
            "not_inf_res_for_gen_fdiv",
        );
        let not_zero_res_cond = fp_logical_not(
            &is_zero_result_scenario,
            ctx,
            constraints,
            "not_zero_res_for_gen_fdiv",
        );
        let is_general_case_cond_pt1 = fp_logical_and(
            &not_final_nan_cond,
            &not_inf_res_cond,
            ctx,
            constraints,
            "gen_case_pt1_fdiv",
        );
        let is_general_case_condition = fp_logical_and(
            &is_general_case_cond_pt1,
            &not_zero_res_cond,
            ctx,
            constraints,
            "is_general_case_fdiv",
        );

        let op1_s_diff = fp_sub(
            &op1_s_expr,
            &calculated_op1_sign,
            ctx,
            constraints,
            "op1_s_diff_fdiv",
        );
        let op1_s_constraint = fp_mul(
            &is_general_case_condition,
            &op1_s_diff,
            ctx,
            constraints,
            "op1_s_constr_fdiv",
        );
        constraints.push(op1_s_constraint);

        let op1_e_diff = fp_sub(
            &op1_e_val_expr,
            &gen_case_op1_e,
            ctx,
            constraints,
            "op1_e_diff_fdiv",
        );
        let op1_e_constraint = fp_mul(
            &is_general_case_condition,
            &op1_e_diff,
            ctx,
            constraints,
            "op1_e_constr_fdiv",
        );
        constraints.push(op1_e_constraint);

        let op1_m_diff = fp_sub(
            &op1_m_val_expr,
            &gen_case_op1_m,
            ctx,
            constraints,
            "op1_m_diff_fdiv",
        );
        let op1_m_constraint = fp_mul(
            &is_general_case_condition,
            &op1_m_diff,
            ctx,
            constraints,
            "op1_m_constr_fdiv",
        );
        constraints.push(op1_m_constraint);
    }
}

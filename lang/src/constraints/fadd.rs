use crate::constraints::{AirExpression, RowOffset};
use crate::utils::*;
use crate::{constraints::ResolveConstraint, ConstraintSystemVariable, Operand};

#[derive(Debug, Clone)]
pub struct FAdd {
    pub operand1: Operand,
    pub operand2: Operand,
    pub result: ConstraintSystemVariable,
    pub block_name: String,
    pub operand_bitwidth: u32,
}

impl ResolveConstraint for FAdd {
    fn resolve(
        &self,
        constraints: &mut Vec<super::AirExpression>,
        ctx: &mut crate::ctx::AirGenContext,
        phi_condition_map: &std::collections::HashMap<(String, String), ConstraintSystemVariable>,
        switch_instructions: &Vec<crate::StructuredAirConstraint>,
    ) {
        println!(
            "  FADD: op1={:?}, op2={:?}, res={:?} (bitwidth {}) - Setting up S/E/M aux vars.",
            self.operand1, self.operand2, self.result, self.operand_bitwidth
        );

        let (s_bit_count, exp_bit_count, mant_bit_count) = match self.operand_bitwidth {
            16 => (1u32, 5u32, 10u32),
            32 => (1u32, 8u32, 23u32),
            64 => (1u32, 11u32, 52u32),
            80 => (1u32, 15u32, 63u32),
            128 => (1u32, 15u32, 112u32),
            _ => panic!(
                "Unsupported self.operand_bitwidth {} for FAdd S/E/M decomposition.",
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
            "op2",
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
            "op1",
        );
        let op2_is_nan = fp_is_nan(
            &op2_e_val_expr,
            &op2_m_val_expr,
            exp_bit_count,
            mant_bit_count,
            ctx,
            constraints,
            "op2",
        );

        let op1_is_inf = fp_is_inf(
            &op1_e_val_expr,
            &op1_m_val_expr,
            exp_bit_count,
            mant_bit_count,
            ctx,
            constraints,
            "op1",
        );
        let op2_is_inf = fp_is_inf(
            &op2_e_val_expr,
            &op2_m_val_expr,
            exp_bit_count,
            mant_bit_count,
            ctx,
            constraints,
            "op2",
        );

        let op1_is_pos_inf = fp_logical_and(
            &op1_is_inf,
            &fp_is_value_zero(&op1_s_expr, ctx, constraints, "op1_s_is_zero"),
            ctx,
            constraints,
            "op1_is_pos_inf",
        );
        let op1_is_neg_inf = fp_logical_and(
            &op1_is_inf,
            &fp_logical_not(
                &fp_is_value_zero(&op1_s_expr, ctx, constraints, "op1_s_is_zero_for_neg"),
                ctx,
                constraints,
                "op1_s_is_one",
            ),
            ctx,
            constraints,
            "op1_is_neg_inf",
        );
        let op2_is_pos_inf = fp_logical_and(
            &op2_is_inf,
            &fp_is_value_zero(&op2_s_expr, ctx, constraints, "op2_s_is_zero"),
            ctx,
            constraints,
            "op2_is_pos_inf",
        );
        let op2_is_neg_inf = fp_logical_and(
            &op2_is_inf,
            &fp_logical_not(
                &fp_is_value_zero(&op2_s_expr, ctx, constraints, "op2_s_is_zero_for_neg"),
                ctx,
                constraints,
                "op2_s_is_one",
            ),
            ctx,
            constraints,
            "op2_is_neg_inf",
        );

        let op1_is_true_zero = fp_is_true_zero(
            &op1_e_val_expr,
            &op1_m_val_expr,
            exp_bit_count,
            mant_bit_count,
            ctx,
            constraints,
            "op1",
        );
        let op2_is_true_zero = fp_is_true_zero(
            &op2_e_val_expr,
            &op2_m_val_expr,
            exp_bit_count,
            mant_bit_count,
            ctx,
            constraints,
            "op2",
        );

        let qnan_sign = AirExpression::Constant(0);
        let qnan_exp = AirExpression::Constant((1u128 << exp_bit_count) - 1);
        let qnan_mant = AirExpression::Constant(1u128 << (mant_bit_count - 1));

        let res_is_nan_due_to_op_nan = fp_logical_or(
            &op1_is_nan,
            &op2_is_nan,
            ctx,
            constraints,
            "res_is_nan_from_op",
        );

        let inf_plus_neg_inf = fp_logical_and(
            &op1_is_pos_inf,
            &op2_is_neg_inf,
            ctx,
            constraints,
            "pInf_nInf",
        );
        let neg_inf_plus_pos_inf = fp_logical_and(
            &op1_is_neg_inf,
            &op2_is_pos_inf,
            ctx,
            constraints,
            "nInf_pInf",
        );
        let res_is_nan_due_to_inf_cancel = fp_logical_or(
            &inf_plus_neg_inf,
            &neg_inf_plus_pos_inf,
            ctx,
            constraints,
            "res_is_nan_inf_cancel",
        );

        let final_res_is_nan = fp_logical_or(
            &res_is_nan_due_to_op_nan,
            &res_is_nan_due_to_inf_cancel,
            ctx,
            constraints,
            "final_res_is_nan",
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
            &fp_logical_not(&op1_is_nan, ctx, constraints, "op1_not_nan"),
            ctx,
            constraints,
            "op1_inf_not_nan",
        );
        let op2_is_inf_not_nan = fp_logical_and(
            &op2_is_inf,
            &fp_logical_not(&op2_is_nan, ctx, constraints, "op2_not_nan"),
            ctx,
            constraints,
            "op2_inf_not_nan",
        );
        let op1_is_fin_not_nan =
            fp_logical_not(&op1_is_inf_not_nan, ctx, constraints, "op1_fin_not_nan");
        let op2_is_fin_not_nan =
            fp_logical_not(&op2_is_inf_not_nan, ctx, constraints, "op2_fin_not_nan");

        let inf_plus_finite_res_s = fp_select(
            &op1_is_inf_not_nan,
            &op1_s_expr,
            &op2_s_expr,
            ctx,
            constraints,
            "inf_fin_s",
        );

        let cond_inf_plus_finite = fp_logical_or(
            &fp_logical_and(
                &op1_is_inf_not_nan,
                &op2_is_fin_not_nan,
                ctx,
                constraints,
                "op1inf_op2fin",
            ),
            &fp_logical_and(
                &op2_is_inf_not_nan,
                &op1_is_fin_not_nan,
                ctx,
                constraints,
                "op2inf_op1fin",
            ),
            ctx,
            constraints,
            "cond_inf_plus_fin",
        );

        let op1_is_pos_inf_not_nan = fp_logical_and(
            &op1_is_pos_inf,
            &fp_logical_not(&op1_is_nan, ctx, constraints, "op1_pos_inf_nn_aux1"),
            ctx,
            constraints,
            "op1_pos_inf_nn",
        );
        let op2_is_pos_inf_not_nan = fp_logical_and(
            &op2_is_pos_inf,
            &fp_logical_not(&op2_is_nan, ctx, constraints, "op2_pos_inf_nn_aux1"),
            ctx,
            constraints,
            "op2_pos_inf_nn",
        );
        let op1_is_neg_inf_not_nan = fp_logical_and(
            &op1_is_neg_inf,
            &fp_logical_not(&op1_is_nan, ctx, constraints, "op1_neg_inf_nn_aux1"),
            ctx,
            constraints,
            "op1_neg_inf_nn",
        );
        let op2_is_neg_inf_not_nan = fp_logical_and(
            &op2_is_neg_inf,
            &fp_logical_not(&op2_is_nan, ctx, constraints, "op2_neg_inf_nn_aux1"),
            ctx,
            constraints,
            "op2_neg_inf_nn",
        );

        let both_pos_inf = fp_logical_and(
            &op1_is_pos_inf_not_nan,
            &op2_is_pos_inf_not_nan,
            ctx,
            constraints,
            "both_pos_inf",
        );
        let both_neg_inf = fp_logical_and(
            &op1_is_neg_inf_not_nan,
            &op2_is_neg_inf_not_nan,
            ctx,
            constraints,
            "both_neg_inf",
        );
        let cond_both_inf_same_sign = fp_logical_or(
            &both_pos_inf,
            &both_neg_inf,
            ctx,
            constraints,
            "both_inf_same_sign",
        );
        let both_inf_same_sign_res_s = op1_s_expr.clone();

        let is_inf_result_scenario = fp_logical_or(
            &cond_inf_plus_finite,
            &cond_both_inf_same_sign,
            ctx,
            constraints,
            "is_inf_res_scenario",
        );
        let inter_res_s_if_inf = fp_select(
            &cond_inf_plus_finite,
            &inf_plus_finite_res_s,
            &both_inf_same_sign_res_s,
            ctx,
            constraints,
            "inter_s_if_inf",
        );
        let inter_res_e_if_inf = qnan_exp.clone();
        let inter_res_m_if_inf = AirExpression::Constant(0);

        let op1_is_zero_not_special = fp_logical_and(
            &op1_is_true_zero,
            &fp_logical_not(&op1_is_nan, ctx, constraints, "op1_not_nan_z"),
            ctx,
            constraints,
            "op1_zero_not_nan",
        );
        let op1_is_zero_not_special = fp_logical_and(
            &op1_is_zero_not_special,
            &fp_logical_not(&op1_is_inf, ctx, constraints, "op1_not_inf_z"),
            ctx,
            constraints,
            "op1_zero_not_spec",
        );

        let op2_is_zero_not_special = fp_logical_and(
            &op2_is_true_zero,
            &fp_logical_not(&op2_is_nan, ctx, constraints, "op2_not_nan_z"),
            ctx,
            constraints,
            "op2_zero_not_nan",
        );
        let op2_is_zero_not_special = fp_logical_and(
            &op2_is_zero_not_special,
            &fp_logical_not(&op2_is_inf, ctx, constraints, "op2_not_inf_z"),
            ctx,
            constraints,
            "op2_zero_not_spec",
        );

        let cond_op1_zero_op2_fin = fp_logical_and(
            &op1_is_zero_not_special,
            &op2_is_fin_not_nan,
            ctx,
            constraints,
            "op1z_op2fin",
        );
        let cond_op2_zero_op1_fin = fp_logical_and(
            &op2_is_zero_not_special,
            &op1_is_fin_not_nan,
            ctx,
            constraints,
            "op2z_op1fin",
        );

        let zero_plus_fin_res_s = fp_select(
            &cond_op1_zero_op2_fin,
            &op2_s_expr,
            &op1_s_expr,
            ctx,
            constraints,
            "zero_fin_s",
        );
        let zero_plus_fin_res_e = fp_select(
            &cond_op1_zero_op2_fin,
            &op2_e_val_expr,
            &op1_e_val_expr,
            ctx,
            constraints,
            "zero_fin_e",
        );
        let zero_plus_fin_res_m = fp_select(
            &cond_op1_zero_op2_fin,
            &op2_m_val_expr,
            &op1_m_val_expr,
            ctx,
            constraints,
            "zero_fin_m",
        );
        let cond_zero_plus_finite = fp_logical_or(
            &cond_op1_zero_op2_fin,
            &cond_op2_zero_op1_fin,
            ctx,
            constraints,
            "cond_zero_plus_fin",
        );

        let both_true_zero = fp_logical_and(
            &op1_is_zero_not_special,
            &op2_is_zero_not_special,
            ctx,
            constraints,
            "both_zero",
        );
        let both_zero_res_s = fp_logical_and(
            &op1_s_expr,
            &op2_s_expr,
            ctx,
            constraints,
            "both_zero_s_logic",
        );
        let both_zero_res_e = AirExpression::Constant(0);
        let both_zero_res_m = AirExpression::Constant(0);

        let is_zero_result_scenario = fp_logical_or(
            &cond_zero_plus_finite,
            &both_true_zero,
            ctx,
            constraints,
            "is_zero_res_scenario",
        );
        let inter_res_s_if_zero = fp_select(
            &cond_zero_plus_finite,
            &zero_plus_fin_res_s,
            &both_zero_res_s,
            ctx,
            constraints,
            "inter_s_if_zero",
        );
        let inter_res_e_if_zero = fp_select(
            &cond_zero_plus_finite,
            &zero_plus_fin_res_e,
            &both_zero_res_e,
            ctx,
            constraints,
            "inter_e_if_zero",
        );
        let inter_res_m_if_zero = fp_select(
            &cond_zero_plus_finite,
            &zero_plus_fin_res_m,
            &both_zero_res_m,
            ctx,
            constraints,
            "inter_m_if_zero",
        );

        let res_s_if_not_nan = fp_select(
            &is_inf_result_scenario,
            &inter_res_s_if_inf,
            &general_case_res_s_expr,
            ctx,
            constraints,
            "s_not_nan_inf_vs_gen",
        );
        let res_e_if_not_nan = fp_select(
            &is_inf_result_scenario,
            &inter_res_e_if_inf,
            &general_case_res_e_expr,
            ctx,
            constraints,
            "e_not_nan_inf_vs_gen",
        );
        let res_m_if_not_nan = fp_select(
            &is_inf_result_scenario,
            &inter_res_m_if_inf,
            &general_case_res_m_expr,
            ctx,
            constraints,
            "m_not_nan_inf_vs_gen",
        );

        let res_s_if_not_nan_not_inf = fp_select(
            &is_zero_result_scenario,
            &inter_res_s_if_zero,
            &res_s_if_not_nan,
            ctx,
            constraints,
            "s_not_nan_not_inf_zero_vs_else",
        );
        let res_e_if_not_nan_not_inf = fp_select(
            &is_zero_result_scenario,
            &inter_res_e_if_zero,
            &res_e_if_not_nan,
            ctx,
            constraints,
            "e_not_nan_not_inf_zero_vs_else",
        );
        let res_m_if_not_nan_not_inf = fp_select(
            &is_zero_result_scenario,
            &inter_res_m_if_zero,
            &res_m_if_not_nan,
            ctx,
            constraints,
            "m_not_nan_not_inf_zero_vs_else",
        );

        let final_res_s_val = fp_select(
            &final_res_is_nan,
            &qnan_sign,
            &res_s_if_not_nan_not_inf,
            ctx,
            constraints,
            "final_s",
        );
        let final_res_e_val = fp_select(
            &final_res_is_nan,
            &qnan_exp,
            &res_e_if_not_nan_not_inf,
            ctx,
            constraints,
            "final_e",
        );
        let final_res_m_val = fp_select(
            &final_res_is_nan,
            &qnan_mant,
            &res_m_if_not_nan_not_inf,
            ctx,
            constraints,
            "final_m",
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

        let not_special_scenario_intermediate1 =
            fp_logical_not(&final_res_is_nan, ctx, constraints, "not_nan_for_gen");
        let not_special_scenario_intermediate2 =
            fp_logical_not(&is_inf_result_scenario, ctx, constraints, "not_inf_for_gen");
        let not_special_scenario_intermediate3 = fp_logical_not(
            &is_zero_result_scenario,
            ctx,
            constraints,
            "not_zero_for_gen",
        );
        let is_general_case_cond_pt1 = fp_logical_and(
            &not_special_scenario_intermediate1,
            &not_special_scenario_intermediate2,
            ctx,
            constraints,
            "gen_case_pt1",
        );
        let is_general_case_condition = fp_logical_and(
            &is_general_case_cond_pt1,
            &not_special_scenario_intermediate3,
            ctx,
            constraints,
            "is_general_case",
        );

        let implicit_mant_bit_pos = mant_bit_count;

        let all_ones_exp_biased = (1u128 << exp_bit_count) - 1;
        let min_exp_biased_val = 1u128;
        let zero_exp_biased_val = 0u128;

        let op1_is_denormal = fp_is_value_equal(
            &op1_e_val_expr,
            &AirExpression::Constant(zero_exp_biased_val),
            ctx,
            constraints,
            "op1_is_denorm_e_check",
        );
        let op2_is_denormal = fp_is_value_equal(
            &op2_e_val_expr,
            &AirExpression::Constant(zero_exp_biased_val),
            ctx,
            constraints,
            "op2_is_denorm_e_check",
        );

        let implicit_bit_val_op1 =
            fp_logical_not(&op1_is_denormal, ctx, constraints, "op1_implicit_bit");
        let implicit_bit_val_op2 =
            fp_logical_not(&op2_is_denormal, ctx, constraints, "op2_implicit_bit");

        let full_significand_op1 = fp_add(
            &op1_m_val_expr,
            &fp_mul(
                &implicit_bit_val_op1,
                &AirExpression::Constant(1u128 << implicit_mant_bit_pos),
                ctx,
                constraints,
                "op1_impl_shifted",
            ),
            ctx,
            constraints,
            "full_sig_op1",
        );
        let full_significand_op2 = fp_add(
            &op2_m_val_expr,
            &fp_mul(
                &implicit_bit_val_op2,
                &AirExpression::Constant(1u128 << implicit_mant_bit_pos),
                ctx,
                constraints,
                "op2_impl_shifted",
            ),
            ctx,
            constraints,
            "full_sig_op2",
        );

        let effective_exp_op1 = fp_select(
            &op1_is_denormal,
            &AirExpression::Constant(min_exp_biased_val),
            &op1_e_val_expr,
            ctx,
            constraints,
            "eff_exp_op1",
        );
        let effective_exp_op2 = fp_select(
            &op2_is_denormal,
            &AirExpression::Constant(min_exp_biased_val),
            &op2_e_val_expr,
            ctx,
            constraints,
            "eff_exp_op2",
        );

        let op1_exp_lt_op2_exp = fp_icmp_ult(
            &effective_exp_op1,
            &effective_exp_op2,
            exp_bit_count + 1,
            ctx,
            constraints,
            "op1e_lt_op2e",
        );

        let e1_eff = fp_select(
            &op1_exp_lt_op2_exp,
            &effective_exp_op2,
            &effective_exp_op1,
            ctx,
            constraints,
            "e1_eff_sel",
        );
        let e2_eff = fp_select(
            &op1_exp_lt_op2_exp,
            &effective_exp_op1,
            &effective_exp_op2,
            ctx,
            constraints,
            "e2_eff_sel",
        );
        let sig1_full = fp_select(
            &op1_exp_lt_op2_exp,
            &full_significand_op2,
            &full_significand_op1,
            ctx,
            constraints,
            "sig1_sel",
        );
        let sig2_full = fp_select(
            &op1_exp_lt_op2_exp,
            &full_significand_op1,
            &full_significand_op2,
            ctx,
            constraints,
            "sig2_sel",
        );
        let s1_orig = fp_select(
            &op1_exp_lt_op2_exp,
            &op2_s_expr,
            &op1_s_expr,
            ctx,
            constraints,
            "s1_orig_sel",
        );
        let s2_orig = fp_select(
            &op1_exp_lt_op2_exp,
            &op1_s_expr,
            &op2_s_expr,
            ctx,
            constraints,
            "s2_orig_sel",
        );

        let exp_diff = fp_sub(&e1_eff, &e2_eff, ctx, constraints, "exp_diff");
        let final_calc_exp_biased = e1_eff.clone();

        let (sig2_aligned, _guard_bit, _round_bit, _sticky_bit) = fp_variable_right_shift_with_grs(
            &sig2_full,
            &exp_diff,
            mant_bit_count + 1,
            mant_bit_count + 3,
            ctx,
            constraints,
            "sig2_align_shift",
        );

        let effective_op_is_sub =
            fp_icmp_neq(&s1_orig, &s2_orig, ctx, constraints, "eff_op_is_sub");

        let sig1_lt_sig2_aligned = fp_icmp_ult(
            &sig1_full,
            &sig2_aligned,
            mant_bit_count + 3,
            ctx,
            constraints,
            "sig1_lt_sig2a_for_sub",
        );

        let diff_sig1_minus_sig2 = fp_sub(
            &sig1_full,
            &sig2_aligned,
            ctx,
            constraints,
            "diff_s1_minus_s2",
        );
        let diff_sig2_minus_sig1 = fp_sub(
            &sig2_aligned,
            &sig1_full,
            ctx,
            constraints,
            "diff_s2_minus_s1",
        );

        let sub_magnitude = fp_select(
            &sig1_lt_sig2_aligned,
            &diff_sig2_minus_sig1,
            &diff_sig1_minus_sig2,
            ctx,
            constraints,
            "sub_magnitude",
        );
        let sub_sign = fp_select(
            &sig1_lt_sig2_aligned,
            &s2_orig,
            &s1_orig,
            ctx,
            constraints,
            "sub_sign",
        );

        let add_magnitude = fp_add(&sig1_full, &sig2_aligned, ctx, constraints, "add_magnitude");
        let add_sign = s1_orig.clone();

        let intermediate_significand_val = fp_select(
            &effective_op_is_sub,
            &sub_magnitude,
            &add_magnitude,
            ctx,
            constraints,
            "intermediate_significand",
        );
        let result_sign_intermediate_val = fp_select(
            &effective_op_is_sub,
            &sub_sign,
            &add_sign,
            ctx,
            constraints,
            "result_sign_intermediate",
        );

        let (
            normalized_sign,
            adjusted_biased_exp,
            normalized_significand,
            _is_true_zero_after_norm_round,
        ) = fp_normalize_and_round_significand(
            &intermediate_significand_val,
            &result_sign_intermediate_val,
            &final_calc_exp_biased,
            &_guard_bit,
            &_round_bit,
            &_sticky_bit,
            mant_bit_count,
            exp_bit_count,
            ctx,
            constraints,
            "fadd_norm_round",
        );

        let exp_overflows = fp_icmp_ule(
            &AirExpression::Constant(all_ones_exp_biased),
            &adjusted_biased_exp,
            exp_bit_count + 1,
            ctx,
            constraints,
            "exp_overflows",
        );
        let exp_underflows_to_zero = fp_icmp_ule(
            &adjusted_biased_exp,
            &AirExpression::Constant(zero_exp_biased_val),
            exp_bit_count + 1,
            ctx,
            constraints,
            "exp_underflows",
        );

        let gen_case_final_s = fp_select(
            &exp_overflows,
            &normalized_sign,
            &normalized_sign,
            ctx,
            constraints,
            "gen_s_ovf",
        );
        let gen_case_final_s = fp_select(
            &exp_underflows_to_zero,
            &normalized_sign,
            &gen_case_final_s,
            ctx,
            constraints,
            "gen_s_undf",
        );

        let gen_case_final_e = fp_select(
            &exp_overflows,
            &AirExpression::Constant(all_ones_exp_biased),
            &adjusted_biased_exp,
            ctx,
            constraints,
            "gen_e_ovf",
        );
        let gen_case_final_e = fp_select(
            &exp_underflows_to_zero,
            &AirExpression::Constant(zero_exp_biased_val),
            &gen_case_final_e,
            ctx,
            constraints,
            "gen_e_undf",
        );

        let gen_case_final_m = fp_select(
            &exp_overflows,
            &AirExpression::Constant(0),
            &normalized_significand,
            ctx,
            constraints,
            "gen_m_ovf",
        );
        let gen_case_final_m = fp_select(
            &exp_underflows_to_zero,
            &AirExpression::Constant(0),
            &gen_case_final_m,
            ctx,
            constraints,
            "gen_m_undf",
        );

        let gen_s_val_diff = fp_sub(
            &general_case_res_s_expr,
            &gen_case_final_s,
            ctx,
            constraints,
            "gen_s_val_diff",
        );
        let gen_s_constraint = fp_mul(
            &is_general_case_condition,
            &gen_s_val_diff,
            ctx,
            constraints,
            "gen_s_constr_mul",
        );
        constraints.push(gen_s_constraint);

        let gen_e_val_diff = fp_sub(
            &general_case_res_e_expr,
            &gen_case_final_e,
            ctx,
            constraints,
            "gen_e_val_diff",
        );
        let gen_e_constraint = fp_mul(
            &is_general_case_condition,
            &gen_e_val_diff,
            ctx,
            constraints,
            "gen_e_constr_mul",
        );
        constraints.push(gen_e_constraint);

        let gen_m_val_diff = fp_sub(
            &general_case_res_m_expr,
            &gen_case_final_m,
            ctx,
            constraints,
            "gen_m_val_diff",
        );
        let gen_m_constraint = fp_mul(
            &is_general_case_condition,
            &gen_m_val_diff,
            ctx,
            constraints,
            "gen_m_constr_mul",
        );
        constraints.push(gen_m_constraint);
    }
}

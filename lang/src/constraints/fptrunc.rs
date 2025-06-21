use crate::constraints::{AirExpression, AirTraceVariable, RowOffset};
use crate::utils::*;
use crate::{constraints::ResolveConstraint, ConstraintSystemVariable, Operand};

#[derive(Debug, Clone)]
pub struct FpTrunc {
    pub operand: Operand,
    pub result: ConstraintSystemVariable,
    pub operand_bitwidth: u32,
    pub result_bitwidth: u32,
    pub block_name: String,
}

impl ResolveConstraint for FpTrunc {
    fn resolve(
        &self,
        constraints: &mut Vec<super::AirExpression>,
        ctx: &mut crate::ctx::AirGenContext,
        phi_condition_map: &std::collections::HashMap<(String, String), ConstraintSystemVariable>,
        switch_instructions: &Vec<crate::StructuredAirConstraint>,
    ) {
        let reg_col_opt = ctx.col_for_ssa(self.result);

        let dest_col = ctx.new_aux_variable();
        ctx.bind_ssa_var(self.result, dest_col.0);

        println!(
            "  FPTRUNC: op={:?}, res={:?} (dest col {:?}, bitwidth {}) - Setting up S/E/M aux vars.",
            self.operand, self.result, dest_col, self.operand_bitwidth
        );

        let (s_bit_count, exp_bit_count, mant_bit_count) = match self.operand_bitwidth {
            16 => (1u32, 5u32, 10u32),
            32 => (1u32, 8u32, 23u32),
            64 => (1u32, 11u32, 52u32),
            80 => (1u32, 15u32, 63u32),
            128 => (1u32, 15u32, 112u32),
            _ => panic!(
                "Unsupported operand_bitwidth {} for FAdd S/E/M decomposition.",
                self.operand_bitwidth
            ),
        };

        let (res_s_bit_count, res_exp_bit_count, res_mant_bit_count) = match self.result_bitwidth {
            16 => (1u32, 5u32, 10u32),
            32 => (1u32, 8u32, 23u32),
            64 => (1u32, 11u32, 52u32),
            80 => (1u32, 15u32, 63u32),
            128 => (1u32, 15u32, 112u32),
            _ => panic!(
                "Unsupported result_bitwidth {} for FPTrunc S/E/M decomposition.",
                self.result_bitwidth
            ),
        };

        let (op_s_var, op_e_var, op_m_var) = setup_sem_aux_vars(
            self.operand,
            "op",
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
            res_s_bit_count,
            res_exp_bit_count,
            res_mant_bit_count,
            constraints,
        );

        let op_s_expr = AirExpression::Trace(op_s_var, RowOffset::Current);
        let op_e_expr = AirExpression::Trace(op_e_var, RowOffset::Current);
        let op_m_expr = AirExpression::Trace(op_m_var, RowOffset::Current);
        let res_s_expr = AirExpression::Trace(res_s_var, RowOffset::Current);
        let res_e_expr = AirExpression::Trace(res_e_var, RowOffset::Current);
        let res_m_expr = AirExpression::Trace(res_m_var, RowOffset::Current);

        let op_is_nan = fp_is_nan(
            &op_e_expr,
            &op_m_expr,
            exp_bit_count,
            mant_bit_count,
            ctx,
            constraints,
            "op_fptrunc_nan",
        );
        let op_is_inf = fp_is_inf(
            &op_e_expr,
            &op_m_expr,
            exp_bit_count,
            mant_bit_count,
            ctx,
            constraints,
            "op_fptrunc_inf",
        );
        let op_is_true_zero = fp_is_true_zero(
            &op_e_expr,
            &op_m_expr,
            exp_bit_count,
            mant_bit_count,
            ctx,
            constraints,
            "op_fptrunc_zero",
        );

        let res_qnan_sign = AirExpression::Constant(0);
        let res_qnan_exp = AirExpression::Constant((1u128 << res_exp_bit_count) - 1);
        let res_qnan_mant = AirExpression::Constant(1u128 << (res_mant_bit_count - 1));

        let res_inf_sign = op_s_expr.clone();
        let res_inf_exp = res_qnan_exp.clone();
        let res_inf_mant = AirExpression::Constant(0);

        let res_zero_sign = op_s_expr.clone();
        let res_zero_exp = AirExpression::Constant(0);
        let res_zero_mant = AirExpression::Constant(0);

        let op_bias_val = (1u128 << (exp_bit_count - 1)) - 1;
        let res_bias_val = (1u128 << (res_exp_bit_count - 1)) - 1;

        let op_is_denormal = fp_is_value_equal(
            &op_e_expr,
            &AirExpression::Constant(0),
            ctx,
            constraints,
            "op_is_denorm_e_check_fptrunc",
        );
        let implicit_bit_val_op =
            fp_logical_not(&op_is_denormal, ctx, constraints, "op_implicit_bit_fptrunc");
        let full_significand_op = fp_add(
            &op_m_expr,
            &fp_mul(
                &implicit_bit_val_op,
                &AirExpression::Constant(1u128 << mant_bit_count),
                ctx,
                constraints,
                "op_impl_shifted_fptrunc",
            ),
            ctx,
            constraints,
            "full_sig_op_fptrunc",
        );

        let effective_exp_op = fp_select(
            &op_is_denormal,
            &AirExpression::Constant(1),
            &op_e_expr,
            ctx,
            constraints,
            "eff_exp_op_fptrunc",
        );
        let unbiased_exp_op = fp_sub(
            &effective_exp_op,
            &AirExpression::Constant(op_bias_val),
            ctx,
            constraints,
            "unbiased_e_op_fptrunc",
        );
        let initial_biased_exp_for_norm = fp_add(
            &unbiased_exp_op,
            &AirExpression::Constant(res_bias_val),
            ctx,
            constraints,
            "init_biased_exp_res_fptrunc",
        );

        let (gen_case_s_val, gen_case_e_val, gen_case_m_val, _) =
            fp_normalize_and_round_significand(
                &full_significand_op,
                &op_s_expr,
                &initial_biased_exp_for_norm,
                &AirExpression::Constant(0),
                &AirExpression::Constant(0),
                &AirExpression::Constant(0),
                res_mant_bit_count,
                res_exp_bit_count,
                ctx,
                constraints,
                "fptrunc_norm_round",
            );

        let s_if_not_inf = fp_select(
            &op_is_true_zero,
            &res_zero_sign,
            &gen_case_s_val,
            ctx,
            constraints,
            "s_zero_vs_gen_fptrunc",
        );
        let e_if_not_inf = fp_select(
            &op_is_true_zero,
            &res_zero_exp,
            &gen_case_e_val,
            ctx,
            constraints,
            "e_zero_vs_gen_fptrunc",
        );
        let m_if_not_inf = fp_select(
            &op_is_true_zero,
            &res_zero_mant,
            &gen_case_m_val,
            ctx,
            constraints,
            "m_zero_vs_gen_fptrunc",
        );

        let s_if_not_nan = fp_select(
            &op_is_inf,
            &res_inf_sign,
            &s_if_not_inf,
            ctx,
            constraints,
            "s_inf_vs_else_fptrunc",
        );
        let e_if_not_nan = fp_select(
            &op_is_inf,
            &res_inf_exp,
            &e_if_not_inf,
            ctx,
            constraints,
            "e_inf_vs_else_fptrunc",
        );
        let m_if_not_nan = fp_select(
            &op_is_inf,
            &res_inf_mant,
            &m_if_not_inf,
            ctx,
            constraints,
            "m_inf_vs_else_fptrunc",
        );

        let final_res_s_val = fp_select(
            &op_is_nan,
            &res_qnan_sign,
            &s_if_not_nan,
            ctx,
            constraints,
            "s_nan_vs_else_fptrunc",
        );
        let final_res_e_val = fp_select(
            &op_is_nan,
            &res_qnan_exp,
            &e_if_not_nan,
            ctx,
            constraints,
            "e_nan_vs_else_fptrunc",
        );
        let final_res_m_val = fp_select(
            &op_is_nan,
            &res_qnan_mant,
            &m_if_not_nan,
            ctx,
            constraints,
            "m_nan_vs_else_fptrunc",
        );

        let res_s_final_constraint =
            AirExpression::Sub(Box::new(res_s_expr), Box::new(final_res_s_val));
        let res_e_final_constraint =
            AirExpression::Sub(Box::new(res_e_expr), Box::new(final_res_e_val));
        let res_m_final_constraint =
            AirExpression::Sub(Box::new(res_m_expr), Box::new(final_res_m_val));

        constraints.push(res_s_final_constraint);
        constraints.push(res_e_final_constraint);
        constraints.push(res_m_final_constraint);
        println!("      FPTRUNC: Main constraint added.");

        if let Some(reg_col) = reg_col_opt {
            let selector = ctx.new_row_selector();
            let dest_expr = AirExpression::Trace(dest_col.clone(), RowOffset::Current);
            let reg_expr = AirExpression::Trace(AirTraceVariable(reg_col), RowOffset::Current);
            let diff = AirExpression::Sub(Box::new(dest_expr), Box::new(reg_expr));
            ctx.add_row_gated_constraint(selector, diff);
        }
    }
}

use crate::constraints::{AirExpression, RowOffset};
use crate::utils::*;
use crate::{constraints::ResolveConstraint, ConstraintSystemVariable, Operand};

#[derive(Debug, Clone)]
pub struct FRem {
    pub operand1: Operand,
    pub operand2: Operand,
    pub result: ConstraintSystemVariable,
    pub operand_bitwidth: u32,
    pub block_name: String,
}

impl ResolveConstraint for FRem {
    fn resolve(
        &self,
        constraints: &mut Vec<super::AirExpression>,
        ctx: &mut crate::ctx::AirGenContext,
        phi_condition_map: &std::collections::HashMap<(String, String), ConstraintSystemVariable>,
        switch_instructions: &Vec<crate::StructuredAirConstraint>,
    ) {
        println!(
            "  FREM: op1={:?}, op2={:?}, res={:?} (bitwidth {}) - Setting up S/E/M aux vars.",
            self.operand1, self.operand2, self.result, self.operand_bitwidth
        );

        let (s_bit_count, exp_bit_count, mant_bit_count) = match self.operand_bitwidth {
            16 => (1u32, 5u32, 10u32),
            32 => (1u32, 8u32, 23u32),
            64 => (1u32, 11u32, 52u32),
            80 => (1u32, 15u32, 63u32),
            128 => (1u32, 15u32, 112u32),
            _ => panic!(
                "Unsupported self.operand_bitwidth {} for FRem S/E/M decomposition.",
                self.operand_bitwidth
            ),
        };

        let (op1_s_var, op1_e_var, op1_m_var) = setup_sem_aux_vars(
            self.operand1,
            "op1_frem",
            ctx,
            s_bit_count,
            exp_bit_count,
            mant_bit_count,
            constraints,
        );
        let (_op2_s_var, op2_e_var, op2_m_var) = setup_sem_aux_vars(
            self.operand2,
            "op2_frem",
            ctx,
            s_bit_count,
            exp_bit_count,
            mant_bit_count,
            constraints,
        );
        let (res_s_var, res_e_var, res_m_var) = setup_sem_aux_vars(
            Operand::Var(self.result),
            "res_frem",
            ctx,
            s_bit_count,
            exp_bit_count,
            mant_bit_count,
            constraints,
        );

        let op1_s_expr = AirExpression::Trace(op1_s_var, RowOffset::Current);
        let op1_e_val_expr = AirExpression::Trace(op1_e_var, RowOffset::Current);
        let op1_m_val_expr = AirExpression::Trace(op1_m_var, RowOffset::Current);

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
            "op1_frem",
        );
        let op2_is_nan = fp_is_nan(
            &op2_e_val_expr,
            &op2_m_val_expr,
            exp_bit_count,
            mant_bit_count,
            ctx,
            constraints,
            "op2_frem",
        );

        let op1_is_inf = fp_is_inf(
            &op1_e_val_expr,
            &op1_m_val_expr,
            exp_bit_count,
            mant_bit_count,
            ctx,
            constraints,
            "op1_frem",
        );
        let op2_is_inf = fp_is_inf(
            &op2_e_val_expr,
            &op2_m_val_expr,
            exp_bit_count,
            mant_bit_count,
            ctx,
            constraints,
            "op2_frem",
        );

        let op1_is_true_zero = fp_is_true_zero(
            &op1_e_val_expr,
            &op1_m_val_expr,
            exp_bit_count,
            mant_bit_count,
            ctx,
            constraints,
            "op1_frem",
        );
        let op2_is_true_zero = fp_is_true_zero(
            &op2_e_val_expr,
            &op2_m_val_expr,
            exp_bit_count,
            mant_bit_count,
            ctx,
            constraints,
            "op2_frem",
        );

        let qnan_sign = AirExpression::Constant(0);
        let qnan_exp = AirExpression::Constant((1u128 << exp_bit_count) - 1);
        let qnan_mant = AirExpression::Constant(1u128 << (mant_bit_count - 1));

        let res_is_nan_from_op = fp_logical_or(
            &op1_is_nan,
            &op2_is_nan,
            ctx,
            constraints,
            "res_nan_from_op_frem",
        );

        let res_is_nan_undef = fp_logical_or(
            &op1_is_inf,
            &op2_is_true_zero,
            ctx,
            constraints,
            "res_nan_undef_frem",
        );
        let final_res_is_nan = fp_logical_or(
            &res_is_nan_from_op,
            &res_is_nan_undef,
            ctx,
            constraints,
            "final_res_is_nan_frem",
        );

        let op1_is_finite = fp_logical_not(
            &fp_logical_or(
                &op1_is_nan,
                &op1_is_inf,
                ctx,
                constraints,
                "op1_nan_or_inf_frem",
            ),
            ctx,
            constraints,
            "op1_is_finite_frem",
        );
        let is_op1_result_scenario = fp_logical_and(
            &op1_is_finite,
            &op2_is_inf,
            ctx,
            constraints,
            "is_op1_res_scenario_frem",
        );

        let is_zero_result_scenario = op1_is_true_zero.clone();

        let inter_res_s_if_op1 = op1_s_expr.clone();
        let inter_res_e_if_op1 = op1_e_val_expr.clone();
        let inter_res_m_if_op1 = op1_m_val_expr.clone();

        let inter_res_s_if_zero = op1_s_expr.clone();
        let inter_res_e_if_zero = AirExpression::Constant(0);
        let inter_res_m_if_zero = AirExpression::Constant(0);

        let res_s_if_not_nan = fp_select(
            &is_op1_result_scenario,
            &inter_res_s_if_op1,
            &res_s_expr,
            ctx,
            constraints,
            "s_not_nan_op1_vs_else_frem",
        );
        let res_e_if_not_nan = fp_select(
            &is_op1_result_scenario,
            &inter_res_e_if_op1,
            &res_e_val_expr,
            ctx,
            constraints,
            "e_not_nan_op1_vs_else_frem",
        );
        let res_m_if_not_nan = fp_select(
            &is_op1_result_scenario,
            &inter_res_m_if_op1,
            &res_m_val_expr,
            ctx,
            constraints,
            "m_not_nan_op1_vs_else_frem",
        );

        let res_s_if_not_nan_zero = fp_select(
            &is_zero_result_scenario,
            &inter_res_s_if_zero,
            &res_s_if_not_nan,
            ctx,
            constraints,
            "s_not_nan_zero_vs_else_frem",
        );
        let res_e_if_not_nan_zero = fp_select(
            &is_zero_result_scenario,
            &inter_res_e_if_zero,
            &res_e_if_not_nan,
            ctx,
            constraints,
            "e_not_nan_zero_vs_else_frem",
        );
        let res_m_if_not_nan_zero = fp_select(
            &is_zero_result_scenario,
            &inter_res_m_if_zero,
            &res_m_if_not_nan,
            ctx,
            constraints,
            "m_not_nan_zero_vs_else_frem",
        );

        let final_res_s_val = fp_select(
            &final_res_is_nan,
            &qnan_sign,
            &res_s_if_not_nan_zero,
            ctx,
            constraints,
            "final_s_frem",
        );
        let final_res_e_val = fp_select(
            &final_res_is_nan,
            &qnan_exp,
            &res_e_if_not_nan_zero,
            ctx,
            constraints,
            "final_e_frem",
        );
        let final_res_m_val = fp_select(
            &final_res_is_nan,
            &qnan_mant,
            &res_m_if_not_nan_zero,
            ctx,
            constraints,
            "final_m_frem",
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
            "not_final_nan_for_gen_frem",
        );
        let not_op1_res_cond = fp_logical_not(
            &is_op1_result_scenario,
            ctx,
            constraints,
            "not_op1_res_for_gen_frem",
        );
        let not_zero_res_cond = fp_logical_not(
            &is_zero_result_scenario,
            ctx,
            constraints,
            "not_zero_res_for_gen_frem",
        );
        let is_general_case_cond_pt1 = fp_logical_and(
            &not_final_nan_cond,
            &not_op1_res_cond,
            ctx,
            constraints,
            "gen_case_pt1_frem",
        );
        let is_general_case_condition = fp_logical_and(
            &is_general_case_cond_pt1,
            &not_zero_res_cond,
            ctx,
            constraints,
            "is_general_case_frem",
        );

        let sign_diff = fp_sub(&res_s_expr, &op1_s_expr, ctx, constraints, "sign_diff_frem");
        let sign_constraint = fp_mul(
            &is_general_case_condition,
            &sign_diff,
            ctx,
            constraints,
            "sign_constr_frem",
        );
        constraints.push(sign_constraint);

        let rem_abs_val = fp_add(
            &fp_mul(
                &res_e_val_expr,
                &AirExpression::Constant(1u128 << mant_bit_count),
                ctx,
                constraints,
                "rem_e_shifted_frem",
            ),
            &res_m_val_expr,
            ctx,
            constraints,
            "rem_abs_val_frem",
        );
        let op2_abs_val = fp_add(
            &fp_mul(
                &op2_e_val_expr,
                &AirExpression::Constant(1u128 << mant_bit_count),
                ctx,
                constraints,
                "op2_e_shifted_frem",
            ),
            &op2_m_val_expr,
            ctx,
            constraints,
            "op2_abs_val_frem",
        );

        let abs_rem_lt_abs_op2 = fp_icmp_ult(
            &rem_abs_val,
            &op2_abs_val,
            mant_bit_count + exp_bit_count,
            ctx,
            constraints,
            "abs_rem_lt_abs_op2_frem",
        );
        let lt_check_diff = fp_sub(
            &abs_rem_lt_abs_op2,
            &AirExpression::Constant(1),
            ctx,
            constraints,
            "lt_check_diff_frem",
        );
        let lt_constraint = fp_mul(
            &is_general_case_condition,
            &lt_check_diff,
            ctx,
            constraints,
            "lt_constr_frem",
        );
        constraints.push(lt_constraint);
    }
}

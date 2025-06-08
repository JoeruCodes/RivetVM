use std::collections::HashMap;

use crate::utils::*;
use crate::{
    constraints::{AirExpression, ResolveConstraint, RowOffset},
    ConstraintSystemVariable, Operand, StructuredAirConstraint,
};

#[derive(Debug, Clone)]
pub struct FpExt {
    pub operand: Operand,
    pub result: ConstraintSystemVariable,
    pub operand_bitwidth: u32,
    pub result_bitwidth: u32,
    pub block_name: String,
}

impl ResolveConstraint for FpExt {
    fn resolve(
        &self,
        constraints: &mut Vec<super::AirExpression>,
        ctx: &mut crate::ctx::AirGenContext,
        phi_condition_map: &HashMap<(String, String), ConstraintSystemVariable>,
        switch_instructions: &Vec<StructuredAirConstraint>,
    ) {
        let (op_s_bits, op_e_bits, op_m_bits) = match self.operand_bitwidth {
            32 => (1, 8, 23),
            16 => (1, 5, 10),
            _ => panic!("Unsupported FP bitwidth for FPExt operand"),
        };
        let op_bias = (1u128 << (op_e_bits - 1)) - 1;

        let (res_s_bits, res_e_bits, res_m_bits) = match self.result_bitwidth {
            64 => (1, 11, 52),
            32 => (1, 8, 23),
            _ => panic!("Unsupported FP bitwidth for FPExt result"),
        };
        let res_bias = (1u128 << (res_e_bits - 1)) - 1;
        let res_e_max = (1u128 << res_e_bits) - 1;

        let (op_s_var, op_e_var, op_m_var) = setup_sem_aux_vars(
            self.operand,
            "op_fpext",
            ctx,
            op_s_bits,
            op_e_bits,
            op_m_bits,
            constraints,
        );
        let op_s_expr = AirExpression::Trace(op_s_var, RowOffset::Current);
        let op_e_expr = AirExpression::Trace(op_e_var, RowOffset::Current);
        let op_m_expr = AirExpression::Trace(op_m_var, RowOffset::Current);

        let (res_s_var, res_e_var, res_m_var) = setup_sem_aux_vars(
            Operand::Var(self.result),
            "res_fpext",
            ctx,
            res_s_bits,
            res_e_bits,
            res_m_bits,
            constraints,
        );
        let res_s_expr = AirExpression::Trace(res_s_var, RowOffset::Current);
        let res_e_expr = AirExpression::Trace(res_e_var, RowOffset::Current);
        let res_m_expr = AirExpression::Trace(res_m_var, RowOffset::Current);

        constraints.push(AirExpression::Sub(
            Box::new(res_s_expr.clone()),
            Box::new(op_s_expr.clone()),
        ));

        let is_op_zero = fp_is_true_zero(
            &op_e_expr,
            &op_m_expr,
            op_e_bits,
            op_m_bits,
            ctx,
            constraints,
            "fpext_op_is_zero",
        );
        let is_op_inf = fp_is_inf(
            &op_e_expr,
            &op_m_expr,
            op_e_bits,
            op_m_bits,
            ctx,
            constraints,
            "fpext_op_is_inf",
        );
        let is_op_nan = fp_is_nan(
            &op_e_expr,
            &op_m_expr,
            op_e_bits,
            op_m_bits,
            ctx,
            constraints,
            "fpext_op_is_nan",
        );

        let is_op_denormal = fp_is_value_zero(&op_e_expr, ctx, constraints, "fpext_op_is_denormal");
        let op_implicit_bit =
            fp_logical_not(&is_op_denormal, ctx, constraints, "fpext_op_implicit_bit");
        let op_full_significand = fp_add(
            &op_m_expr,
            &fp_mul(
                &op_implicit_bit,
                &AirExpression::Constant(1u128 << op_m_bits),
                ctx,
                constraints,
                "fpext_op_full_sig",
            ),
            ctx,
            constraints,
            "fpext_op_full_sig_add",
        );

        let op_effective_exp = fp_select(
            &is_op_denormal,
            &AirExpression::Constant(1),
            &op_e_expr,
            ctx,
            constraints,
            "fpext_op_eff_exp",
        );

        let unbiased_exp = fp_sub(
            &op_effective_exp,
            &AirExpression::Constant(op_bias),
            ctx,
            constraints,
            "fpext_unbias",
        );

        let res_e_general = fp_add(
            &unbiased_exp,
            &AirExpression::Constant(res_bias),
            ctx,
            constraints,
            "fpext_rebias",
        );

        let mantissa_shift_amount = res_m_bits - op_m_bits;
        let res_m_general = fp_mul(
            &op_full_significand,
            &AirExpression::Constant(1u128 << mantissa_shift_amount),
            ctx,
            constraints,
            "fpext_m_shift",
        );

        let res_e_if_zero = AirExpression::Constant(0);
        let res_m_if_zero = AirExpression::Constant(0);

        let res_e_if_inf = AirExpression::Constant(res_e_max);
        let res_m_if_inf = AirExpression::Constant(0);

        let res_e_if_nan = AirExpression::Constant(res_e_max);

        let res_m_if_nan = fp_mul(
            &op_m_expr,
            &AirExpression::Constant(1u128 << mantissa_shift_amount),
            ctx,
            constraints,
            "fpext_nan_m_shift",
        );

        let res_e_1 = fp_select(
            &is_op_zero,
            &res_e_if_zero,
            &res_e_general,
            ctx,
            constraints,
            "fpext_sel_e_1",
        );
        let res_m_1 = fp_select(
            &is_op_zero,
            &res_m_if_zero,
            &res_m_general,
            ctx,
            constraints,
            "fpext_sel_m_1",
        );

        let res_e_2 = fp_select(
            &is_op_inf,
            &res_e_if_inf,
            &res_e_1,
            ctx,
            constraints,
            "fpext_sel_e_2",
        );
        let res_m_2 = fp_select(
            &is_op_inf,
            &res_m_if_inf,
            &res_m_1,
            ctx,
            constraints,
            "fpext_sel_m_2",
        );

        let final_e = fp_select(
            &is_op_nan,
            &res_e_if_nan,
            &res_e_2,
            ctx,
            constraints,
            "fpext_sel_e_final",
        );
        let final_m = fp_select(
            &is_op_nan,
            &res_m_if_nan,
            &res_m_2,
            ctx,
            constraints,
            "fpext_sel_m_final",
        );

        constraints.push(AirExpression::Sub(Box::new(res_e_expr), Box::new(final_e)));
        constraints.push(AirExpression::Sub(Box::new(res_m_expr), Box::new(final_m)));
    }
}

use std::collections::HashMap;

use crate::constraints::{AirExpression, AirTraceVariable, RowOffset};
use crate::{constraints::ResolveConstraint, ConstraintSystemVariable, Operand};
use crate::{utils::*, StructuredAirConstraint};

#[derive(Debug, Clone)]
pub struct FpToUi {
    operand: Operand,
    result: ConstraintSystemVariable,
    operand_bitwidth: u32,
    result_bitwidth: u32,
    block_name: String,
}

impl ResolveConstraint for FpToUi {
    fn resolve(
        &self,
        constraints: &mut Vec<super::AirExpression>,
        ctx: &mut crate::ctx::AirGenContext,
        phi_condition_map: &HashMap<(String, String), ConstraintSystemVariable>,
        switch_instructions: &Vec<StructuredAirConstraint>,
    ) {
        println!(
            "  FPTOUI: op={:?}, res={:?}, op_bw={}, res_bw={}",
            self.operand, self.result, self.operand_bitwidth, self.result_bitwidth
        );

        let (s_fp_bits, e_fp_bits, m_fp_bits) = match self.operand_bitwidth {
            32 => (1, 8, 23),
            64 => (1, 11, 52),
            _ => panic!("Unsupported FP bitwidth for FPToUI"),
        };
        let (op_s_var, op_e_var, op_m_var) = setup_sem_aux_vars(
            self.operand,
            "op_fptoui",
            ctx,
            s_fp_bits,
            e_fp_bits,
            m_fp_bits,
            constraints,
        );
        let op_s_expr = AirExpression::Trace(op_s_var, RowOffset::Current);
        let op_e_expr = AirExpression::Trace(op_e_var, RowOffset::Current);
        let op_m_expr = AirExpression::Trace(op_m_var, RowOffset::Current);
        let res_expr = AirExpression::Trace(AirTraceVariable(self.result.0), RowOffset::Current);

        let is_nan = fp_is_nan(
            &op_e_expr,
            &op_m_expr,
            e_fp_bits,
            m_fp_bits,
            ctx,
            constraints,
            "fptoui_nan",
        );
        let is_inf = fp_is_inf(
            &op_e_expr,
            &op_m_expr,
            e_fp_bits,
            m_fp_bits,
            ctx,
            constraints,
            "fptoui_inf",
        );
        let is_special = fp_logical_or(&is_nan, &is_inf, ctx, constraints, "fptoui_special");

        let is_neg = op_s_expr.clone();
        let is_invalid = fp_logical_or(&is_special, &is_neg, ctx, constraints, "fptoui_invalid");

        let bias = (1u128 << (e_fp_bits - 1)) - 1;
        let is_denormal = fp_is_value_zero(&op_e_expr, ctx, constraints, "fptoui_denorm");
        let implicit_bit = fp_logical_not(&is_denormal, ctx, constraints, "fptoui_impl_bit");
        let full_significand = fp_add(
            &op_m_expr,
            &fp_mul(
                &implicit_bit,
                &AirExpression::Constant(1u128 << m_fp_bits),
                ctx,
                constraints,
                "fptoui_full_sig_add",
            ),
            ctx,
            constraints,
            "fptoui_full_sig",
        );
        let effective_exp = fp_select(
            &is_denormal,
            &AirExpression::Constant(1),
            &op_e_expr,
            ctx,
            constraints,
            "fptoui_eff_exp",
        );

        let shift_threshold = bias + m_fp_bits as u128;
        let is_left_shift = fp_icmp_uge(
            &effective_exp,
            &AirExpression::Constant(shift_threshold),
            e_fp_bits + 1,
            ctx,
            constraints,
            "fptoui_is_left",
        );

        let left_shift_amount = fp_sub(
            &effective_exp,
            &AirExpression::Constant(shift_threshold),
            ctx,
            constraints,
            "fptoui_lshift",
        );
        let right_shift_amount = fp_sub(
            &AirExpression::Constant(shift_threshold),
            &effective_exp,
            ctx,
            constraints,
            "fptoui_rshift",
        );

        let left_shifted_val = {
            let power_of_2 = fp_power_of_2(
                &left_shift_amount,
                e_fp_bits + m_fp_bits + 2,
                ctx,
                constraints,
                "fptoui_lshift_pow2",
            );
            fp_mul(
                &full_significand,
                &power_of_2,
                ctx,
                constraints,
                "fptoui_lshift_res",
            )
        };
        let right_shifted_val = {
            let (quotient, _rem) = fp_variable_division(
                &full_significand,
                &right_shift_amount,
                m_fp_bits + 1,
                m_fp_bits + 1 + e_fp_bits,
                ctx,
                constraints,
                "fptoui_rshift",
            );
            quotient
        };

        let general_case_res = fp_select(
            &is_left_shift,
            &left_shifted_val,
            &right_shifted_val,
            ctx,
            constraints,
            "fptoui_abs_val",
        );

        let final_res = fp_select(
            &is_invalid,
            &AirExpression::Constant(0),
            &general_case_res,
            ctx,
            constraints,
            "fptoui_final_res",
        );
        constraints.push(AirExpression::Sub(
            Box::new(res_expr.clone()),
            Box::new(final_res),
        ));

        ctx.add_unsigned_range_proof_constraints(res_expr, self.result_bitwidth);
    }
}

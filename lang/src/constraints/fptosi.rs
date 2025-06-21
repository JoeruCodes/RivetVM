use std::collections::HashMap;

use crate::constraints::{AirExpression, AirTraceVariable, RowOffset};
use crate::{constraints::ResolveConstraint, ConstraintSystemVariable, Operand};
use crate::{utils::*, StructuredAirConstraint};

#[derive(Debug, Clone)]
pub struct FpToSi {
    pub operand: Operand,
    pub result: ConstraintSystemVariable,
    pub operand_bitwidth: u32,
    pub result_bitwidth: u32,
    pub block_name: String,
}

impl ResolveConstraint for FpToSi {
    fn resolve(
        &self,
        constraints: &mut Vec<super::AirExpression>,
        ctx: &mut crate::ctx::AirGenContext,
        phi_condition_map: &HashMap<(String, String), ConstraintSystemVariable>,
        switch_instructions: &Vec<StructuredAirConstraint>,
    ) {
        let reg_col_opt = ctx.col_for_ssa(self.result);
        let dest_col = ctx.new_aux_variable();
        ctx.bind_ssa_var(self.result, dest_col.0);

        println!(
            "  FPTOSI: op={:?}, res={:?} (dest col {:?}), op_bw={}, res_bw={}",
            self.operand, self.result, dest_col, self.operand_bitwidth, self.result_bitwidth
        );

        let (s_fp_bits, e_fp_bits, m_fp_bits) = match self.operand_bitwidth {
            32 => (1, 8, 23),
            64 => (1, 11, 52),
            _ => panic!("Unsupported FP bitwidth for FPToSI"),
        };
        let (op_s_var, op_e_var, op_m_var) = setup_sem_aux_vars(
            self.operand,
            "op_fptosi",
            ctx,
            s_fp_bits,
            e_fp_bits,
            m_fp_bits,
            constraints,
        );
        let op_s_expr = AirExpression::Trace(op_s_var, RowOffset::Current);
        let op_e_expr = AirExpression::Trace(op_e_var, RowOffset::Current);
        let op_m_expr = AirExpression::Trace(op_m_var, RowOffset::Current);
        let res_expr = AirExpression::Trace(dest_col, RowOffset::Current);

        let is_nan = fp_is_nan(
            &op_e_expr,
            &op_m_expr,
            e_fp_bits,
            m_fp_bits,
            ctx,
            constraints,
            "fptosi_nan",
        );
        let is_inf = fp_is_inf(
            &op_e_expr,
            &op_m_expr,
            e_fp_bits,
            m_fp_bits,
            ctx,
            constraints,
            "fptosi_inf",
        );
        let is_special = fp_logical_or(&is_nan, &is_inf, ctx, constraints, "fptosi_special");

        let bias = (1u128 << (e_fp_bits - 1)) - 1;
        let is_denormal = fp_is_value_zero(&op_e_expr, ctx, constraints, "fptosi_denorm");
        let implicit_bit = fp_logical_not(&is_denormal, ctx, constraints, "fptosi_impl_bit");
        let full_significand = fp_add(
            &op_m_expr,
            &fp_mul(
                &implicit_bit,
                &AirExpression::Constant(1u128 << m_fp_bits),
                ctx,
                constraints,
                "fptosi_full_sig_add",
            ),
            ctx,
            constraints,
            "fptosi_full_sig",
        );
        let effective_exp = fp_select(
            &is_denormal,
            &AirExpression::Constant(1),
            &op_e_expr,
            ctx,
            constraints,
            "fptosi_eff_exp",
        );

        let shift_threshold = bias + m_fp_bits as u128;
        let is_left_shift = fp_icmp_uge(
            &effective_exp,
            &AirExpression::Constant(shift_threshold),
            e_fp_bits + 1,
            ctx,
            constraints,
            "fptosi_is_left",
        );

        let left_shift_amount = fp_sub(
            &effective_exp,
            &AirExpression::Constant(shift_threshold),
            ctx,
            constraints,
            "fptosi_lshift",
        );
        let right_shift_amount = fp_sub(
            &AirExpression::Constant(shift_threshold),
            &effective_exp,
            ctx,
            constraints,
            "fptosi_rshift",
        );

        let left_shifted_val = {
            let power_of_2 = fp_power_of_2(
                &left_shift_amount,
                e_fp_bits + 1,
                ctx,
                constraints,
                "fptosi_lshift_pow2",
            );
            fp_mul(
                &full_significand,
                &power_of_2,
                ctx,
                constraints,
                "fptosi_lshift_res",
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
                "fptosi_rshift",
            );
            quotient
        };

        let abs_int_val = fp_select(
            &is_left_shift,
            &left_shifted_val,
            &right_shifted_val,
            ctx,
            constraints,
            "fptosi_abs_val",
        );

        let one_minus_2s = fp_sub(
            &AirExpression::Constant(1),
            &fp_mul(
                &AirExpression::Constant(2),
                &op_s_expr,
                ctx,
                constraints,
                "fptosi_2s",
            ),
            ctx,
            constraints,
            "fptosi_1_2s",
        );
        let general_case_res = fp_mul(
            &abs_int_val,
            &one_minus_2s,
            ctx,
            constraints,
            "fptosi_signed_res",
        );

        let final_res = fp_select(
            &is_special,
            &AirExpression::Constant(0),
            &general_case_res,
            ctx,
            constraints,
            "fptosi_final_res",
        );
        constraints.push(AirExpression::Sub(
            Box::new(res_expr.clone()),
            Box::new(final_res),
        ));

        ctx.add_signed_range_proof_constraints(res_expr.clone(), self.result_bitwidth);

        if let Some(reg_col) = reg_col_opt {
            let sel = ctx.new_row_selector();
            let reg_expr = AirExpression::Trace(AirTraceVariable(reg_col), RowOffset::Current);
            let diff = AirExpression::Sub(Box::new(res_expr), Box::new(reg_expr));
            ctx.add_row_gated_constraint(sel, diff);
        }
    }
}

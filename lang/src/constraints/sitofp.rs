use std::collections::HashMap;

use crate::constraints::{lang_operand_to_air_expression, AirExpression, RowOffset};
use crate::{constraints::ResolveConstraint, ConstraintSystemVariable, Operand};
use crate::{utils::*, StructuredAirConstraint};

#[derive(Debug, Clone)]
pub struct SiToFp {
    pub operand: Operand,
    pub result: ConstraintSystemVariable,
    pub operand_bitwidth: u32,
    pub result_bitwidth: u32,
    pub block_name: String,
}

impl ResolveConstraint for SiToFp {
    fn resolve(
        &self,
        constraints: &mut Vec<super::AirExpression>,
        ctx: &mut crate::ctx::AirGenContext,
        phi_condition_map: &HashMap<(String, String), ConstraintSystemVariable>,
        switch_instructions: &Vec<StructuredAirConstraint>,
    ) {
        println!(
            "  SITOFP: op={:?}, res={:?}, op_bw={}, res_bw={}",
            self.operand, self.result, self.operand_bitwidth, self.result_bitwidth
        );

        let (s_fp_bits, e_fp_bits, m_fp_bits) = match self.result_bitwidth {
            32 => (1, 8, 23),
            64 => (1, 11, 52),
            _ => panic!("Unsupported FP bitwidth for SIToFP"),
        };
        let (res_s_var, res_e_var, res_m_var) = setup_sem_aux_vars(
            Operand::Var(self.result),
            "res_sitofp",
            ctx,
            s_fp_bits,
            e_fp_bits,
            m_fp_bits,
            constraints,
        );
        let res_s_expr = AirExpression::Trace(res_s_var, RowOffset::Current);
        let res_e_expr = AirExpression::Trace(res_e_var, RowOffset::Current);
        let res_m_expr = AirExpression::Trace(res_m_var, RowOffset::Current);
        let op_expr = lang_operand_to_air_expression(self.operand);

        let (_op_bits, op_msb_expr_opt) =
            ctx.add_signed_range_proof_constraints(op_expr.clone(), self.operand_bitwidth);

        if let Some(op_msb_expr) = op_msb_expr_opt {
            constraints.push(AirExpression::Sub(
                Box::new(res_s_expr.clone()),
                Box::new(op_msb_expr),
            ));
        }

        let bias = (1u128 << (e_fp_bits - 1)) - 1;
        let is_denormal = fp_is_value_zero(&res_e_expr, ctx, constraints, "sitofp_denorm");
        let implicit_bit = fp_logical_not(&is_denormal, ctx, constraints, "sitofp_impl_bit");
        let full_significand = fp_add(
            &res_m_expr,
            &fp_mul(
                &implicit_bit,
                &AirExpression::Constant(1u128 << m_fp_bits),
                ctx,
                constraints,
                "sitofp_full_sig_add",
            ),
            ctx,
            constraints,
            "sitofp_full_sig",
        );
        let effective_exp = fp_select(
            &is_denormal,
            &AirExpression::Constant(1),
            &res_e_expr,
            ctx,
            constraints,
            "sitofp_eff_exp",
        );

        let shift_threshold = bias + m_fp_bits as u128;
        let is_left_shift = fp_icmp_uge(
            &effective_exp,
            &AirExpression::Constant(shift_threshold),
            e_fp_bits + 1,
            ctx,
            constraints,
            "sitofp_is_left",
        );

        let left_shift_amount = fp_sub(
            &effective_exp,
            &AirExpression::Constant(shift_threshold),
            ctx,
            constraints,
            "sitofp_lshift",
        );
        let right_shift_amount = fp_sub(
            &AirExpression::Constant(shift_threshold),
            &effective_exp,
            ctx,
            constraints,
            "sitofp_rshift",
        );

        let (left_shifted_val, left_shift_rem) = (
            {
                let power_of_2 = fp_power_of_2(
                    &left_shift_amount,
                    e_fp_bits + 1,
                    ctx,
                    constraints,
                    "sitofp_lshift_pow2",
                );
                fp_mul(
                    &full_significand,
                    &power_of_2,
                    ctx,
                    constraints,
                    "sitofp_lshift_res",
                )
            },
            AirExpression::Constant(0),
        );
        let (right_shifted_val, right_shift_rem) = fp_variable_division(
            &full_significand,
            &right_shift_amount,
            m_fp_bits + 1,
            m_fp_bits + 1 + e_fp_bits,
            ctx,
            constraints,
            "sitofp_rshift",
        );

        let abs_int_val = fp_select(
            &is_left_shift,
            &left_shifted_val,
            &right_shifted_val,
            ctx,
            constraints,
            "sitofp_abs_val",
        );
        let remainder = fp_select(
            &is_left_shift,
            &left_shift_rem,
            &right_shift_rem,
            ctx,
            constraints,
            "sitofp_rem",
        );

        let one_minus_2s = fp_sub(
            &AirExpression::Constant(1),
            &fp_mul(
                &AirExpression::Constant(2),
                &res_s_expr,
                ctx,
                constraints,
                "sitofp_2s",
            ),
            ctx,
            constraints,
            "sitofp_1_2s",
        );
        let calculated_int_val = fp_mul(
            &abs_int_val,
            &one_minus_2s,
            ctx,
            constraints,
            "sitofp_signed_res",
        );
        constraints.push(AirExpression::Sub(
            Box::new(op_expr),
            Box::new(calculated_int_val),
        ));

        constraints.push(remainder);
    }
}

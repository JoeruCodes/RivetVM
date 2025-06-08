use std::collections::HashMap;

use crate::utils::*;
use crate::{
    constraints::{lang_operand_to_air_expression, AirExpression, ResolveConstraint, RowOffset},
    ConstraintSystemVariable, Operand, StructuredAirConstraint,
};

#[derive(Debug, Clone)]
pub struct UiToFp {
    operand: Operand,
    result: ConstraintSystemVariable,
    operand_bitwidth: u32,
    result_bitwidth: u32,
    block_name: String,
}

impl ResolveConstraint for UiToFp {
    fn resolve(
        &self,
        constraints: &mut Vec<super::AirExpression>,
        ctx: &mut crate::ctx::AirGenContext,
        phi_condition_map: &HashMap<(String, String), ConstraintSystemVariable>,
        switch_instructions: &Vec<StructuredAirConstraint>,
    ) {
        println!(
            "  UITOFP: op={:?}, res={:?}, op_bw={}, res_bw={}",
            self.operand, self.result, self.operand_bitwidth, self.result_bitwidth
        );

        let op_expr = lang_operand_to_air_expression(self.operand);
        ctx.add_unsigned_range_proof_constraints(op_expr.clone(), self.operand_bitwidth);

        let (s_fp_bits, e_fp_bits, m_fp_bits) = match self.result_bitwidth {
            32 => (1, 8, 23),
            64 => (1, 11, 52),
            _ => panic!("Unsupported FP bitwidth for UIToFP"),
        };

        let (res_s_var, res_e_var, res_m_var) = setup_sem_aux_vars(
            Operand::Var(self.result),
            "res_uitofp",
            ctx,
            s_fp_bits,
            e_fp_bits,
            m_fp_bits,
            constraints,
        );

        let res_s_expr = AirExpression::Trace(res_s_var, RowOffset::Current);
        let res_e_expr = AirExpression::Trace(res_e_var, RowOffset::Current);
        let res_m_expr = AirExpression::Trace(res_m_var, RowOffset::Current);

        constraints.push(res_s_expr.clone());

        let is_zero = fp_is_value_zero(&op_expr, ctx, constraints, "uitofp_is_zero");

        constraints.push(AirExpression::Mul(
            Box::new(is_zero.clone()),
            Box::new(res_e_expr.clone()),
        ));
        constraints.push(AirExpression::Mul(
            Box::new(is_zero.clone()),
            Box::new(res_m_expr.clone()),
        ));

        let not_is_zero = fp_logical_not(&is_zero, ctx, constraints, "uitofp_not_zero");

        let (msb_pos_expr, op_without_msb_expr) = fp_find_msb(
            &op_expr,
            self.operand_bitwidth,
            ctx,
            constraints,
            "uitofp_msb",
        );

        let bias = (1u128 << (e_fp_bits - 1)) - 1;
        let calculated_e = fp_add(
            &msb_pos_expr,
            &AirExpression::Constant(bias),
            ctx,
            constraints,
            "uitofp_calc_e",
        );

        let e_constraint = AirExpression::Sub(Box::new(res_e_expr.clone()), Box::new(calculated_e));

        constraints.push(AirExpression::Mul(
            Box::new(not_is_zero.clone()),
            Box::new(e_constraint),
        ));

        let m_fp_bits_expr = AirExpression::Constant(m_fp_bits as u128);

        let is_right_shift = fp_icmp_uge(
            &msb_pos_expr,
            &m_fp_bits_expr,
            self.operand_bitwidth,
            ctx,
            constraints,
            "uitofp_is_rshift",
        );

        let right_shift_amount = fp_sub(
            &msb_pos_expr,
            &m_fp_bits_expr,
            ctx,
            constraints,
            "uitofp_rshift_amt",
        );
        let (rshifted_m, _r_rem) = fp_variable_division(
            &op_without_msb_expr,
            &right_shift_amount,
            self.operand_bitwidth.saturating_sub(1),
            self.operand_bitwidth,
            ctx,
            constraints,
            "uitofp_rshift",
        );

        let left_shift_amount = fp_sub(
            &m_fp_bits_expr,
            &msb_pos_expr,
            ctx,
            constraints,
            "uitofp_lshift_amt",
        );
        let pow2_lshift = fp_power_of_2(
            &left_shift_amount,
            m_fp_bits,
            ctx,
            constraints,
            "uitofp_lshift_pow2",
        );
        let lshifted_m = fp_mul(
            &op_without_msb_expr,
            &pow2_lshift,
            ctx,
            constraints,
            "uitofp_lshift",
        );

        let calculated_m = fp_select(
            &is_right_shift,
            &rshifted_m,
            &lshifted_m,
            ctx,
            constraints,
            "uitofp_calc_m",
        );

        let m_constraint = AirExpression::Sub(Box::new(res_m_expr.clone()), Box::new(calculated_m));
        constraints.push(AirExpression::Mul(
            Box::new(not_is_zero.clone()),
            Box::new(m_constraint),
        ));
    }
}

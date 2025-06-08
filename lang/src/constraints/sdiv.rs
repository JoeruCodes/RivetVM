use std::collections::HashMap;

use crate::{
    constraints::{
        lang_operand_to_air_expression, AirExpression, AirTraceVariable, ResolveConstraint,
        RowOffset,
    },
    ConstraintSystemVariable, Operand, StructuredAirConstraint,
};

#[derive(Debug, Clone)]
pub struct SDiv {
    pub operand1: Operand,
    pub operand2: Operand,
    pub result: ConstraintSystemVariable,
    pub block_name: String,
    pub operand_bitwidth: u32,
}

impl ResolveConstraint for SDiv {
    fn resolve(
        &self,
        constraints: &mut Vec<super::AirExpression>,
        ctx: &mut crate::ctx::AirGenContext,
        phi_condition_map: &HashMap<(String, String), ConstraintSystemVariable>,
        switch_instructions: &Vec<StructuredAirConstraint>,
    ) {
        let a_expr = lang_operand_to_air_expression(self.operand1);
        let b_expr = lang_operand_to_air_expression(self.operand2);
        let q_expr = AirExpression::Trace(AirTraceVariable(self.result.0), RowOffset::Current);

        let r_aux_var = ctx.new_aux_variable();
        let r_expr = AirExpression::Trace(r_aux_var, RowOffset::Current);
        println!(
            "  SDIV: dividend={:?}, divisor={:?}, self.result={:?}, remainder_aux_var={:?} (bitwidth {})",
            self.operand1, self.operand2, self.result, r_aux_var, self.operand_bitwidth
        );

        ctx.add_signed_range_proof_constraints(a_expr.clone(), self.operand_bitwidth);
        ctx.add_signed_range_proof_constraints(b_expr.clone(), self.operand_bitwidth);
        ctx.add_signed_range_proof_constraints(q_expr.clone(), self.operand_bitwidth);

        let is_a_zero_aux = ctx.new_aux_variable();
        let is_a_zero_expr = AirExpression::Trace(is_a_zero_aux, RowOffset::Current);
        constraints.push(AirExpression::Mul(
            Box::new(is_a_zero_expr.clone()),
            Box::new(AirExpression::Sub(
                Box::new(is_a_zero_expr.clone()),
                Box::new(AirExpression::Constant(1)),
            )),
        ));
        constraints.push(AirExpression::Mul(
            Box::new(is_a_zero_expr.clone()),
            Box::new(a_expr.clone()),
        ));
        println!(
            "    SDIV: is_a_zero_aux {:?} (bool + def: is_a_zero*a=0) added early.",
            is_a_zero_aux
        );

        let q_times_b = AirExpression::Mul(Box::new(q_expr.clone()), Box::new(b_expr.clone()));
        let qb_plus_r = AirExpression::Add(Box::new(q_times_b), Box::new(r_expr.clone()));
        constraints.push(AirExpression::Sub(
            Box::new(a_expr.clone()),
            Box::new(qb_plus_r),
        ));
        println!("    SDIV: Constraint a-(q*b+r)=0 added.");

        let (_a_bits, a_msb_expr_opt) =
            ctx.add_signed_range_proof_constraints(a_expr, self.operand_bitwidth);
        let (_b_bits, b_msb_expr_opt) =
            ctx.add_signed_range_proof_constraints(b_expr.clone(), self.operand_bitwidth);
        let (_q_bits, q_msb_expr_opt) =
            ctx.add_signed_range_proof_constraints(q_expr, self.operand_bitwidth);
        let (_r_bits, r_msb_expr_opt) =
            ctx.add_signed_range_proof_constraints(r_expr.clone(), self.operand_bitwidth);

        if let (Some(a_msb_expr_val), Some(r_msb_expr_val)) =
            (a_msb_expr_opt.as_ref(), r_msb_expr_opt.as_ref())
        {
            println!(
                "    SDIV: Implementing Remainder Sign Constraint using a_msb={:?}, r_msb={:?}",
                a_msb_expr_val, r_msb_expr_val
            );

            let one_minus_is_a_zero = AirExpression::Sub(
                Box::new(AirExpression::Constant(1)),
                Box::new(is_a_zero_expr.clone()),
            );
            let a_msb_minus_r_msb = AirExpression::Sub(
                Box::new(a_msb_expr_val.clone()),
                Box::new(r_msb_expr_val.clone()),
            );
            constraints.push(AirExpression::Mul(
                Box::new(one_minus_is_a_zero),
                Box::new(a_msb_minus_r_msb),
            ));
            println!("      SDIV RemSign: (1-is_a_zero)*(a_msb-r_msb)=0 added.");

            constraints.push(AirExpression::Mul(
                Box::new(is_a_zero_expr.clone()),
                Box::new(r_expr.clone()),
            ));
            println!("      SDIV RemSign: is_a_zero * r = 0 added.");
        } else {
            println!(
                "    SDIV: WARN - Could not implement Remainder Sign constraint due to missing MSB for 'a' or 'r'. self.operand_bitwidth: {}",
                self.operand_bitwidth
            );
        }

        if let (Some(r_msb_expr_val_mag), Some(b_msb_expr_val_mag)) =
            (r_msb_expr_opt.as_ref(), b_msb_expr_opt.as_ref())
        {
            println!("    SDIV: Implementing Remainder Magnitude Constraint abs(r) < abs(b)");

            let one_const = AirExpression::Constant(1);
            let two_const = AirExpression::Constant(2);

            let one_minus_two_r_msb = AirExpression::Sub(
                Box::new(one_const.clone()),
                Box::new(AirExpression::Mul(
                    Box::new(two_const.clone()),
                    Box::new(r_msb_expr_val_mag.clone()),
                )),
            );
            let abs_r_expr =
                AirExpression::Mul(Box::new(r_expr.clone()), Box::new(one_minus_two_r_msb));
            println!(
                "      SDIV Mag: abs_r_expr = r * (1 - 2*r_msb) = {:?}",
                abs_r_expr
            );

            let one_minus_two_b_msb = AirExpression::Sub(
                Box::new(one_const.clone()),
                Box::new(AirExpression::Mul(
                    Box::new(two_const.clone()),
                    Box::new(b_msb_expr_val_mag.clone()),
                )),
            );
            let abs_b_expr =
                AirExpression::Mul(Box::new(b_expr.clone()), Box::new(one_minus_two_b_msb));
            println!(
                "      SDIV Mag: abs_b_expr = b * (1 - 2*b_msb) = {:?}",
                abs_b_expr
            );

            let ult_res_abs_r_lt_abs_b_var = ctx.new_aux_variable();
            let ult_res_abs_r_lt_abs_b_expr =
                AirExpression::Trace(ult_res_abs_r_lt_abs_b_var, RowOffset::Current);
            println!(
                "      SDIV Mag: ult_res_var for (abs(r) < abs(b)) is {:?}",
                ult_res_abs_r_lt_abs_b_var
            );

            constraints.push(AirExpression::Mul(
                Box::new(ult_res_abs_r_lt_abs_b_expr.clone()),
                Box::new(AirExpression::Sub(
                    Box::new(ult_res_abs_r_lt_abs_b_expr.clone()),
                    Box::new(AirExpression::Constant(1)),
                )),
            ));
            constraints.push(AirExpression::Sub(
                Box::new(ult_res_abs_r_lt_abs_b_expr.clone()),
                Box::new(AirExpression::Constant(1)),
            ));
            println!("      SDIV Mag: Booleanity and assertion (must be 1) for ult_res_var added.");

            let mut d_sum_bit_vars_ult_mag = Vec::new();
            println!(
                "      SDIV Mag: Decomposing for D_sum in ULT(abs_r, abs_b) ({} bits)",
                self.operand_bitwidth
            );
            if self.operand_bitwidth > 0 {
                for i in 0..self.operand_bitwidth {
                    let bit_aux_var = ctx.new_aux_variable();
                    let bit_expr_d = AirExpression::Trace(bit_aux_var, RowOffset::Current);
                    constraints.push(AirExpression::Mul(
                        Box::new(bit_expr_d.clone()),
                        Box::new(AirExpression::Sub(
                            Box::new(bit_expr_d.clone()),
                            Box::new(AirExpression::Constant(1)),
                        )),
                    ));
                    d_sum_bit_vars_ult_mag.push(bit_expr_d);
                    println!(
                        "        ULT(abs_r,abs_b) D_sum bit_{} (trace col {}) created",
                        i, bit_aux_var.0
                    );
                }
            }

            let d_sum_air_ult_mag = d_sum_bit_vars_ult_mag.iter().enumerate().fold(
                AirExpression::Constant(0),
                |acc, (i, bit_e)| {
                    AirExpression::Add(
                        Box::new(acc),
                        Box::new(AirExpression::Mul(
                            Box::new(bit_e.clone()),
                            Box::new(AirExpression::Constant(1u128 << i)),
                        )),
                    )
                },
            );
            println!(
                "      SDIV Mag: D_sum_air for ULT(abs_r,abs_b) constructed: {:?}",
                d_sum_air_ult_mag
            );

            let b_abs_minus_a_abs_minus_1 = AirExpression::Sub(
                Box::new(AirExpression::Sub(
                    Box::new(abs_b_expr.clone()),
                    Box::new(abs_r_expr.clone()),
                )),
                Box::new(AirExpression::Constant(1)),
            );
            let ult_final_constraint = AirExpression::Sub(
                Box::new(b_abs_minus_a_abs_minus_1),
                Box::new(d_sum_air_ult_mag.clone()),
            );
            constraints.push(ult_final_constraint);
            println!(
                "      SDIV Mag: ULT(abs_r,abs_b) constraint ( (abs_b - abs_r - 1) - D_sum = 0) added."
            );
        } else {
            println!(
                "    SDIV: WARN - Could not implement Remainder Magnitude constraint due to missing MSB for 'r' or 'b'. self.operand_bitwidth: {}",
                self.operand_bitwidth
            );
        }

        if let (Some(a_msb_expr_val_qs), Some(b_msb_expr_val_qs), Some(q_msb_expr_val_qs)) = (
            a_msb_expr_opt.as_ref(),
            b_msb_expr_opt.as_ref(),
            q_msb_expr_opt.as_ref(),
        ) {
            println!(
                "    SDIV: Implementing Quotient Sign Constraint using a_msb={:?}, b_msb={:?}, q_msb={:?}",
                a_msb_expr_val_qs, b_msb_expr_val_qs, q_msb_expr_val_qs
            );

            let is_b_zero_aux = ctx.new_aux_variable();
            let is_b_zero_expr = AirExpression::Trace(is_b_zero_aux, RowOffset::Current);
            constraints.push(AirExpression::Mul(
                Box::new(is_b_zero_expr.clone()),
                Box::new(AirExpression::Sub(
                    Box::new(is_b_zero_expr.clone()),
                    Box::new(AirExpression::Constant(1)),
                )),
            ));
            constraints.push(AirExpression::Mul(
                Box::new(is_b_zero_expr.clone()),
                Box::new(b_expr.clone()),
            ));
            println!(
                "      SDIV QuotSign: is_b_zero_aux {:?} (bool + def) added.",
                is_b_zero_aux
            );

            let one_minus_is_a_zero_for_quot = AirExpression::Sub(
                Box::new(AirExpression::Constant(1)),
                Box::new(is_a_zero_expr.clone()),
            );
            let one_minus_is_b_zero = AirExpression::Sub(
                Box::new(AirExpression::Constant(1)),
                Box::new(is_b_zero_expr.clone()),
            );

            let condition_apply_sign_logic_aux = ctx.new_aux_variable();
            let condition_apply_sign_logic_expr =
                AirExpression::Trace(condition_apply_sign_logic_aux, RowOffset::Current);
            constraints.push(AirExpression::Mul(
                Box::new(condition_apply_sign_logic_expr.clone()),
                Box::new(AirExpression::Sub(
                    Box::new(condition_apply_sign_logic_expr.clone()),
                    Box::new(AirExpression::Constant(1)),
                )),
            ));
            let product_of_nots = AirExpression::Mul(
                Box::new(one_minus_is_a_zero_for_quot.clone()),
                Box::new(one_minus_is_b_zero.clone()),
            );
            constraints.push(AirExpression::Sub(
                Box::new(condition_apply_sign_logic_expr.clone()),
                Box::new(product_of_nots),
            ));
            println!(
                "      SDIV QuotSign: condition_apply_sign_logic_expr {:?} (bool + def) added.",
                condition_apply_sign_logic_aux
            );

            let a_msb_plus_b_msb = AirExpression::Add(
                Box::new(a_msb_expr_val_qs.clone()),
                Box::new(b_msb_expr_val_qs.clone()),
            );
            let two_const = AirExpression::Constant(2);
            let a_msb_times_b_msb = AirExpression::Mul(
                Box::new(a_msb_expr_val_qs.clone()),
                Box::new(b_msb_expr_val_qs.clone()),
            );
            let two_a_msb_b_msb =
                AirExpression::Mul(Box::new(two_const), Box::new(a_msb_times_b_msb));
            let xor_val_expr =
                AirExpression::Sub(Box::new(a_msb_plus_b_msb), Box::new(two_a_msb_b_msb));

            let xor_minus_q_msb =
                AirExpression::Sub(Box::new(xor_val_expr), Box::new(q_msb_expr_val_qs.clone()));
            constraints.push(AirExpression::Mul(
                Box::new(condition_apply_sign_logic_expr.clone()),
                Box::new(xor_minus_q_msb),
            ));
            println!("      SDIV QuotSign: conditional XOR logic for q_msb added.");

            constraints.push(AirExpression::Mul(
                Box::new(is_a_zero_expr.clone()),
                Box::new(q_msb_expr_val_qs.clone()),
            ));
            println!("      SDIV QuotSign: is_a_zero * q_msb = 0 added.");
        } else {
            println!(
                "    SDIV: WARN - Could not implement Quotient Sign constraint due to missing MSB for 'a', 'b', or 'q'. self.operand_bitwidth: {}",
                self.operand_bitwidth
            );
        }
    }
}

use std::collections::HashMap;

use crate::{
    constraints::{
        lang_operand_to_air_expression, AirExpression, AirTraceVariable, ResolveConstraint,
        RowOffset,
    },
    ConstraintSystemVariable, Operand, StructuredAirConstraint,
};

#[derive(Debug, Clone)]
pub struct UDiv {
    pub operand1: Operand,
    pub operand2: Operand,
    pub result: ConstraintSystemVariable,
    pub block_name: String,
    pub operand_bitwidth: u32,
}

impl ResolveConstraint for UDiv {
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
            "  UDIV: dividend={:?}, divisor={:?}, self.result={:?}, remainder_aux_var={:?} (bitwidth {})",
            self.operand1, self.operand2, self.result, r_aux_var, self.operand_bitwidth
        );

        ctx.add_unsigned_range_proof_constraints(a_expr.clone(), self.operand_bitwidth);
        ctx.add_unsigned_range_proof_constraints(b_expr.clone(), self.operand_bitwidth);
        ctx.add_unsigned_range_proof_constraints(q_expr.clone(), self.operand_bitwidth);
        ctx.add_unsigned_range_proof_constraints(r_expr.clone(), self.operand_bitwidth);

        let q_times_b = AirExpression::Mul(Box::new(q_expr.clone()), Box::new(b_expr.clone()));
        let qb_plus_r = AirExpression::Add(Box::new(q_times_b), Box::new(r_expr.clone()));
        constraints.push(AirExpression::Sub(
            Box::new(a_expr.clone()),
            Box::new(qb_plus_r),
        ));
        println!("    UDIV: Constraint a-(q*b+r)=0 added.");

        let mut r_bit_vars_exprs = Vec::new();
        let mut r_sum_terms = Vec::new();
        println!(
            "    UDIV: Decomposing remainder r ({:?}) into {} bits",
            r_aux_var, self.operand_bitwidth
        );
        for i in 0..self.operand_bitwidth {
            let bit_aux_var = ctx.new_aux_variable();
            let bit_expr = AirExpression::Trace(bit_aux_var, RowOffset::Current);
            let bit_minus_one = AirExpression::Sub(
                Box::new(bit_expr.clone()),
                Box::new(AirExpression::Constant(1)),
            );
            constraints.push(AirExpression::Mul(
                Box::new(bit_expr.clone()),
                Box::new(bit_minus_one),
            ));
            r_bit_vars_exprs.push(bit_expr.clone());
            let power_of_2 = 1u128 << i;
            r_sum_terms.push(AirExpression::Mul(
                Box::new(bit_expr.clone()),
                Box::new(AirExpression::Constant(power_of_2)),
            ));
            println!(
                "      r_bit_{} (trace col {}) created for remainder",
                i, bit_aux_var.0
            );
        }
        let r_sum_from_bits = r_sum_terms
            .into_iter()
            .reduce(|acc, term| AirExpression::Add(Box::new(acc), Box::new(term)))
            .unwrap_or_else(|| AirExpression::Constant(0));
        constraints.push(AirExpression::Sub(
            Box::new(r_expr.clone()),
            Box::new(r_sum_from_bits),
        ));
        println!("    UDIV: Remainder r decomposition constraint added.");

        let ult_res_r_lt_b_var = ctx.new_aux_variable();
        let ult_res_r_lt_b_expr = AirExpression::Trace(ult_res_r_lt_b_var, RowOffset::Current);
        println!(
            "    UDIV: ult_res_r_lt_b_var for (r < b) is {:?}",
            ult_res_r_lt_b_var
        );

        let ult_res_minus_one = AirExpression::Sub(
            Box::new(ult_res_r_lt_b_expr.clone()),
            Box::new(AirExpression::Constant(1)),
        );
        constraints.push(AirExpression::Mul(
            Box::new(ult_res_r_lt_b_expr.clone()),
            Box::new(ult_res_minus_one),
        ));

        constraints.push(AirExpression::Sub(
            Box::new(ult_res_r_lt_b_expr.clone()),
            Box::new(AirExpression::Constant(1)),
        ));
        println!("    UDIV: Booleanity and assertion (must be 1) for ult_res_r_lt_b added.");

        let mut ult_bit_vars_air_exprs = Vec::new();
        println!(
            "    UDIV: Decomposing for D_sum in ULT(r,b) ({} bits)",
            self.operand_bitwidth
        );
        for i in 0..self.operand_bitwidth {
            let bit_aux_var = ctx.new_aux_variable();
            let bit_expr_d = AirExpression::Trace(bit_aux_var, RowOffset::Current);
            let bit_minus_one_d = AirExpression::Sub(
                Box::new(bit_expr_d.clone()),
                Box::new(AirExpression::Constant(1)),
            );
            constraints.push(AirExpression::Mul(
                Box::new(bit_expr_d.clone()),
                Box::new(bit_minus_one_d),
            ));
            ult_bit_vars_air_exprs.push(bit_expr_d);
            println!(
                "      ULT(r,b) D_sum bit_{} (trace col {}) created",
                i, bit_aux_var.0
            );
        }

        let mut d_sum_air_ult: Option<Box<AirExpression>> = None;
        for (i, bit_expr_d) in ult_bit_vars_air_exprs.iter().enumerate() {
            let power_of_2 = 1u128 << i;
            let term = AirExpression::Mul(
                Box::new(bit_expr_d.clone()),
                Box::new(AirExpression::Constant(power_of_2)),
            );
            d_sum_air_ult = Some(match d_sum_air_ult {
                Some(current_sum) => Box::new(AirExpression::Add(current_sum, Box::new(term))),
                None => Box::new(term),
            });
        }
        let d_sum_air_ult = d_sum_air_ult.unwrap_or_else(|| Box::new(AirExpression::Constant(0)));
        println!(
            "    UDIV: D_sum_air for ULT(r,b) constructed: {:?}",
            d_sum_air_ult
        );

        let b_minus_r_minus_1 = AirExpression::Sub(
            Box::new(AirExpression::Sub(
                Box::new(b_expr.clone()),
                Box::new(r_expr.clone()),
            )),
            Box::new(AirExpression::Constant(1)),
        );
        let term1_val_ult = AirExpression::Sub(Box::new(b_minus_r_minus_1), d_sum_air_ult.clone());
        constraints.push(AirExpression::Mul(
            Box::new(ult_res_r_lt_b_expr.clone()),
            Box::new(term1_val_ult),
        ));
        println!("    UDIV: ULT(r,b) selector1 (res=1 path) constraint added.");

        let one_minus_ult_res = AirExpression::Sub(
            Box::new(AirExpression::Constant(1)),
            Box::new(ult_res_r_lt_b_expr.clone()),
        );
        let r_minus_b = AirExpression::Sub(Box::new(r_expr.clone()), Box::new(b_expr.clone()));
        let term2_val_ult = AirExpression::Sub(Box::new(r_minus_b), d_sum_air_ult.clone());
        constraints.push(AirExpression::Mul(
            Box::new(one_minus_ult_res),
            Box::new(term2_val_ult),
        ));
        println!("    UDIV: ULT(r,b) selector2 (res=0 path) constraint added.");
    }
}

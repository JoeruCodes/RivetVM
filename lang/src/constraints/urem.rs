use crate::{
    constraints::{
        lang_operand_to_air_expression, AirExpression, AirTraceVariable, ResolveConstraint,
        RowOffset,
    },
    ConstraintSystemVariable, Operand,
};

#[derive(Debug, Clone)]
pub struct URem {
    pub operand1: Operand,
    pub operand2: Operand,
    pub result: ConstraintSystemVariable,
    pub block_name: String,
    pub operand_bitwidth: u32,
}

impl ResolveConstraint for URem {
    fn resolve(
        &self,
        constraints: &mut Vec<super::AirExpression>,
        ctx: &mut crate::ctx::AirGenContext,
        phi_condition_map: &std::collections::HashMap<(String, String), ConstraintSystemVariable>,
        switch_instructions: &Vec<crate::StructuredAirConstraint>,
    ) {
        let a_expr = ctx.expr_for_operand(self.operand1);
        let b_expr = ctx.expr_for_operand(self.operand2);

        let reg_col_opt = ctx.col_for_ssa(self.result);

        let dest_col = ctx.new_aux_variable();
        ctx.bind_ssa_var(self.result, dest_col.0);
        let r_expr = AirExpression::Trace(dest_col, RowOffset::Current);

        let q_aux_var = ctx.new_aux_variable();
        let q_expr = AirExpression::Trace(q_aux_var, RowOffset::Current);
        println!(
                "  UREM: dividend(a)={:?}, divisor(b)={:?}, remainder(r)={:?}, quotient_aux(q)={:?} (bitwidth {})",
                self.operand1, self.operand2, self.result, q_aux_var, self.operand_bitwidth
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
        println!("    UREM: Constraint a-(q*b+r)=0 added.");

        let ult_res_r_lt_b_var = ctx.new_aux_variable();
        let ult_res_r_lt_b_expr = AirExpression::Trace(ult_res_r_lt_b_var, RowOffset::Current);
        println!(
            "    UREM: ult_res_r_lt_b_var for (r < b) is {:?}",
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
        println!("    UREM: Booleanity and assertion (must be 1) for ult_res_r_lt_b added.");

        let mut ult_bit_vars_air_exprs = Vec::new();
        for _ in 0..self.operand_bitwidth {
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
        println!("    UREM: ULT(r,b) selectors added.");

        if let Some(reg_col) = reg_col_opt {
            let selector_expr = ctx.new_row_selector();
            let reg_expr = AirExpression::Trace(AirTraceVariable(reg_col), RowOffset::Current);
            let eq_expr = AirExpression::Sub(Box::new(r_expr.clone()), Box::new(reg_expr));
            ctx.add_row_gated_constraint(selector_expr, eq_expr);
        }
    }
}

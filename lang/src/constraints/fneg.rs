use crate::constraints::{AirExpression, AirTraceVariable, RowOffset};
use crate::utils::*;
use crate::{constraints::ResolveConstraint, ConstraintSystemVariable, Operand};

#[derive(Debug, Clone)]
pub struct FNeg {
    pub operand: Operand,
    pub result: ConstraintSystemVariable,
    pub block_name: String,
    pub operand_bitwidth: u32,
}

impl ResolveConstraint for FNeg {
    fn resolve(
        &self,
        constraints: &mut Vec<super::AirExpression>,
        ctx: &mut crate::ctx::AirGenContext,
        phi_condition_map: &std::collections::HashMap<(String, String), ConstraintSystemVariable>,
        switch_instructions: &Vec<crate::StructuredAirConstraint>,
    ) {
        println!(
            "  FNEG: op={:?}, res={:?} (bitwidth {}) - Setting up S/E/M aux vars.",
            self.operand, self.result, self.operand_bitwidth
        );

        let reg_col_opt = ctx.col_for_ssa(self.result);

        let dest_col = ctx.new_aux_variable();
        ctx.bind_ssa_var(self.result, dest_col.0);
        let res_expr_full = AirExpression::Trace(dest_col, RowOffset::Current);

        let (s_bit_count, exp_bit_count, mant_bit_count) = match self.operand_bitwidth {
            16 => (1u32, 5u32, 10u32),
            32 => (1u32, 8u32, 23u32),
            64 => (1u32, 11u32, 52u32),
            80 => (1u32, 15u32, 63u32),
            128 => (1u32, 15u32, 112u32),
            _ => panic!(
                "Unsupported self.operand_bitwidth {} for FNeg S/E/M decomposition.",
                self.operand_bitwidth
            ),
        };

        let (op_s_var, op_e_var, op_m_var) = setup_sem_aux_vars(
            self.operand,
            "op_fneg",
            ctx,
            s_bit_count,
            exp_bit_count,
            mant_bit_count,
            constraints,
        );
        let (res_s_var, res_e_var, res_m_var) = setup_sem_aux_vars(
            Operand::Var(self.result),
            "res_fneg",
            ctx,
            s_bit_count,
            exp_bit_count,
            mant_bit_count,
            constraints,
        );

        let op_s_expr = AirExpression::Trace(op_s_var, RowOffset::Current);
        let op_e_expr = AirExpression::Trace(op_e_var, RowOffset::Current);
        let op_m_expr = AirExpression::Trace(op_m_var, RowOffset::Current);

        let res_s_expr = AirExpression::Trace(res_s_var, RowOffset::Current);
        let res_e_expr = AirExpression::Trace(res_e_var, RowOffset::Current);
        let res_m_expr = AirExpression::Trace(res_m_var, RowOffset::Current);

        let flipped_sign =
            AirExpression::Sub(Box::new(AirExpression::Constant(1)), Box::new(op_s_expr));
        constraints.push(AirExpression::Sub(
            Box::new(res_s_expr),
            Box::new(flipped_sign),
        ));

        constraints.push(AirExpression::Sub(
            Box::new(res_e_expr),
            Box::new(op_e_expr),
        ));

        constraints.push(AirExpression::Sub(
            Box::new(res_m_expr),
            Box::new(op_m_expr),
        ));

        if let Some(reg_col) = reg_col_opt {
            let selector_expr = ctx.new_row_selector();
            let reg_expr = AirExpression::Trace(AirTraceVariable(reg_col), RowOffset::Current);
            let eq_expr = AirExpression::Sub(Box::new(res_expr_full), Box::new(reg_expr));
            ctx.add_row_gated_constraint(selector_expr, eq_expr);
        }
    }
}

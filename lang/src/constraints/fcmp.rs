use inkwell::FloatPredicate;

use crate::constraints::{AirExpression, RowOffset};
use crate::utils::*;
use crate::{constraints::ResolveConstraint, ConstraintSystemVariable, Operand};

#[derive(Debug, Clone)]
pub struct FCmp {
    pub cond: FloatPredicate,
    pub operand1: Operand,
    pub operand2: Operand,
    pub result: ConstraintSystemVariable,
    pub block_name: String,
    pub operand_bitwidth: u32,
}

impl ResolveConstraint for FCmp {
    fn resolve(
        &self,
        constraints: &mut Vec<super::AirExpression>,
        ctx: &mut crate::ctx::AirGenContext,
        phi_condition_map: &std::collections::HashMap<(String, String), ConstraintSystemVariable>,
        switch_instructions: &Vec<crate::StructuredAirConstraint>,
    ) {
        let (s_bit_count, exp_bit_count, mant_bit_count) = match self.operand_bitwidth {
            16 => (1, 5, 10),
            32 => (1, 8, 23),
            64 => (1, 11, 52),
            _ => panic!(
                "Unsupported self.operand_bitwidth {} for FCmp",
                self.operand_bitwidth
            ),
        };

        let (op1_s_var, op1_e_var, op1_m_var) = setup_sem_aux_vars(
            self.operand1,
            "op1_fcmp",
            ctx,
            s_bit_count,
            exp_bit_count,
            mant_bit_count,
            constraints,
        );
        let (op2_s_var, op2_e_var, op2_m_var) = setup_sem_aux_vars(
            self.operand2,
            "op2_fcmp",
            ctx,
            s_bit_count,
            exp_bit_count,
            mant_bit_count,
            constraints,
        );

        let op1_s_expr = AirExpression::Trace(op1_s_var, RowOffset::Current);
        let op1_e_expr = AirExpression::Trace(op1_e_var, RowOffset::Current);
        let op1_m_expr = AirExpression::Trace(op1_m_var, RowOffset::Current);

        let op2_s_expr = AirExpression::Trace(op2_s_var, RowOffset::Current);
        let op2_e_expr = AirExpression::Trace(op2_e_var, RowOffset::Current);
        let op2_m_expr = AirExpression::Trace(op2_m_var, RowOffset::Current);

        let res_air_var = super::AirTraceVariable(self.result.0);
        let res_expr = AirExpression::Trace(res_air_var, RowOffset::Current);

        constraints.push(AirExpression::Mul(
            Box::new(res_expr.clone()),
            Box::new(AirExpression::Sub(
                Box::new(res_expr.clone()),
                Box::new(AirExpression::Constant(1)),
            )),
        ));

        let op1_is_nan = fp_is_nan(
            &op1_e_expr,
            &op1_m_expr,
            exp_bit_count,
            mant_bit_count,
            ctx,
            constraints,
            "op1_fcmp_nan",
        );
        let op2_is_nan = fp_is_nan(
            &op2_e_expr,
            &op2_m_expr,
            exp_bit_count,
            mant_bit_count,
            ctx,
            constraints,
            "op2_fcmp_nan",
        );

        let op1_is_inf = fp_is_inf(
            &op1_e_expr,
            &op1_m_expr,
            exp_bit_count,
            mant_bit_count,
            ctx,
            constraints,
            "op1_fcmp_inf",
        );
        let op2_is_inf = fp_is_inf(
            &op2_e_expr,
            &op2_m_expr,
            exp_bit_count,
            mant_bit_count,
            ctx,
            constraints,
            "op2_fcmp_inf",
        );

        let op1_is_true_zero = fp_is_true_zero(
            &op1_e_expr,
            &op1_m_expr,
            exp_bit_count,
            mant_bit_count,
            ctx,
            constraints,
            "op1_fcmp_zero",
        );
        let op2_is_true_zero = fp_is_true_zero(
            &op2_e_expr,
            &op2_m_expr,
            exp_bit_count,
            mant_bit_count,
            ctx,
            constraints,
            "op2_fcmp_zero",
        );

        let is_uno = fp_logical_or(&op1_is_nan, &op2_is_nan, ctx, constraints, "is_uno_fcmp");
        let is_ord = fp_logical_not(&is_uno, ctx, constraints, "is_ord_fcmp");

        let signs_eq = fp_icmp_eq(&op1_s_expr, &op2_s_expr, ctx, constraints, "signs_eq_fcmp");
        let exps_eq = fp_icmp_eq(&op1_e_expr, &op2_e_expr, ctx, constraints, "exps_eq_fcmp");
        let mants_eq = fp_icmp_eq(&op1_m_expr, &op2_m_expr, ctx, constraints, "mants_eq_fcmp");

        let same_sem = fp_logical_and(
            &signs_eq,
            &fp_logical_and(&exps_eq, &mants_eq, ctx, constraints, "em_eq_fcmp"),
            ctx,
            constraints,
            "sem_eq_fcmp",
        );
        let both_zero = fp_logical_and(
            &op1_is_true_zero,
            &op2_is_true_zero,
            ctx,
            constraints,
            "both_zero_fcmp",
        );
        let are_equal_if_not_inf = fp_logical_or(
            &same_sem,
            &both_zero,
            ctx,
            constraints,
            "are_equal_not_inf_fcmp",
        );

        let both_inf = fp_logical_and(&op1_is_inf, &op2_is_inf, ctx, constraints, "both_inf_fcmp");
        let both_inf_and_signs_eq =
            fp_logical_and(&both_inf, &signs_eq, ctx, constraints, "both_inf_eq_fcmp");

        let are_equal_ord = fp_select(
            &op1_is_inf,
            &both_inf_and_signs_eq,
            &are_equal_if_not_inf,
            ctx,
            constraints,
            "are_equal_ord_fcmp",
        );

        let op1_is_neg = fp_icmp_eq(
            &op1_s_expr,
            &AirExpression::Constant(1),
            ctx,
            constraints,
            "op1_neg_fcmp",
        );
        let op2_is_neg = fp_icmp_eq(
            &op2_s_expr,
            &AirExpression::Constant(1),
            ctx,
            constraints,
            "op2_neg_fcmp",
        );
        let op1_is_pos = fp_logical_not(&op1_is_neg, ctx, constraints, "op1_pos_fcmp");
        let op2_is_pos = fp_logical_not(&op2_is_neg, ctx, constraints, "op2_pos_fcmp");

        let op1_neg_op2_pos = fp_logical_and(
            &op1_is_neg,
            &op2_is_pos,
            ctx,
            constraints,
            "op1_neg_op2_pos_fcmp",
        );

        let op1_exp_lt_op2_exp = fp_icmp_ult(
            &op1_e_expr,
            &op2_e_expr,
            exp_bit_count,
            ctx,
            constraints,
            "op1_exp_lt_fcmp",
        );
        let op1_mant_lt_op2_mant = fp_icmp_ult(
            &op1_m_expr,
            &op2_m_expr,
            mant_bit_count,
            ctx,
            constraints,
            "op1_mant_lt_fcmp",
        );
        let exp_eq_mant_lt = fp_logical_and(
            &exps_eq,
            &op1_mant_lt_op2_mant,
            ctx,
            constraints,
            "exp_eq_mant_lt_fcmp",
        );
        let lt_if_pos_signed = fp_logical_or(
            &op1_exp_lt_op2_exp,
            &exp_eq_mant_lt,
            ctx,
            constraints,
            "lt_if_pos_signed_fcmp",
        );

        let op2_exp_lt_op1_exp = fp_icmp_ult(
            &op2_e_expr,
            &op1_e_expr,
            exp_bit_count,
            ctx,
            constraints,
            "op2_exp_lt_fcmp",
        );
        let op2_mant_lt_op1_mant = fp_icmp_ult(
            &op2_m_expr,
            &op1_m_expr,
            mant_bit_count,
            ctx,
            constraints,
            "op2_mant_lt_fcmp",
        );
        let exp_eq_mant_gt = fp_logical_and(
            &exps_eq,
            &op2_mant_lt_op1_mant,
            ctx,
            constraints,
            "exp_eq_mant_gt_fcmp",
        );
        let lt_if_neg_signed = fp_logical_or(
            &op2_exp_lt_op1_exp,
            &exp_eq_mant_gt,
            ctx,
            constraints,
            "lt_if_neg_signed_fcmp",
        );

        let same_sign_pos = fp_logical_and(&signs_eq, &op1_is_pos, ctx, constraints, "ss_pos_fcmp");
        let same_sign_neg = fp_logical_and(&signs_eq, &op1_is_neg, ctx, constraints, "ss_neg_fcmp");

        let same_sign_lt = fp_logical_or(
            &fp_logical_and(
                &same_sign_pos,
                &lt_if_pos_signed,
                ctx,
                constraints,
                "ss_pos_lt_fcmp",
            ),
            &fp_logical_and(
                &same_sign_neg,
                &lt_if_neg_signed,
                ctx,
                constraints,
                "ss_neg_lt_fcmp",
            ),
            ctx,
            constraints,
            "same_sign_lt_fcmp",
        );

        let lt_if_normal_numbers = fp_logical_or(
            &op1_neg_op2_pos,
            &same_sign_lt,
            ctx,
            constraints,
            "lt_if_normal_fcmp",
        );

        let op1_is_neg_inf = fp_logical_and(
            &op1_is_inf,
            &op1_is_neg,
            ctx,
            constraints,
            "op1_neg_inf_fcmp",
        );
        let op2_is_neg_inf = fp_logical_and(
            &op2_is_inf,
            &op2_is_neg,
            ctx,
            constraints,
            "op2_neg_inf_fcmp",
        );
        let op1_is_pos_inf = fp_logical_and(
            &op1_is_inf,
            &op1_is_pos,
            ctx,
            constraints,
            "op1_pos_inf_fcmp",
        );
        let op2_is_pos_inf = fp_logical_and(
            &op2_is_inf,
            &op2_is_pos,
            ctx,
            constraints,
            "op2_pos_inf_fcmp",
        );

        let case1_lt_inf = fp_logical_and(
            &op1_is_neg_inf,
            &fp_logical_not(&op2_is_neg_inf, ctx, constraints, "not_op2_neg_inf"),
            ctx,
            constraints,
            "lt_op1_neg_inf",
        );
        let case2_lt_inf = fp_logical_and(
            &op2_is_pos_inf,
            &fp_logical_not(&op1_is_pos_inf, ctx, constraints, "not_op1_pos_inf"),
            ctx,
            constraints,
            "lt_op2_pos_inf",
        );
        let is_lt_due_to_inf = fp_logical_or(
            &case1_lt_inf,
            &case2_lt_inf,
            ctx,
            constraints,
            "is_lt_due_to_inf",
        );

        let is_lt_ord = fp_select(
            &fp_logical_or(&op1_is_inf, &op2_is_inf, ctx, constraints, "any_inf"),
            &is_lt_due_to_inf,
            &lt_if_normal_numbers,
            ctx,
            constraints,
            "is_lt_ord_fcmp",
        );

        let is_gt_ord = fp_logical_and(
            &is_ord,
            &fp_logical_not(
                &fp_logical_or(&is_lt_ord, &are_equal_ord, ctx, constraints, "lt_or_eq_ord"),
                ctx,
                constraints,
                "not_lt_or_eq_ord",
            ),
            ctx,
            constraints,
            "is_gt_ord_fcmp",
        );

        let final_res = match self.cond {
            FloatPredicate::OEQ => {
                fp_logical_and(&is_ord, &are_equal_ord, ctx, constraints, "res_oeq")
            }
            FloatPredicate::ONE => fp_logical_and(
                &is_ord,
                &fp_logical_not(&are_equal_ord, ctx, constraints, "not_are_equal_ord"),
                ctx,
                constraints,
                "res_one",
            ),
            FloatPredicate::OGT => fp_logical_and(&is_ord, &is_gt_ord, ctx, constraints, "res_ogt"),
            FloatPredicate::OGE => fp_logical_and(
                &is_ord,
                &fp_logical_or(&is_gt_ord, &are_equal_ord, ctx, constraints, "oge_cond"),
                ctx,
                constraints,
                "res_oge",
            ),
            FloatPredicate::OLT => fp_logical_and(&is_ord, &is_lt_ord, ctx, constraints, "res_olt"),
            FloatPredicate::OLE => fp_logical_and(
                &is_ord,
                &fp_logical_or(&is_lt_ord, &are_equal_ord, ctx, constraints, "ole_cond"),
                ctx,
                constraints,
                "res_ole",
            ),
            FloatPredicate::ORD => is_ord.clone(),

            FloatPredicate::UEQ => {
                fp_logical_or(&is_uno, &are_equal_ord, ctx, constraints, "res_ueq")
            }
            FloatPredicate::UNE => fp_logical_or(
                &is_uno,
                &fp_logical_not(&are_equal_ord, ctx, constraints, "not_are_equal_ord_u"),
                ctx,
                constraints,
                "res_une",
            ),
            FloatPredicate::UGT => fp_logical_or(&is_uno, &is_gt_ord, ctx, constraints, "res_ugt"),
            FloatPredicate::UGE => fp_logical_or(
                &is_uno,
                &fp_logical_or(&is_gt_ord, &are_equal_ord, ctx, constraints, "uge_cond"),
                ctx,
                constraints,
                "res_uge",
            ),
            FloatPredicate::ULT => fp_logical_or(&is_uno, &is_lt_ord, ctx, constraints, "res_ult"),
            FloatPredicate::ULE => fp_logical_or(
                &is_uno,
                &fp_logical_or(&is_lt_ord, &are_equal_ord, ctx, constraints, "ule_cond"),
                ctx,
                constraints,
                "res_ule",
            ),
            FloatPredicate::UNO => is_uno.clone(),

            FloatPredicate::PredicateTrue => AirExpression::Constant(1),
            FloatPredicate::PredicateFalse => AirExpression::Constant(0),
        };

        constraints.push(AirExpression::Sub(Box::new(res_expr), Box::new(final_res)));
    }
}

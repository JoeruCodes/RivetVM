use std::collections::HashMap;

use inkwell::IntPredicate;

use crate::{
    constraints::{
        lang_operand_to_air_expression, AirExpression, AirTraceVariable, ResolveConstraint,
        RowOffset,
    },
    ConstraintSystemVariable, Operand, StructuredAirConstraint,
};

#[derive(Debug, Clone)]
pub struct Icmp {
    pub cond: IntPredicate,
    pub operand1: Operand,
    pub operand2: Operand,
    pub result: ConstraintSystemVariable,
    pub block_name: String,
    pub operand_bitwidth: u32,
}

impl ResolveConstraint for Icmp {
    fn resolve(
        &self,
        constraints: &mut Vec<super::AirExpression>,
        ctx: &mut crate::ctx::AirGenContext,
        phi_condition_map: &HashMap<(String, String), ConstraintSystemVariable>,
        switch_instructions: &Vec<StructuredAirConstraint>,
    ) {
        let res_air_var = AirTraceVariable(self.result.0);
        let res_expr = AirExpression::Trace(res_air_var, RowOffset::Current);

        let res_minus_one = AirExpression::Sub(
            Box::new(res_expr.clone()),
            Box::new(AirExpression::Constant(1)),
        );
        constraints.push(AirExpression::Mul(
            Box::new(res_expr.clone()),
            Box::new(res_minus_one),
        ));

        match self.cond {
            IntPredicate::EQ => {
                let op1_air = lang_operand_to_air_expression(self.operand1);
                let op2_air = lang_operand_to_air_expression(self.operand2);
                let diff_expr = AirExpression::Sub(Box::new(op1_air), Box::new(op2_air));
                constraints.push(AirExpression::Mul(
                    Box::new(diff_expr),
                    Box::new(res_expr.clone()),
                ));
            }
            IntPredicate::NE => {
                let op1_air = lang_operand_to_air_expression(self.operand1);
                let op2_air = lang_operand_to_air_expression(self.operand2);
                let one_minus_res = AirExpression::Sub(
                    Box::new(AirExpression::Constant(1)),
                    Box::new(res_expr.clone()),
                );
                let diff_expr = AirExpression::Sub(Box::new(op1_air), Box::new(op2_air));
                constraints.push(AirExpression::Mul(
                    Box::new(diff_expr),
                    Box::new(one_minus_res),
                ));
            }
            IntPredicate::ULT | IntPredicate::UGT => {
                let op1_air_orig = lang_operand_to_air_expression(self.operand1);
                let op2_air_orig = lang_operand_to_air_expression(self.operand2);

                let a_expr = if self.cond == IntPredicate::ULT {
                    op1_air_orig.clone()
                } else {
                    op2_air_orig.clone()
                };
                let b_expr = if self.cond == IntPredicate::ULT {
                    op2_air_orig.clone()
                } else {
                    op1_air_orig.clone()
                };

                println!(
                    "ICMP {:?}: op_bitwidth = {}, a={:?}, b={:?}, res={:?}",
                    self.cond, self.operand_bitwidth, a_expr, b_expr, res_expr
                );

                let mut bit_vars_air_exprs = Vec::new();
                for i in 0..self.operand_bitwidth {
                    let bit_aux_var = ctx.new_aux_variable();
                    let bit_expr_aux = AirExpression::Trace(bit_aux_var, RowOffset::Current);
                    let bit_minus_one_aux = AirExpression::Sub(
                        Box::new(bit_expr_aux.clone()),
                        Box::new(AirExpression::Constant(1)),
                    );
                    constraints.push(AirExpression::Mul(
                        Box::new(bit_expr_aux.clone()),
                        Box::new(bit_minus_one_aux),
                    ));
                    bit_vars_air_exprs.push(bit_expr_aux);
                    println!(
                                    "  {:?}: Added booleanity for bit_aux_var {:?} (orig idx {}), trace col idx {}",
                                    self.cond, bit_aux_var, i, bit_aux_var.0
                                );
                }

                let mut d_sum_air: Option<Box<AirExpression>> = None;
                for (i, bit_expr_d) in bit_vars_air_exprs.iter().enumerate() {
                    let power_of_2 = 1u128 << i;
                    let term = AirExpression::Mul(
                        Box::new(bit_expr_d.clone()),
                        Box::new(AirExpression::Constant(power_of_2)),
                    );
                    d_sum_air = Some(match d_sum_air {
                        Some(current_sum) => {
                            Box::new(AirExpression::Add(current_sum, Box::new(term)))
                        }
                        None => Box::new(term),
                    });
                }
                let d_sum_air = d_sum_air.unwrap_or_else(|| Box::new(AirExpression::Constant(0)));
                println!("  {:?}: D_sum_air constructed: {:?}", self.cond, d_sum_air);

                let b_minus_a_minus_1 = AirExpression::Sub(
                    Box::new(AirExpression::Sub(
                        Box::new(b_expr.clone()),
                        Box::new(a_expr.clone()),
                    )),
                    Box::new(AirExpression::Constant(1)),
                );
                let term1_val = AirExpression::Sub(Box::new(b_minus_a_minus_1), d_sum_air.clone());
                constraints.push(AirExpression::Mul(
                    Box::new(res_expr.clone()),
                    Box::new(term1_val),
                ));
                println!("  {:?}: Constraint (res=1 path) generated.", self.cond);

                let one_minus_res = AirExpression::Sub(
                    Box::new(AirExpression::Constant(1)),
                    Box::new(res_expr.clone()),
                );
                let a_minus_b =
                    AirExpression::Sub(Box::new(a_expr.clone()), Box::new(b_expr.clone()));
                let term2_val = AirExpression::Sub(Box::new(a_minus_b), d_sum_air.clone());
                constraints.push(AirExpression::Mul(
                    Box::new(one_minus_res),
                    Box::new(term2_val),
                ));
                println!("  {:?}: Constraint (res=0 path) generated.", self.cond);
            }
            IntPredicate::ULE | IntPredicate::UGE => {
                let op1_air_orig = lang_operand_to_air_expression(self.operand1);
                let op2_air_orig = lang_operand_to_air_expression(self.operand2);

                let is_ule = self.cond == IntPredicate::ULE;
                let internal_predicate = if is_ule {
                    IntPredicate::UGT
                } else {
                    IntPredicate::ULT
                };

                println!(
                    "ICMP {:?}: Internally using {:?} with op_bitwidth = {}",
                    self.cond, internal_predicate, self.operand_bitwidth
                );

                let aux_res_var = ctx.new_aux_variable();
                let aux_res_expr = AirExpression::Trace(aux_res_var, RowOffset::Current);

                let aux_res_minus_one = AirExpression::Sub(
                    Box::new(aux_res_expr.clone()),
                    Box::new(AirExpression::Constant(1)),
                );
                constraints.push(AirExpression::Mul(
                    Box::new(aux_res_expr.clone()),
                    Box::new(aux_res_minus_one),
                ));
                println!(
                    "  {:?}: Added booleanity for aux_res_var {:?}",
                    self.cond, aux_res_var
                );

                let a_expr_internal: AirExpression;
                let b_expr_internal: AirExpression;

                if internal_predicate == IntPredicate::ULT {
                    a_expr_internal = op1_air_orig.clone();
                    b_expr_internal = op2_air_orig.clone();
                } else {
                    a_expr_internal = op2_air_orig.clone();
                    b_expr_internal = op1_air_orig.clone();
                }
                println!(
                                "  {:?}: Internal predicate {:?} uses a_internal={:?}, b_internal={:?}, aux_res={:?}",
                                self.cond,
                                internal_predicate,
                                a_expr_internal,
                                b_expr_internal,
                                aux_res_expr
                            );

                let mut bit_vars_air_exprs = Vec::new();
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
                    bit_vars_air_exprs.push(bit_expr_d);
                    println!(
                                    "    {:?}: Added booleanity for bit_aux_var {:?} (orig idx {}), trace col idx {}",
                                    self.cond, bit_aux_var, i, bit_aux_var.0
                                );
                }

                let mut d_sum_air: Option<Box<AirExpression>> = None;
                for (i, bit_expr_d) in bit_vars_air_exprs.iter().enumerate() {
                    let power_of_2 = 1u128 << i;
                    let term = AirExpression::Mul(
                        Box::new(bit_expr_d.clone()),
                        Box::new(AirExpression::Constant(power_of_2)),
                    );
                    d_sum_air = Some(match d_sum_air {
                        Some(current_sum) => {
                            Box::new(AirExpression::Add(current_sum, Box::new(term)))
                        }
                        None => Box::new(term),
                    });
                }
                let d_sum_air = d_sum_air.unwrap_or_else(|| Box::new(AirExpression::Constant(0)));
                println!(
                    "  {:?}: D_sum_air for internal op constructed: {:?}",
                    self.cond, d_sum_air
                );

                let b_i_minus_a_i_minus_1 = AirExpression::Sub(
                    Box::new(AirExpression::Sub(
                        Box::new(b_expr_internal.clone()),
                        Box::new(a_expr_internal.clone()),
                    )),
                    Box::new(AirExpression::Constant(1)),
                );
                let term1_val_internal =
                    AirExpression::Sub(Box::new(b_i_minus_a_i_minus_1), d_sum_air.clone());
                constraints.push(AirExpression::Mul(
                    Box::new(aux_res_expr.clone()),
                    Box::new(term1_val_internal),
                ));
                println!("  {:?}: Internal selector1 generated.", self.cond);

                let one_minus_aux_res = AirExpression::Sub(
                    Box::new(AirExpression::Constant(1)),
                    Box::new(aux_res_expr.clone()),
                );
                let a_i_minus_b_i = AirExpression::Sub(
                    Box::new(a_expr_internal.clone()),
                    Box::new(b_expr_internal.clone()),
                );
                let term2_val_internal =
                    AirExpression::Sub(Box::new(a_i_minus_b_i), d_sum_air.clone());
                constraints.push(AirExpression::Mul(
                    Box::new(one_minus_aux_res),
                    Box::new(term2_val_internal),
                ));
                println!("  {:?}: Internal selector2 generated.", self.cond);

                let sum_res_aux =
                    AirExpression::Add(Box::new(res_expr.clone()), Box::new(aux_res_expr.clone()));
                let final_relation_constraint =
                    AirExpression::Sub(Box::new(sum_res_aux), Box::new(AirExpression::Constant(1)));
                constraints.push(final_relation_constraint);
                println!(
                    "  {:?}: Final relation constraint (res + aux_res - 1 = 0) generated.",
                    self.cond
                );
            }
            IntPredicate::SLT => {
                let op1_air_orig = lang_operand_to_air_expression(self.operand1);
                let op2_air_orig = lang_operand_to_air_expression(self.operand2);

                println!(
                    "ICMP SLT: op_bitwidth = {}, op1={:?}, op2={:?}, res={:?}",
                    self.operand_bitwidth, op1_air_orig, op2_air_orig, res_expr
                );

                let mut op1_bit_vars_exprs = Vec::new();
                let mut op1_sum_terms = Vec::new();
                println!(
                    "  SLT: Decomposing op1 ({:?}) into {} bits",
                    op1_air_orig, self.operand_bitwidth
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
                    op1_bit_vars_exprs.push(bit_expr.clone());

                    let power_of_2 = 1u128 << i;
                    op1_sum_terms.push(AirExpression::Mul(
                        Box::new(bit_expr.clone()),
                        Box::new(AirExpression::Constant(power_of_2)),
                    ));
                    println!("    op1_bit_{} (trace col {}) created", i, bit_aux_var.0);
                }
                let op1_sum_from_bits = op1_sum_terms
                    .into_iter()
                    .reduce(|acc, term| AirExpression::Add(Box::new(acc), Box::new(term)))
                    .unwrap_or_else(|| AirExpression::Constant(0));
                constraints.push(AirExpression::Sub(
                    Box::new(op1_air_orig.clone()),
                    Box::new(op1_sum_from_bits),
                ));
                println!("  SLT: op1 decomposition constraint added.");

                let mut op2_bit_vars_exprs = Vec::new();
                let mut op2_sum_terms = Vec::new();
                println!(
                    "  SLT: Decomposing op2 ({:?}) into {} bits",
                    op2_air_orig, self.operand_bitwidth
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
                    op2_bit_vars_exprs.push(bit_expr.clone());

                    let power_of_2 = 1u128 << i;
                    op2_sum_terms.push(AirExpression::Mul(
                        Box::new(bit_expr.clone()),
                        Box::new(AirExpression::Constant(power_of_2)),
                    ));
                    println!("    op2_bit_{} (trace col {}) created", i, bit_aux_var.0);
                }
                let op2_sum_from_bits = op2_sum_terms
                    .into_iter()
                    .reduce(|acc, term| AirExpression::Add(Box::new(acc), Box::new(term)))
                    .unwrap_or_else(|| AirExpression::Constant(0));
                constraints.push(AirExpression::Sub(
                    Box::new(op2_air_orig.clone()),
                    Box::new(op2_sum_from_bits),
                ));
                println!("  SLT: op2 decomposition constraint added.");

                let a_msb_expr = op1_bit_vars_exprs
                    .last()
                    .expect("op1_bit_vars_exprs should not be empty for SLT")
                    .clone();
                let b_msb_expr = op2_bit_vars_exprs
                    .last()
                    .expect("op2_bit_vars_exprs should not be empty for SLT")
                    .clone();
                println!(
                    "  SLT: a_msb_expr={:?}, b_msb_expr={:?}",
                    a_msb_expr, b_msb_expr
                );

                let ult_ab_aux_res_var = ctx.new_aux_variable();
                let ult_ab_res_expr = AirExpression::Trace(ult_ab_aux_res_var, RowOffset::Current);
                println!(
                    "  SLT: ult_ab_aux_res_var (for ULT(op1,op2)) is {:?}",
                    ult_ab_aux_res_var
                );

                constraints.push(AirExpression::Mul(
                    Box::new(ult_ab_res_expr.clone()),
                    Box::new(AirExpression::Sub(
                        Box::new(ult_ab_res_expr.clone()),
                        Box::new(AirExpression::Constant(1)),
                    )),
                ));

                let mut ult_intern_bit_vars = Vec::new();
                for i_ult in 0..self.operand_bitwidth {
                    let ult_bit_aux = ctx.new_aux_variable();
                    let ult_bit_expr = AirExpression::Trace(ult_bit_aux, RowOffset::Current);
                    constraints.push(AirExpression::Mul(
                        Box::new(ult_bit_expr.clone()),
                        Box::new(AirExpression::Sub(
                            Box::new(ult_bit_expr.clone()),
                            Box::new(AirExpression::Constant(1)),
                        )),
                    ));
                    ult_intern_bit_vars.push(ult_bit_expr);
                    println!(
                        "    SLT->ULT: bit_{} (trace col {}) created",
                        i_ult, ult_bit_aux.0
                    );
                }
                let ult_d_sum = ult_intern_bit_vars.iter().enumerate().fold(
                    AirExpression::Constant(0),
                    |sum, (i, bit_e)| {
                        AirExpression::Add(
                            Box::new(sum),
                            Box::new(AirExpression::Mul(
                                Box::new(bit_e.clone()),
                                Box::new(AirExpression::Constant(1u128 << i)),
                            )),
                        )
                    },
                );
                let b_ult_minus_a_ult_minus_1 = AirExpression::Sub(
                    Box::new(AirExpression::Sub(
                        Box::new(op2_air_orig.clone()),
                        Box::new(op1_air_orig.clone()),
                    )),
                    Box::new(AirExpression::Constant(1)),
                );
                constraints.push(AirExpression::Mul(
                    Box::new(ult_ab_res_expr.clone()),
                    Box::new(AirExpression::Sub(
                        Box::new(b_ult_minus_a_ult_minus_1),
                        Box::new(ult_d_sum.clone()),
                    )),
                ));
                let a_ult_minus_b_ult = AirExpression::Sub(
                    Box::new(op2_air_orig.clone()),
                    Box::new(op1_air_orig.clone()),
                );
                constraints.push(AirExpression::Mul(
                    Box::new(AirExpression::Sub(
                        Box::new(AirExpression::Constant(1)),
                        Box::new(ult_ab_res_expr.clone()),
                    )),
                    Box::new(AirExpression::Sub(
                        Box::new(a_ult_minus_b_ult),
                        Box::new(ult_d_sum.clone()),
                    )),
                ));
                println!("  SLT: Constraints for internal ULT(op1,op2) added.");

                let b_is_pos_aux_var = ctx.new_aux_variable();
                let b_is_pos_expr = AirExpression::Trace(b_is_pos_aux_var, RowOffset::Current);
                constraints.push(AirExpression::Mul(
                    Box::new(b_is_pos_expr.clone()),
                    Box::new(AirExpression::Sub(
                        Box::new(b_is_pos_expr.clone()),
                        Box::new(AirExpression::Constant(1)),
                    )),
                ));
                constraints.push(AirExpression::Sub(
                    Box::new(b_is_pos_expr.clone()),
                    Box::new(AirExpression::Sub(
                        Box::new(AirExpression::Constant(1)),
                        Box::new(b_msb_expr.clone()),
                    )),
                ));
                println!(
                    "  SLT: b_is_pos_expr (trace col {}) created from b_msb_expr.",
                    b_is_pos_aux_var.0
                );

                let cond1_aux_var = ctx.new_aux_variable();
                let cond1_expr = AirExpression::Trace(cond1_aux_var, RowOffset::Current);
                constraints.push(AirExpression::Mul(
                    Box::new(cond1_expr.clone()),
                    Box::new(AirExpression::Sub(
                        Box::new(cond1_expr.clone()),
                        Box::new(AirExpression::Constant(1)),
                    )),
                ));
                constraints.push(AirExpression::Sub(
                    Box::new(cond1_expr.clone()),
                    Box::new(AirExpression::Mul(
                        Box::new(a_msb_expr.clone()),
                        Box::new(b_is_pos_expr.clone()),
                    )),
                ));
                println!("  SLT: cond1_expr (trace col {}) created.", cond1_aux_var.0);

                let signs_eq_aux_var = ctx.new_aux_variable();
                let signs_eq_expr = AirExpression::Trace(signs_eq_aux_var, RowOffset::Current);
                constraints.push(AirExpression::Mul(
                    Box::new(signs_eq_expr.clone()),
                    Box::new(AirExpression::Sub(
                        Box::new(signs_eq_expr.clone()),
                        Box::new(AirExpression::Constant(1)),
                    )),
                ));

                let term_ab =
                    AirExpression::Mul(Box::new(a_msb_expr.clone()), Box::new(b_msb_expr.clone()));
                let term_not_a_not_b = AirExpression::Mul(
                    Box::new(AirExpression::Sub(
                        Box::new(AirExpression::Constant(1)),
                        Box::new(a_msb_expr.clone()),
                    )),
                    Box::new(AirExpression::Sub(
                        Box::new(AirExpression::Constant(1)),
                        Box::new(b_msb_expr.clone()),
                    )),
                );
                constraints.push(AirExpression::Sub(
                    Box::new(signs_eq_expr.clone()),
                    Box::new(AirExpression::Add(
                        Box::new(term_ab),
                        Box::new(term_not_a_not_b),
                    )),
                ));
                println!(
                    "  SLT: signs_eq_expr (trace col {}) created.",
                    signs_eq_aux_var.0
                );

                let cond2_aux_var = ctx.new_aux_variable();
                let cond2_expr = AirExpression::Trace(cond2_aux_var, RowOffset::Current);
                constraints.push(AirExpression::Mul(
                    Box::new(cond2_expr.clone()),
                    Box::new(AirExpression::Sub(
                        Box::new(cond2_expr.clone()),
                        Box::new(AirExpression::Constant(1)),
                    )),
                ));
                constraints.push(AirExpression::Sub(
                    Box::new(cond2_expr.clone()),
                    Box::new(AirExpression::Mul(
                        Box::new(signs_eq_expr.clone()),
                        Box::new(ult_ab_res_expr.clone()),
                    )),
                ));
                println!("  SLT: cond2_expr (trace col {}) created.", cond2_aux_var.0);

                let sum_conds =
                    AirExpression::Add(Box::new(cond1_expr.clone()), Box::new(cond2_expr.clone()));
                let prod_conds =
                    AirExpression::Mul(Box::new(cond1_expr.clone()), Box::new(cond2_expr.clone()));
                let or_expr_val = AirExpression::Sub(Box::new(sum_conds), Box::new(prod_conds));
                constraints.push(AirExpression::Sub(
                    Box::new(res_expr.clone()),
                    Box::new(or_expr_val),
                ));
                println!("  SLT: Final OR constraint for result added.");
            }
            IntPredicate::SGT => {
                let op1_air_orig = lang_operand_to_air_expression(self.operand1);
                let op2_air_orig = lang_operand_to_air_expression(self.operand2);

                println!(
                    "ICMP SGT: op_bitwidth = {}, op1={:?}, op2={:?}, res={:?}",
                    self.operand_bitwidth, op1_air_orig, op2_air_orig, res_expr
                );

                let mut slt_a_bit_vars_exprs = Vec::new();
                let mut slt_a_sum_terms = Vec::new();
                for i in 0..self.operand_bitwidth {
                    let bit_aux_var = ctx.new_aux_variable();
                    let bit_expr = AirExpression::Trace(bit_aux_var, RowOffset::Current);
                    constraints.push(AirExpression::Mul(
                        Box::new(bit_expr.clone()),
                        Box::new(AirExpression::Sub(
                            Box::new(bit_expr.clone()),
                            Box::new(AirExpression::Constant(1)),
                        )),
                    ));
                    slt_a_bit_vars_exprs.push(bit_expr.clone());
                    slt_a_sum_terms.push(AirExpression::Mul(
                        Box::new(bit_expr.clone()),
                        Box::new(AirExpression::Constant(1u128 << i)),
                    ));
                }
                let slt_a_sum_from_bits = slt_a_sum_terms
                    .into_iter()
                    .reduce(|acc, term| AirExpression::Add(Box::new(acc), Box::new(term)))
                    .unwrap_or_else(|| AirExpression::Constant(0));
                constraints.push(AirExpression::Sub(
                    Box::new(op2_air_orig.clone()),
                    Box::new(slt_a_sum_from_bits),
                ));

                let mut slt_b_bit_vars_exprs = Vec::new();
                let mut slt_b_sum_terms = Vec::new();
                for i in 0..self.operand_bitwidth {
                    let bit_aux_var = ctx.new_aux_variable();
                    let bit_expr = AirExpression::Trace(bit_aux_var, RowOffset::Current);
                    constraints.push(AirExpression::Mul(
                        Box::new(bit_expr.clone()),
                        Box::new(AirExpression::Sub(
                            Box::new(bit_expr.clone()),
                            Box::new(AirExpression::Constant(1)),
                        )),
                    ));
                    slt_b_bit_vars_exprs.push(bit_expr.clone());
                    slt_b_sum_terms.push(AirExpression::Mul(
                        Box::new(bit_expr.clone()),
                        Box::new(AirExpression::Constant(1u128 << i)),
                    ));
                }
                let slt_b_sum_from_bits = slt_b_sum_terms
                    .into_iter()
                    .reduce(|acc, term| AirExpression::Add(Box::new(acc), Box::new(term)))
                    .unwrap_or_else(|| AirExpression::Constant(0));
                constraints.push(AirExpression::Sub(
                    Box::new(op1_air_orig.clone()),
                    Box::new(slt_b_sum_from_bits),
                ));

                let slt_a_msb_expr = slt_a_bit_vars_exprs.last().unwrap().clone();
                let slt_b_msb_expr = slt_b_bit_vars_exprs.last().unwrap().clone();

                let ult_slt_ab_aux_res_var = ctx.new_aux_variable();
                let ult_slt_ab_res_expr =
                    AirExpression::Trace(ult_slt_ab_aux_res_var, RowOffset::Current);
                constraints.push(AirExpression::Mul(
                    Box::new(ult_slt_ab_res_expr.clone()),
                    Box::new(AirExpression::Sub(
                        Box::new(ult_slt_ab_res_expr.clone()),
                        Box::new(AirExpression::Constant(1)),
                    )),
                ));

                let mut ult_slt_intern_bit_vars = Vec::new();
                for _ in 0..self.operand_bitwidth {
                    let bit_aux = ctx.new_aux_variable();
                    ult_slt_intern_bit_vars.push(AirExpression::Trace(bit_aux, RowOffset::Current));
                    constraints.push(AirExpression::Mul(
                        Box::new(ult_slt_intern_bit_vars.last().unwrap().clone()),
                        Box::new(AirExpression::Sub(
                            Box::new(ult_slt_intern_bit_vars.last().unwrap().clone()),
                            Box::new(AirExpression::Constant(1)),
                        )),
                    ));
                }
                let ult_slt_d_sum = ult_slt_intern_bit_vars.iter().enumerate().fold(
                    AirExpression::Constant(0),
                    |sum, (i, bit_e)| {
                        AirExpression::Add(
                            Box::new(sum),
                            Box::new(AirExpression::Mul(
                                Box::new(bit_e.clone()),
                                Box::new(AirExpression::Constant(1u128 << i)),
                            )),
                        )
                    },
                );

                let b_ult_minus_a_ult_minus_1 = AirExpression::Sub(
                    Box::new(AirExpression::Sub(
                        Box::new(op1_air_orig.clone()),
                        Box::new(op2_air_orig.clone()),
                    )),
                    Box::new(AirExpression::Constant(1)),
                );
                constraints.push(AirExpression::Mul(
                    Box::new(ult_slt_ab_res_expr.clone()),
                    Box::new(AirExpression::Sub(
                        Box::new(b_ult_minus_a_ult_minus_1),
                        Box::new(ult_slt_d_sum.clone()),
                    )),
                ));
                let a_ult_minus_b_ult = AirExpression::Sub(
                    Box::new(op2_air_orig.clone()),
                    Box::new(op1_air_orig.clone()),
                );
                constraints.push(AirExpression::Mul(
                    Box::new(AirExpression::Sub(
                        Box::new(AirExpression::Constant(1)),
                        Box::new(ult_slt_ab_res_expr.clone()),
                    )),
                    Box::new(AirExpression::Sub(
                        Box::new(a_ult_minus_b_ult),
                        Box::new(ult_slt_d_sum.clone()),
                    )),
                ));

                let slt_b_is_pos_aux_var = ctx.new_aux_variable();
                let slt_b_is_pos_expr =
                    AirExpression::Trace(slt_b_is_pos_aux_var, RowOffset::Current);
                constraints.push(AirExpression::Mul(
                    Box::new(slt_b_is_pos_expr.clone()),
                    Box::new(AirExpression::Sub(
                        Box::new(slt_b_is_pos_expr.clone()),
                        Box::new(AirExpression::Constant(1)),
                    )),
                ));
                constraints.push(AirExpression::Sub(
                    Box::new(slt_b_is_pos_expr.clone()),
                    Box::new(AirExpression::Sub(
                        Box::new(AirExpression::Constant(1)),
                        Box::new(slt_b_msb_expr.clone()),
                    )),
                ));

                let slt_cond1_aux_var = ctx.new_aux_variable();
                let slt_cond1_expr = AirExpression::Trace(slt_cond1_aux_var, RowOffset::Current);
                constraints.push(AirExpression::Mul(
                    Box::new(slt_cond1_expr.clone()),
                    Box::new(AirExpression::Sub(
                        Box::new(slt_cond1_expr.clone()),
                        Box::new(AirExpression::Constant(1)),
                    )),
                ));
                constraints.push(AirExpression::Sub(
                    Box::new(slt_cond1_expr.clone()),
                    Box::new(AirExpression::Mul(
                        Box::new(slt_a_msb_expr.clone()),
                        Box::new(slt_b_is_pos_expr.clone()),
                    )),
                ));

                let slt_signs_eq_aux_var = ctx.new_aux_variable();
                let slt_signs_eq_expr =
                    AirExpression::Trace(slt_signs_eq_aux_var, RowOffset::Current);
                constraints.push(AirExpression::Mul(
                    Box::new(slt_signs_eq_expr.clone()),
                    Box::new(AirExpression::Sub(
                        Box::new(slt_signs_eq_expr.clone()),
                        Box::new(AirExpression::Constant(1)),
                    )),
                ));
                let slt_term_ab = AirExpression::Mul(
                    Box::new(slt_a_msb_expr.clone()),
                    Box::new(slt_b_msb_expr.clone()),
                );
                let slt_term_not_a_not_b = AirExpression::Mul(
                    Box::new(AirExpression::Sub(
                        Box::new(AirExpression::Constant(1)),
                        Box::new(slt_a_msb_expr.clone()),
                    )),
                    Box::new(AirExpression::Sub(
                        Box::new(AirExpression::Constant(1)),
                        Box::new(slt_b_msb_expr.clone()),
                    )),
                );
                constraints.push(AirExpression::Sub(
                    Box::new(slt_signs_eq_expr.clone()),
                    Box::new(AirExpression::Add(
                        Box::new(slt_term_ab),
                        Box::new(slt_term_not_a_not_b),
                    )),
                ));

                let slt_cond2_aux_var = ctx.new_aux_variable();
                let slt_cond2_expr = AirExpression::Trace(slt_cond2_aux_var, RowOffset::Current);
                constraints.push(AirExpression::Mul(
                    Box::new(slt_cond2_expr.clone()),
                    Box::new(AirExpression::Sub(
                        Box::new(slt_cond2_expr.clone()),
                        Box::new(AirExpression::Constant(1)),
                    )),
                ));
                constraints.push(AirExpression::Sub(
                    Box::new(slt_cond2_expr.clone()),
                    Box::new(AirExpression::Mul(
                        Box::new(slt_signs_eq_expr.clone()),
                        Box::new(ult_slt_ab_res_expr.clone()),
                    )),
                ));

                let slt_sum_conds = AirExpression::Add(
                    Box::new(slt_cond1_expr.clone()),
                    Box::new(slt_cond2_expr.clone()),
                );
                let slt_prod_conds = AirExpression::Mul(
                    Box::new(slt_cond1_expr.clone()),
                    Box::new(slt_cond2_expr.clone()),
                );
                let slt_or_expr_val =
                    AirExpression::Sub(Box::new(slt_sum_conds), Box::new(slt_prod_conds));

                constraints.push(AirExpression::Sub(
                    Box::new(res_expr.clone()),
                    Box::new(slt_or_expr_val),
                ));
                println!(
                    "  SGT: Logic for SLT(op2,op1) generated, result mapped to SGT's res_expr."
                );
            }
            IntPredicate::SGE => {
                let op1_air_orig = lang_operand_to_air_expression(self.operand1);
                let op2_air_orig = lang_operand_to_air_expression(self.operand2);

                println!(
                    "ICMP SGE: op_bitwidth = {}, op1={:?}, op2={:?}, res={:?}",
                    self.operand_bitwidth, op1_air_orig, op2_air_orig, res_expr
                );

                let slt_aux_res_var = ctx.new_aux_variable();
                let slt_aux_res_expr = AirExpression::Trace(slt_aux_res_var, RowOffset::Current);
                constraints.push(AirExpression::Mul(
                    Box::new(slt_aux_res_expr.clone()),
                    Box::new(AirExpression::Sub(
                        Box::new(slt_aux_res_expr.clone()),
                        Box::new(AirExpression::Constant(1)),
                    )),
                ));
                println!(
                    "  SGE: Created slt_aux_res_var {:?} for internal SLT(op1,op2)",
                    slt_aux_res_var
                );

                let mut slt_a_bit_vars_exprs = Vec::new();
                let mut slt_a_sum_terms = Vec::new();
                for i in 0..self.operand_bitwidth {
                    let bit_aux_var = ctx.new_aux_variable();
                    let bit_expr = AirExpression::Trace(bit_aux_var, RowOffset::Current);
                    constraints.push(AirExpression::Mul(
                        Box::new(bit_expr.clone()),
                        Box::new(AirExpression::Sub(
                            Box::new(bit_expr.clone()),
                            Box::new(AirExpression::Constant(1)),
                        )),
                    ));
                    slt_a_bit_vars_exprs.push(bit_expr.clone());
                    slt_a_sum_terms.push(AirExpression::Mul(
                        Box::new(bit_expr.clone()),
                        Box::new(AirExpression::Constant(1u128 << i)),
                    ));
                }
                let slt_a_sum_from_bits = slt_a_sum_terms
                    .into_iter()
                    .reduce(|acc, term| AirExpression::Add(Box::new(acc), Box::new(term)))
                    .unwrap_or_else(|| AirExpression::Constant(0));
                constraints.push(AirExpression::Sub(
                    Box::new(op1_air_orig.clone()),
                    Box::new(slt_a_sum_from_bits),
                ));

                let mut slt_b_bit_vars_exprs = Vec::new();
                let mut slt_b_sum_terms = Vec::new();
                for i in 0..self.operand_bitwidth {
                    let bit_aux_var = ctx.new_aux_variable();
                    let bit_expr = AirExpression::Trace(bit_aux_var, RowOffset::Current);
                    constraints.push(AirExpression::Mul(
                        Box::new(bit_expr.clone()),
                        Box::new(AirExpression::Sub(
                            Box::new(bit_expr.clone()),
                            Box::new(AirExpression::Constant(1)),
                        )),
                    ));
                    slt_b_bit_vars_exprs.push(bit_expr.clone());
                    slt_b_sum_terms.push(AirExpression::Mul(
                        Box::new(bit_expr.clone()),
                        Box::new(AirExpression::Constant(1u128 << i)),
                    ));
                }
                let slt_b_sum_from_bits = slt_b_sum_terms
                    .into_iter()
                    .reduce(|acc, term| AirExpression::Add(Box::new(acc), Box::new(term)))
                    .unwrap_or_else(|| AirExpression::Constant(0));
                constraints.push(AirExpression::Sub(
                    Box::new(op2_air_orig.clone()),
                    Box::new(slt_b_sum_from_bits),
                ));

                let a_msb_expr = slt_a_bit_vars_exprs
                    .last()
                    .expect("slt_a_bit_vars_exprs should not be empty for SGE->SLT")
                    .clone();
                let b_msb_expr = slt_b_bit_vars_exprs
                    .last()
                    .expect("slt_b_bit_vars_exprs should not be empty for SGE->SLT")
                    .clone();

                let ult_ab_aux_res_var = ctx.new_aux_variable();
                let ult_ab_res_expr = AirExpression::Trace(ult_ab_aux_res_var, RowOffset::Current);
                constraints.push(AirExpression::Mul(
                    Box::new(ult_ab_res_expr.clone()),
                    Box::new(AirExpression::Sub(
                        Box::new(ult_ab_res_expr.clone()),
                        Box::new(AirExpression::Constant(1)),
                    )),
                ));
                let mut ult_intern_bit_vars = Vec::new();
                for _ in 0..self.operand_bitwidth {
                    let bit_aux = ctx.new_aux_variable();
                    let current_bit_expr = AirExpression::Trace(bit_aux, RowOffset::Current);
                    constraints.push(AirExpression::Mul(
                        Box::new(current_bit_expr.clone()),
                        Box::new(AirExpression::Sub(
                            Box::new(current_bit_expr.clone()),
                            Box::new(AirExpression::Constant(1)),
                        )),
                    ));
                    ult_intern_bit_vars.push(current_bit_expr);
                }
                let ult_d_sum = ult_intern_bit_vars.iter().enumerate().fold(
                    AirExpression::Constant(0),
                    |sum, (i, bit_e)| {
                        AirExpression::Add(
                            Box::new(sum),
                            Box::new(AirExpression::Mul(
                                Box::new(bit_e.clone()),
                                Box::new(AirExpression::Constant(1u128 << i)),
                            )),
                        )
                    },
                );

                let b_ult_minus_a_ult_minus_1 = AirExpression::Sub(
                    Box::new(AirExpression::Sub(
                        Box::new(op2_air_orig.clone()),
                        Box::new(op1_air_orig.clone()),
                    )),
                    Box::new(AirExpression::Constant(1)),
                );
                constraints.push(AirExpression::Mul(
                    Box::new(ult_ab_res_expr.clone()),
                    Box::new(AirExpression::Sub(
                        Box::new(b_ult_minus_a_ult_minus_1),
                        Box::new(ult_d_sum.clone()),
                    )),
                ));
                let a_ult_minus_b_ult = AirExpression::Sub(
                    Box::new(op1_air_orig.clone()),
                    Box::new(op2_air_orig.clone()),
                );
                constraints.push(AirExpression::Mul(
                    Box::new(AirExpression::Sub(
                        Box::new(AirExpression::Constant(1)),
                        Box::new(ult_ab_res_expr.clone()),
                    )),
                    Box::new(AirExpression::Sub(
                        Box::new(a_ult_minus_b_ult),
                        Box::new(ult_d_sum.clone()),
                    )),
                ));

                let b_is_pos_expr_slt = {
                    let aux_var = ctx.new_aux_variable();
                    let expr = AirExpression::Trace(aux_var, RowOffset::Current);
                    constraints.push(AirExpression::Mul(
                        Box::new(expr.clone()),
                        Box::new(AirExpression::Sub(
                            Box::new(expr.clone()),
                            Box::new(AirExpression::Constant(1)),
                        )),
                    ));
                    constraints.push(AirExpression::Sub(
                        Box::new(expr.clone()),
                        Box::new(AirExpression::Sub(
                            Box::new(AirExpression::Constant(1)),
                            Box::new(b_msb_expr.clone()),
                        )),
                    ));
                    expr
                };
                let cond1_expr_slt = {
                    let aux_var = ctx.new_aux_variable();
                    let expr = AirExpression::Trace(aux_var, RowOffset::Current);
                    constraints.push(AirExpression::Mul(
                        Box::new(expr.clone()),
                        Box::new(AirExpression::Sub(
                            Box::new(expr.clone()),
                            Box::new(AirExpression::Constant(1)),
                        )),
                    ));
                    constraints.push(AirExpression::Sub(
                        Box::new(expr.clone()),
                        Box::new(AirExpression::Mul(
                            Box::new(a_msb_expr.clone()),
                            Box::new(b_is_pos_expr_slt.clone()),
                        )),
                    ));
                    expr
                };
                let signs_eq_expr_slt = {
                    let aux_var = ctx.new_aux_variable();
                    let expr = AirExpression::Trace(aux_var, RowOffset::Current);
                    constraints.push(AirExpression::Mul(
                        Box::new(expr.clone()),
                        Box::new(AirExpression::Sub(
                            Box::new(expr.clone()),
                            Box::new(AirExpression::Constant(1)),
                        )),
                    ));
                    let term_ab = AirExpression::Mul(
                        Box::new(a_msb_expr.clone()),
                        Box::new(b_msb_expr.clone()),
                    );
                    let term_not_a_not_b = AirExpression::Mul(
                        Box::new(AirExpression::Sub(
                            Box::new(AirExpression::Constant(1)),
                            Box::new(a_msb_expr.clone()),
                        )),
                        Box::new(AirExpression::Sub(
                            Box::new(AirExpression::Constant(1)),
                            Box::new(b_msb_expr.clone()),
                        )),
                    );
                    constraints.push(AirExpression::Sub(
                        Box::new(expr.clone()),
                        Box::new(AirExpression::Add(
                            Box::new(term_ab),
                            Box::new(term_not_a_not_b),
                        )),
                    ));
                    expr
                };
                let cond2_expr_slt = {
                    let aux_var = ctx.new_aux_variable();
                    let expr = AirExpression::Trace(aux_var, RowOffset::Current);
                    constraints.push(AirExpression::Mul(
                        Box::new(expr.clone()),
                        Box::new(AirExpression::Sub(
                            Box::new(expr.clone()),
                            Box::new(AirExpression::Constant(1)),
                        )),
                    ));
                    constraints.push(AirExpression::Sub(
                        Box::new(expr.clone()),
                        Box::new(AirExpression::Mul(
                            Box::new(signs_eq_expr_slt.clone()),
                            Box::new(ult_ab_res_expr.clone()),
                        )),
                    ));
                    expr
                };
                let sum_conds_slt = AirExpression::Add(
                    Box::new(cond1_expr_slt.clone()),
                    Box::new(cond2_expr_slt.clone()),
                );
                let prod_conds_slt = AirExpression::Mul(
                    Box::new(cond1_expr_slt.clone()),
                    Box::new(cond2_expr_slt.clone()),
                );
                let or_expr_val_slt =
                    AirExpression::Sub(Box::new(sum_conds_slt), Box::new(prod_conds_slt));
                constraints.push(AirExpression::Sub(
                    Box::new(slt_aux_res_expr.clone()),
                    Box::new(or_expr_val_slt),
                ));

                constraints.push(AirExpression::Sub(
                    Box::new(res_expr.clone()),
                    Box::new(AirExpression::Sub(
                        Box::new(AirExpression::Constant(1)),
                        Box::new(slt_aux_res_expr.clone()),
                    )),
                ));
                println!(
                                "  SGE: Logic for SLT(op1,op2) generated into aux var, SGE result is NOT of aux."
                            );
            }
            IntPredicate::SLE => {
                let op1_air_orig = lang_operand_to_air_expression(self.operand1);
                let op2_air_orig = lang_operand_to_air_expression(self.operand2);

                println!(
                    "ICMP SLE: op_bitwidth = {}, op1={:?}, op2={:?}, res={:?}",
                    self.operand_bitwidth, op1_air_orig, op2_air_orig, res_expr
                );

                let sgt_aux_res_var = ctx.new_aux_variable();
                let sgt_aux_res_expr = AirExpression::Trace(sgt_aux_res_var, RowOffset::Current);
                constraints.push(AirExpression::Mul(
                    Box::new(sgt_aux_res_expr.clone()),
                    Box::new(AirExpression::Sub(
                        Box::new(sgt_aux_res_expr.clone()),
                        Box::new(AirExpression::Constant(1)),
                    )),
                ));
                println!(
                    "  SLE: Created sgt_aux_res_var {:?} for internal SGT(op1,op2)",
                    sgt_aux_res_var
                );

                let mut slt_a_bit_vars_exprs = Vec::new();
                let mut slt_a_sum_terms = Vec::new();
                for i in 0..self.operand_bitwidth {
                    let bit_aux_var = ctx.new_aux_variable();
                    let bit_expr = AirExpression::Trace(bit_aux_var, RowOffset::Current);
                    constraints.push(AirExpression::Mul(
                        Box::new(bit_expr.clone()),
                        Box::new(AirExpression::Sub(
                            Box::new(bit_expr.clone()),
                            Box::new(AirExpression::Constant(1)),
                        )),
                    ));
                    slt_a_bit_vars_exprs.push(bit_expr.clone());
                    slt_a_sum_terms.push(AirExpression::Mul(
                        Box::new(bit_expr.clone()),
                        Box::new(AirExpression::Constant(1u128 << i)),
                    ));
                }
                let slt_a_sum_from_bits = slt_a_sum_terms
                    .into_iter()
                    .reduce(|acc, term| AirExpression::Add(Box::new(acc), Box::new(term)))
                    .unwrap_or_else(|| AirExpression::Constant(0));
                constraints.push(AirExpression::Sub(
                    Box::new(op2_air_orig.clone()),
                    Box::new(slt_a_sum_from_bits),
                ));

                let mut slt_b_bit_vars_exprs = Vec::new();
                let mut slt_b_sum_terms = Vec::new();
                for i in 0..self.operand_bitwidth {
                    let bit_aux_var = ctx.new_aux_variable();
                    let bit_expr = AirExpression::Trace(bit_aux_var, RowOffset::Current);
                    constraints.push(AirExpression::Mul(
                        Box::new(bit_expr.clone()),
                        Box::new(AirExpression::Sub(
                            Box::new(bit_expr.clone()),
                            Box::new(AirExpression::Constant(1)),
                        )),
                    ));
                    slt_b_bit_vars_exprs.push(bit_expr.clone());
                    slt_b_sum_terms.push(AirExpression::Mul(
                        Box::new(bit_expr.clone()),
                        Box::new(AirExpression::Constant(1u128 << i)),
                    ));
                }
                let slt_b_sum_from_bits = slt_b_sum_terms
                    .into_iter()
                    .reduce(|acc, term| AirExpression::Add(Box::new(acc), Box::new(term)))
                    .unwrap_or_else(|| AirExpression::Constant(0));
                constraints.push(AirExpression::Sub(
                    Box::new(op1_air_orig.clone()),
                    Box::new(slt_b_sum_from_bits),
                ));

                let a_msb_expr_for_slt_op2_op1 = slt_a_bit_vars_exprs
                    .last()
                    .expect("slt_a_bit_vars_exprs should not be empty for SLE->SGT->SLT")
                    .clone();
                let b_msb_expr_for_slt_op2_op1 = slt_b_bit_vars_exprs
                    .last()
                    .expect("slt_b_bit_vars_exprs should not be empty for SLE->SGT->SLT")
                    .clone();

                let ult_for_slt_op2_op1_aux_res_var = ctx.new_aux_variable();
                let ult_for_slt_op2_op1_res_expr =
                    AirExpression::Trace(ult_for_slt_op2_op1_aux_res_var, RowOffset::Current);
                constraints.push(AirExpression::Mul(
                    Box::new(ult_for_slt_op2_op1_res_expr.clone()),
                    Box::new(AirExpression::Sub(
                        Box::new(ult_for_slt_op2_op1_res_expr.clone()),
                        Box::new(AirExpression::Constant(1)),
                    )),
                ));
                let mut ult_intern_bits_for_slt_op2_op1 = Vec::new();
                for _ in 0..self.operand_bitwidth {
                    let bit_aux = ctx.new_aux_variable();
                    let current_bit_expr = AirExpression::Trace(bit_aux, RowOffset::Current);
                    constraints.push(AirExpression::Mul(
                        Box::new(current_bit_expr.clone()),
                        Box::new(AirExpression::Sub(
                            Box::new(current_bit_expr.clone()),
                            Box::new(AirExpression::Constant(1)),
                        )),
                    ));
                    ult_intern_bits_for_slt_op2_op1.push(current_bit_expr);
                }
                let d_sum_for_slt_op2_op1 = ult_intern_bits_for_slt_op2_op1
                    .iter()
                    .enumerate()
                    .fold(AirExpression::Constant(0), |sum, (i, bit_e)| {
                        AirExpression::Add(
                            Box::new(sum),
                            Box::new(AirExpression::Mul(
                                Box::new(bit_e.clone()),
                                Box::new(AirExpression::Constant(1u128 << i)),
                            )),
                        )
                    });

                let b_ult_minus_a_ult_minus_1 = AirExpression::Sub(
                    Box::new(AirExpression::Sub(
                        Box::new(op1_air_orig.clone()),
                        Box::new(op2_air_orig.clone()),
                    )),
                    Box::new(AirExpression::Constant(1)),
                );
                constraints.push(AirExpression::Mul(
                    Box::new(ult_for_slt_op2_op1_res_expr.clone()),
                    Box::new(AirExpression::Sub(
                        Box::new(b_ult_minus_a_ult_minus_1),
                        Box::new(d_sum_for_slt_op2_op1.clone()),
                    )),
                ));
                let a_ult_minus_b_ult = AirExpression::Sub(
                    Box::new(op2_air_orig.clone()),
                    Box::new(op1_air_orig.clone()),
                );
                constraints.push(AirExpression::Mul(
                    Box::new(AirExpression::Sub(
                        Box::new(AirExpression::Constant(1)),
                        Box::new(ult_for_slt_op2_op1_res_expr.clone()),
                    )),
                    Box::new(AirExpression::Sub(
                        Box::new(a_ult_minus_b_ult),
                        Box::new(d_sum_for_slt_op2_op1.clone()),
                    )),
                ));

                let b_is_pos_for_slt_op2_op1 = {
                    let aux_var = ctx.new_aux_variable();
                    let expr = AirExpression::Trace(aux_var, RowOffset::Current);
                    constraints.push(AirExpression::Mul(
                        Box::new(expr.clone()),
                        Box::new(AirExpression::Sub(
                            Box::new(expr.clone()),
                            Box::new(AirExpression::Constant(1)),
                        )),
                    ));
                    constraints.push(AirExpression::Sub(
                        Box::new(expr.clone()),
                        Box::new(AirExpression::Sub(
                            Box::new(AirExpression::Constant(1)),
                            Box::new(b_msb_expr_for_slt_op2_op1.clone()),
                        )),
                    ));
                    expr
                };
                let cond1_for_slt_op2_op1 = {
                    let aux_var = ctx.new_aux_variable();
                    let expr = AirExpression::Trace(aux_var, RowOffset::Current);
                    constraints.push(AirExpression::Mul(
                        Box::new(expr.clone()),
                        Box::new(AirExpression::Sub(
                            Box::new(expr.clone()),
                            Box::new(AirExpression::Constant(1)),
                        )),
                    ));
                    constraints.push(AirExpression::Sub(
                        Box::new(expr.clone()),
                        Box::new(AirExpression::Mul(
                            Box::new(a_msb_expr_for_slt_op2_op1.clone()),
                            Box::new(b_is_pos_for_slt_op2_op1.clone()),
                        )),
                    ));
                    expr
                };
                let signs_eq_for_slt_op2_op1 = {
                    let aux_var = ctx.new_aux_variable();
                    let expr = AirExpression::Trace(aux_var, RowOffset::Current);
                    constraints.push(AirExpression::Mul(
                        Box::new(expr.clone()),
                        Box::new(AirExpression::Sub(
                            Box::new(expr.clone()),
                            Box::new(AirExpression::Constant(1)),
                        )),
                    ));
                    let term_ab = AirExpression::Mul(
                        Box::new(a_msb_expr_for_slt_op2_op1.clone()),
                        Box::new(b_msb_expr_for_slt_op2_op1.clone()),
                    );
                    let term_not_a_not_b = AirExpression::Mul(
                        Box::new(AirExpression::Sub(
                            Box::new(AirExpression::Constant(1)),
                            Box::new(a_msb_expr_for_slt_op2_op1.clone()),
                        )),
                        Box::new(AirExpression::Sub(
                            Box::new(AirExpression::Constant(1)),
                            Box::new(b_msb_expr_for_slt_op2_op1.clone()),
                        )),
                    );
                    constraints.push(AirExpression::Sub(
                        Box::new(expr.clone()),
                        Box::new(AirExpression::Add(
                            Box::new(term_ab),
                            Box::new(term_not_a_not_b),
                        )),
                    ));
                    expr
                };
                let cond2_for_slt_op2_op1 = {
                    let aux_var = ctx.new_aux_variable();
                    let expr = AirExpression::Trace(aux_var, RowOffset::Current);
                    constraints.push(AirExpression::Mul(
                        Box::new(expr.clone()),
                        Box::new(AirExpression::Sub(
                            Box::new(expr.clone()),
                            Box::new(AirExpression::Constant(1)),
                        )),
                    ));
                    constraints.push(AirExpression::Sub(
                        Box::new(expr.clone()),
                        Box::new(AirExpression::Mul(
                            Box::new(signs_eq_for_slt_op2_op1.clone()),
                            Box::new(ult_for_slt_op2_op1_res_expr.clone()),
                        )),
                    ));
                    expr
                };
                let sum_conds_slt_op2_op1 = AirExpression::Add(
                    Box::new(cond1_for_slt_op2_op1.clone()),
                    Box::new(cond2_for_slt_op2_op1.clone()),
                );
                let prod_conds_slt_op2_op1 = AirExpression::Mul(
                    Box::new(cond1_for_slt_op2_op1.clone()),
                    Box::new(cond2_for_slt_op2_op1.clone()),
                );
                let or_val_slt_op2_op1 = AirExpression::Sub(
                    Box::new(sum_conds_slt_op2_op1),
                    Box::new(prod_conds_slt_op2_op1),
                );

                constraints.push(AirExpression::Sub(
                    Box::new(sgt_aux_res_expr.clone()),
                    Box::new(or_val_slt_op2_op1),
                ));

                constraints.push(AirExpression::Sub(
                    Box::new(res_expr.clone()),
                    Box::new(AirExpression::Sub(
                        Box::new(AirExpression::Constant(1)),
                        Box::new(sgt_aux_res_expr.clone()),
                    )),
                ));
                println!(
                                "  SLE: Logic for SGT(op1,op2) generated into aux var, SLE result is NOT of aux."
                            );
            }
        }
    }
}

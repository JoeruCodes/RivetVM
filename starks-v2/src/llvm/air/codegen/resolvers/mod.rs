use std::collections::HashMap;

use fp::setup_sem_aux_vars;
use lang::{FloatPredicate, Operand, StructuredAirConstraint};

use super::super::codegen::resolvers::fp::{
    fp_add, fp_icmp_neq, fp_icmp_ule, fp_icmp_ult, fp_is_inf, fp_is_nan, fp_is_true_zero,
    fp_is_value_equal, fp_is_value_zero, fp_logical_and, fp_logical_not, fp_logical_or, fp_mul,
    fp_normalize_and_round_significand, fp_select, fp_sub, fp_variable_right_shift_with_grs,
};

use super::AirCodegen;
use crate::llvm::air::codegen::LangIntPredicate;
use crate::llvm::air::codegen::LangVariable;
use crate::llvm::air::codegen::resolvers::fp::{
    fp_find_msb, fp_icmp_eq, fp_icmp_uge, fp_power_of_2, fp_variable_division,
};
use crate::llvm::air::{
    types::{AirExpression, AirTraceVariable, RowOffset},
    utils::{generate_signed_range_proof_constraints, lang_operand_to_air_expression},
};

pub mod fp;
pub mod phi_transitions;

impl AirCodegen {
    pub fn resolve_structured_constraints(
        &mut self,
        structured_constraints_from_lang: Vec<StructuredAirConstraint>,
        phi_condition_map: &HashMap<(String, String), LangVariable>,
        switch_instructions: &Vec<StructuredAirConstraint>,
    ) -> Vec<AirExpression> {
        let mut air_constraints = Vec::new();
        for lang_constraint in structured_constraints_from_lang {
            match lang_constraint {
                StructuredAirConstraint::GetElementPtr {
                    base,
                    index,
                    element_size_bytes,
                    result,
                    block_name: _,
                } => {
                    println!(
                        "  GEP: base={:?}, idx={:?}, size={}, res={:?}",
                        base, index, element_size_bytes, result
                    );
                    let base_expr = lang_operand_to_air_expression(base);
                    let index_expr = lang_operand_to_air_expression(index);
                    let res_expr =
                        AirExpression::Trace(AirTraceVariable(result.0), RowOffset::Current);

                    let size_expr = AirExpression::Constant(element_size_bytes as u128);

                    let offset_expr = AirExpression::Mul(Box::new(index_expr), Box::new(size_expr));

                    let addr_expr = AirExpression::Add(Box::new(base_expr), Box::new(offset_expr));

                    air_constraints
                        .push(AirExpression::Sub(Box::new(res_expr), Box::new(addr_expr)));
                }
                StructuredAirConstraint::ZExt {
                    operand,
                    result,
                    operand_bitwidth,
                    result_bitwidth,
                    block_name: _,
                } => {
                    println!(
                        "  ZEXT: op={:?}, res={:?}, op_bw={}, res_bw={}",
                        operand, result, operand_bitwidth, result_bitwidth
                    );
                    let op_expr = lang_operand_to_air_expression(operand);
                    let res_expr =
                        AirExpression::Trace(AirTraceVariable(result.0), RowOffset::Current);

                    self.ctx
                        .add_unsigned_range_proof_constraints(op_expr.clone(), operand_bitwidth);

                    air_constraints.push(AirExpression::Sub(Box::new(res_expr), Box::new(op_expr)));
                }
                StructuredAirConstraint::SExt {
                    operand,
                    result,
                    operand_bitwidth,
                    result_bitwidth,
                    block_name: _,
                } => {
                    println!(
                        "  SEXT: op={:?}, res={:?}, op_bw={}, res_bw={}",
                        operand, result, operand_bitwidth, result_bitwidth
                    );

                    let op_expr = lang_operand_to_air_expression(operand);
                    let res_expr =
                        AirExpression::Trace(AirTraceVariable(result.0), RowOffset::Current);

                    let (_op_bits, op_msb_expr_opt) = generate_signed_range_proof_constraints(
                        &op_expr,
                        operand_bitwidth,
                        &mut self.ctx,
                        &mut air_constraints,
                        "op_sext",
                    );
                    let op_msb_expr =
                        op_msb_expr_opt.expect("Signed range proof should provide the sign bit");

                    let extension_const = (1u128 << result_bitwidth) - (1u128 << operand_bitwidth);
                    let extension_val = AirExpression::Mul(
                        Box::new(op_msb_expr),
                        Box::new(AirExpression::Constant(extension_const)),
                    );

                    let sext_val = AirExpression::Add(Box::new(op_expr), Box::new(extension_val));
                    air_constraints
                        .push(AirExpression::Sub(Box::new(res_expr), Box::new(sext_val)));
                }
                StructuredAirConstraint::FPExt {
                    operand,
                    result,
                    operand_bitwidth,
                    result_bitwidth,
                    block_name: _,
                } => {
                    println!(
                        "  FPEXT: op={:?}, res={:?}, op_bw={}, res_bw={}",
                        operand, result, operand_bitwidth, result_bitwidth
                    );

                    let (op_s_bits, op_e_bits, op_m_bits) = match operand_bitwidth {
                        32 => (1, 8, 23),
                        16 => (1, 5, 10),
                        _ => panic!("Unsupported FP bitwidth for FPExt operand"),
                    };
                    let op_bias = (1u128 << (op_e_bits - 1)) - 1;

                    let (res_s_bits, res_e_bits, res_m_bits) = match result_bitwidth {
                        64 => (1, 11, 52),
                        32 => (1, 8, 23),
                        _ => panic!("Unsupported FP bitwidth for FPExt result"),
                    };
                    let res_bias = (1u128 << (res_e_bits - 1)) - 1;
                    let res_e_max = (1u128 << res_e_bits) - 1;

                    let (op_s_var, op_e_var, op_m_var) = setup_sem_aux_vars(
                        operand,
                        "op_fpext",
                        &mut self.ctx,
                        op_s_bits,
                        op_e_bits,
                        op_m_bits,
                        &mut air_constraints,
                    );
                    let op_s_expr = AirExpression::Trace(op_s_var, RowOffset::Current);
                    let op_e_expr = AirExpression::Trace(op_e_var, RowOffset::Current);
                    let op_m_expr = AirExpression::Trace(op_m_var, RowOffset::Current);

                    let (res_s_var, res_e_var, res_m_var) = setup_sem_aux_vars(
                        lang::Operand::Var(result),
                        "res_fpext",
                        &mut self.ctx,
                        res_s_bits,
                        res_e_bits,
                        res_m_bits,
                        &mut air_constraints,
                    );
                    let res_s_expr = AirExpression::Trace(res_s_var, RowOffset::Current);
                    let res_e_expr = AirExpression::Trace(res_e_var, RowOffset::Current);
                    let res_m_expr = AirExpression::Trace(res_m_var, RowOffset::Current);

                    air_constraints.push(AirExpression::Sub(
                        Box::new(res_s_expr.clone()),
                        Box::new(op_s_expr.clone()),
                    ));

                    let is_op_zero = fp_is_true_zero(
                        &op_e_expr,
                        &op_m_expr,
                        op_e_bits,
                        op_m_bits,
                        &mut self.ctx,
                        &mut air_constraints,
                        "fpext_op_is_zero",
                    );
                    let is_op_inf = fp_is_inf(
                        &op_e_expr,
                        &op_m_expr,
                        op_e_bits,
                        op_m_bits,
                        &mut self.ctx,
                        &mut air_constraints,
                        "fpext_op_is_inf",
                    );
                    let is_op_nan = fp_is_nan(
                        &op_e_expr,
                        &op_m_expr,
                        op_e_bits,
                        op_m_bits,
                        &mut self.ctx,
                        &mut air_constraints,
                        "fpext_op_is_nan",
                    );

                    let is_op_denormal = fp_is_value_zero(
                        &op_e_expr,
                        &mut self.ctx,
                        &mut air_constraints,
                        "fpext_op_is_denormal",
                    );
                    let op_implicit_bit = fp_logical_not(
                        &is_op_denormal,
                        &mut self.ctx,
                        &mut air_constraints,
                        "fpext_op_implicit_bit",
                    );
                    let op_full_significand = fp_add(
                        &op_m_expr,
                        &fp_mul(
                            &op_implicit_bit,
                            &AirExpression::Constant(1u128 << op_m_bits),
                            &mut self.ctx,
                            &mut air_constraints,
                            "fpext_op_full_sig",
                        ),
                        &mut self.ctx,
                        &mut air_constraints,
                        "fpext_op_full_sig_add",
                    );

                    let op_effective_exp = fp_select(
                        &is_op_denormal,
                        &AirExpression::Constant(1),
                        &op_e_expr,
                        &mut self.ctx,
                        &mut air_constraints,
                        "fpext_op_eff_exp",
                    );

                    let unbiased_exp = fp_sub(
                        &op_effective_exp,
                        &AirExpression::Constant(op_bias),
                        &mut self.ctx,
                        &mut air_constraints,
                        "fpext_unbias",
                    );

                    let res_e_general = fp_add(
                        &unbiased_exp,
                        &AirExpression::Constant(res_bias),
                        &mut self.ctx,
                        &mut air_constraints,
                        "fpext_rebias",
                    );

                    let mantissa_shift_amount = res_m_bits - op_m_bits;
                    let res_m_general = fp_mul(
                        &op_full_significand,
                        &AirExpression::Constant(1u128 << mantissa_shift_amount),
                        &mut self.ctx,
                        &mut air_constraints,
                        "fpext_m_shift",
                    );

                    let res_e_if_zero = AirExpression::Constant(0);
                    let res_m_if_zero = AirExpression::Constant(0);

                    let res_e_if_inf = AirExpression::Constant(res_e_max);
                    let res_m_if_inf = AirExpression::Constant(0);

                    let res_e_if_nan = AirExpression::Constant(res_e_max);

                    let res_m_if_nan = fp_mul(
                        &op_m_expr,
                        &AirExpression::Constant(1u128 << mantissa_shift_amount),
                        &mut self.ctx,
                        &mut air_constraints,
                        "fpext_nan_m_shift",
                    );

                    let res_e_1 = fp_select(
                        &is_op_zero,
                        &res_e_if_zero,
                        &res_e_general,
                        &mut self.ctx,
                        &mut air_constraints,
                        "fpext_sel_e_1",
                    );
                    let res_m_1 = fp_select(
                        &is_op_zero,
                        &res_m_if_zero,
                        &res_m_general,
                        &mut self.ctx,
                        &mut air_constraints,
                        "fpext_sel_m_1",
                    );

                    let res_e_2 = fp_select(
                        &is_op_inf,
                        &res_e_if_inf,
                        &res_e_1,
                        &mut self.ctx,
                        &mut air_constraints,
                        "fpext_sel_e_2",
                    );
                    let res_m_2 = fp_select(
                        &is_op_inf,
                        &res_m_if_inf,
                        &res_m_1,
                        &mut self.ctx,
                        &mut air_constraints,
                        "fpext_sel_m_2",
                    );

                    let final_e = fp_select(
                        &is_op_nan,
                        &res_e_if_nan,
                        &res_e_2,
                        &mut self.ctx,
                        &mut air_constraints,
                        "fpext_sel_e_final",
                    );
                    let final_m = fp_select(
                        &is_op_nan,
                        &res_m_if_nan,
                        &res_m_2,
                        &mut self.ctx,
                        &mut air_constraints,
                        "fpext_sel_m_final",
                    );

                    air_constraints
                        .push(AirExpression::Sub(Box::new(res_e_expr), Box::new(final_e)));
                    air_constraints
                        .push(AirExpression::Sub(Box::new(res_m_expr), Box::new(final_m)));
                }
                StructuredAirConstraint::Select {
                    cond,
                    true_val,
                    false_val,
                    result,
                    block_name: _,
                } => {
                    let cond_expr = lang_operand_to_air_expression(cond);
                    let true_val_expr = lang_operand_to_air_expression(true_val);
                    let false_val_expr = lang_operand_to_air_expression(false_val);
                    let res_expr =
                        AirExpression::Trace(AirTraceVariable(result.0), RowOffset::Current);

                    let term1 =
                        AirExpression::Mul(Box::new(cond_expr.clone()), Box::new(true_val_expr));

                    let one_minus_cond = AirExpression::Sub(
                        Box::new(AirExpression::Constant(1)),
                        Box::new(cond_expr),
                    );
                    let term2 =
                        AirExpression::Mul(Box::new(one_minus_cond), Box::new(false_val_expr));

                    let selected_value_expr = AirExpression::Add(Box::new(term1), Box::new(term2));

                    let final_expr =
                        AirExpression::Sub(Box::new(selected_value_expr), Box::new(res_expr));
                    air_constraints.push(final_expr);
                }
                StructuredAirConstraint::Add {
                    operand1,
                    operand2,
                    result,
                    block_name: _,
                } => {
                    let op1_expr = lang_operand_to_air_expression(operand1);
                    let op2_expr = lang_operand_to_air_expression(operand2);
                    let res_expr =
                        AirExpression::Trace(AirTraceVariable(result.0), RowOffset::Current);
                    let sum_expr = AirExpression::Add(Box::new(op1_expr), Box::new(op2_expr));
                    let final_expr = AirExpression::Sub(Box::new(sum_expr), Box::new(res_expr));
                    air_constraints.push(final_expr);
                }
                StructuredAirConstraint::Sub {
                    operand1,
                    operand2,
                    result,
                    block_name: _,
                } => {
                    let op1_expr = lang_operand_to_air_expression(operand1);
                    let op2_expr = lang_operand_to_air_expression(operand2);
                    let res_expr =
                        AirExpression::Trace(AirTraceVariable(result.0), RowOffset::Current);

                    let op1_minus_op2_expr =
                        AirExpression::Sub(Box::new(op1_expr), Box::new(op2_expr));
                    let final_expr =
                        AirExpression::Sub(Box::new(res_expr), Box::new(op1_minus_op2_expr));
                    air_constraints.push(final_expr);
                }
                StructuredAirConstraint::Multiply {
                    operand1,
                    operand2,
                    result,
                    block_name: _,
                } => {
                    let op1_expr = lang_operand_to_air_expression(operand1);
                    let op2_expr = lang_operand_to_air_expression(operand2);
                    let res_expr =
                        AirExpression::Trace(AirTraceVariable(result.0), RowOffset::Current);
                    let prod_expr = AirExpression::Mul(Box::new(op1_expr), Box::new(op2_expr));
                    let final_expr = AirExpression::Sub(Box::new(prod_expr), Box::new(res_expr));
                    air_constraints.push(final_expr);
                }
                StructuredAirConstraint::And {
                    operand1,
                    operand2,
                    result,
                    block_name: _,
                } => {
                    let op1_expr = lang_operand_to_air_expression(operand1);
                    let op2_expr = lang_operand_to_air_expression(operand2);
                    let res_expr =
                        AirExpression::Trace(AirTraceVariable(result.0), RowOffset::Current);

                    let prod_expr = AirExpression::Mul(Box::new(op1_expr), Box::new(op2_expr));
                    let final_expr = AirExpression::Sub(Box::new(prod_expr), Box::new(res_expr));
                    air_constraints.push(final_expr);
                }
                StructuredAirConstraint::Or {
                    operand1,
                    operand2,
                    result,
                    block_name: _,
                } => {
                    let op1_expr = lang_operand_to_air_expression(operand1);
                    let op2_expr = lang_operand_to_air_expression(operand2);
                    let res_expr =
                        AirExpression::Trace(AirTraceVariable(result.0), RowOffset::Current);

                    let a_plus_b =
                        AirExpression::Add(Box::new(op1_expr.clone()), Box::new(op2_expr.clone()));
                    let a_times_b = AirExpression::Mul(Box::new(op1_expr), Box::new(op2_expr));
                    let or_val_expr = AirExpression::Sub(Box::new(a_plus_b), Box::new(a_times_b));
                    let final_expr = AirExpression::Sub(Box::new(or_val_expr), Box::new(res_expr));
                    air_constraints.push(final_expr);
                }
                StructuredAirConstraint::Xor {
                    operand1,
                    operand2,
                    result,
                    block_name: _,
                } => {
                    let op1_expr = lang_operand_to_air_expression(operand1);
                    let op2_expr = lang_operand_to_air_expression(operand2);
                    let res_expr =
                        AirExpression::Trace(AirTraceVariable(result.0), RowOffset::Current);

                    let a_plus_b =
                        AirExpression::Add(Box::new(op1_expr.clone()), Box::new(op2_expr.clone()));
                    let a_times_b =
                        AirExpression::Mul(Box::new(op1_expr.clone()), Box::new(op2_expr.clone()));
                    let two_const = AirExpression::Constant(2);
                    let two_a_b = AirExpression::Mul(Box::new(two_const), Box::new(a_times_b));
                    let xor_val_expr = AirExpression::Sub(Box::new(a_plus_b), Box::new(two_a_b));
                    let final_expr = AirExpression::Sub(Box::new(xor_val_expr), Box::new(res_expr));
                    air_constraints.push(final_expr);
                }
                StructuredAirConstraint::Shl {
                    operand1,
                    operand2,
                    result,
                    operand_bitwidth,
                    block_name: _,
                } => {
                    let op1_expr = lang_operand_to_air_expression(operand1);
                    let op2_expr = lang_operand_to_air_expression(operand2);
                    let res_expr =
                        AirExpression::Trace(AirTraceVariable(result.0), RowOffset::Current);
                    println!(
                        "  SHL: op1={:?}, op2={:?}, res={:?}, operand_bitwidth={}",
                        op1_expr, op2_expr, res_expr, operand_bitwidth
                    );

                    if let AirExpression::Constant(s_const_val) = op2_expr {
                        if s_const_val >= operand_bitwidth.into() {
                            air_constraints.push(res_expr.clone());
                            println!(
                                "    SHL: op2 is const {} >= bitwidth {}, result set to 0",
                                s_const_val, operand_bitwidth
                            );
                        } else {
                            let power_of_2_s_val = 1u128.wrapping_shl(s_const_val as u32);
                            let power_of_2_s_expr = AirExpression::Constant(power_of_2_s_val);
                            let product = AirExpression::Mul(
                                Box::new(op1_expr.clone()),
                                Box::new(power_of_2_s_expr),
                            );
                            air_constraints.push(AirExpression::Sub(
                                Box::new(res_expr.clone()),
                                Box::new(product),
                            ));
                            println!(
                                "    SHL: op2 is const {}, 2^{} = {}, res = op1 * {}",
                                s_const_val, s_const_val, power_of_2_s_val, power_of_2_s_val
                            );
                        }
                    } else {
                        println!("    SHL: op2 is variable: {:?}", op2_expr);

                        let num_shift_bits = if operand_bitwidth == 1 {
                            1
                        } else {
                            (operand_bitwidth - 1).ilog2() + 1
                        };
                        println!("      SHL: num_shift_bits_for_op2 = {}", num_shift_bits);

                        let mut s_bit_exprs = Vec::new();
                        let mut op2_sum_terms_recon = Vec::new();
                        println!(
                            "      SHL: Decomposing op2_expr into {} bits...",
                            num_shift_bits
                        );
                        for i in 0..num_shift_bits {
                            let bit_aux_var = self.ctx.new_aux_variable();
                            let bit_expr = AirExpression::Trace(bit_aux_var, RowOffset::Current);

                            air_constraints.push(AirExpression::Mul(
                                Box::new(bit_expr.clone()),
                                Box::new(AirExpression::Sub(
                                    Box::new(bit_expr.clone()),
                                    Box::new(AirExpression::Constant(1)),
                                )),
                            ));
                            s_bit_exprs.push(bit_expr.clone());

                            let power_of_2_val = 1u128 << i;
                            op2_sum_terms_recon.push(AirExpression::Mul(
                                Box::new(bit_expr.clone()),
                                Box::new(AirExpression::Constant(power_of_2_val)),
                            ));
                            println!(
                                "        s_bit_{} (trace col {}) created for op2 decomposition",
                                i, bit_aux_var.0
                            );
                        }

                        let op2_reconstructed_expr = op2_sum_terms_recon
                            .into_iter()
                            .reduce(|acc, term| AirExpression::Add(Box::new(acc), Box::new(term)))
                            .unwrap_or_else(|| AirExpression::Constant(0));

                        air_constraints.push(AirExpression::Sub(
                            Box::new(op2_expr.clone()),
                            Box::new(op2_reconstructed_expr),
                        ));
                        println!("      SHL: op2 decomposition constraint added.");

                        let mut factor_exprs_for_prod = Vec::new();
                        println!("      SHL: Calculating factors for 2^op2 term...");
                        for i in 0..num_shift_bits {
                            let s_i_expr: &AirExpression = &s_bit_exprs[i as usize];

                            let exp_base_power = 1u128 << i;

                            let exp_val_i = if exp_base_power >= 128 {
                                0
                            } else {
                                1u128.wrapping_shl(exp_base_power as u32)
                            };
                            if exp_base_power >= 128 && exp_val_i != 0 {
                                println!(
                                    "        WARN: Large exp_base_power {} resulted in exp_val_i {}. This might be an issue.",
                                    exp_base_power, exp_val_i
                                );
                            }

                            let factor_i_aux_var = self.ctx.new_aux_variable();
                            let factor_i_expr_aux =
                                AirExpression::Trace(factor_i_aux_var, RowOffset::Current);

                            let exp_val_i_minus_1 = exp_val_i.saturating_sub(1);
                            let term_mul_factor = AirExpression::Mul(
                                Box::new(s_i_expr.clone()),
                                Box::new(AirExpression::Constant(exp_val_i_minus_1)),
                            );
                            let term_sum_factor = AirExpression::Add(
                                Box::new(term_mul_factor),
                                Box::new(AirExpression::Constant(1)),
                            );
                            air_constraints.push(AirExpression::Sub(
                                Box::new(factor_i_expr_aux.clone()),
                                Box::new(term_sum_factor),
                            ));
                            factor_exprs_for_prod.push(factor_i_expr_aux.clone());
                            println!(
                                "        factor_{} (trace col {}) for s_{} (using exp_val_i=2^(2^{})={}) created.",
                                i, factor_i_aux_var.0, i, i, exp_val_i
                            );
                        }

                        let mut final_power_of_2_op2_expr = AirExpression::Constant(1);
                        if !factor_exprs_for_prod.is_empty() {
                            final_power_of_2_op2_expr = factor_exprs_for_prod[0].clone();
                            println!(
                                "      SHL: Product for 2^op2: init with factor_0 ({:?})",
                                final_power_of_2_op2_expr
                            );
                            for i in 1..factor_exprs_for_prod.len() {
                                let prev_product_expr_val = final_power_of_2_op2_expr.clone();
                                let factor_val_expr = &factor_exprs_for_prod[i];

                                let next_product_aux_var = self.ctx.new_aux_variable();
                                final_power_of_2_op2_expr =
                                    AirExpression::Trace(next_product_aux_var, RowOffset::Current);

                                let product_term_step = AirExpression::Mul(
                                    Box::new(prev_product_expr_val),
                                    Box::new(factor_val_expr.clone()),
                                );
                                air_constraints.push(AirExpression::Sub(
                                    Box::new(final_power_of_2_op2_expr.clone()),
                                    Box::new(product_term_step),
                                ));
                                println!(
                                    "        prod_step_{} (trace col {}): from prev_prod * factor_{}",
                                    i, next_product_aux_var.0, i
                                );
                            }
                        }
                        println!(
                            "      SHL: final_power_of_2_op2_expr = {:?}",
                            final_power_of_2_op2_expr
                        );

                        let main_prod_term = AirExpression::Mul(
                            Box::new(op1_expr.clone()),
                            Box::new(final_power_of_2_op2_expr.clone()),
                        );
                        air_constraints.push(AirExpression::Sub(
                            Box::new(res_expr.clone()),
                            Box::new(main_prod_term),
                        ));
                        println!("      SHL: Main constraint (res - op1 * 2^op2 = 0) added.");
                    }
                }

                StructuredAirConstraint::FPToSI {
                    operand,
                    result,
                    operand_bitwidth,
                    result_bitwidth,
                    block_name: _,
                } => {
                    println!(
                        "  FPTOSI: op={:?}, res={:?}, op_bw={}, res_bw={}",
                        operand, result, operand_bitwidth, result_bitwidth
                    );

                    let (s_fp_bits, e_fp_bits, m_fp_bits) = match operand_bitwidth {
                        32 => (1, 8, 23),
                        64 => (1, 11, 52),
                        _ => panic!("Unsupported FP bitwidth for FPToSI"),
                    };
                    let (op_s_var, op_e_var, op_m_var) = setup_sem_aux_vars(
                        operand,
                        "op_fptosi",
                        &mut self.ctx,
                        s_fp_bits,
                        e_fp_bits,
                        m_fp_bits,
                        &mut air_constraints,
                    );
                    let op_s_expr = AirExpression::Trace(op_s_var, RowOffset::Current);
                    let op_e_expr = AirExpression::Trace(op_e_var, RowOffset::Current);
                    let op_m_expr = AirExpression::Trace(op_m_var, RowOffset::Current);
                    let res_expr =
                        AirExpression::Trace(AirTraceVariable(result.0), RowOffset::Current);

                    let is_nan = fp_is_nan(
                        &op_e_expr,
                        &op_m_expr,
                        e_fp_bits,
                        m_fp_bits,
                        &mut self.ctx,
                        &mut air_constraints,
                        "fptosi_nan",
                    );
                    let is_inf = fp_is_inf(
                        &op_e_expr,
                        &op_m_expr,
                        e_fp_bits,
                        m_fp_bits,
                        &mut self.ctx,
                        &mut air_constraints,
                        "fptosi_inf",
                    );
                    let is_special = fp_logical_or(
                        &is_nan,
                        &is_inf,
                        &mut self.ctx,
                        &mut air_constraints,
                        "fptosi_special",
                    );

                    let bias = (1u128 << (e_fp_bits - 1)) - 1;
                    let is_denormal = fp_is_value_zero(
                        &op_e_expr,
                        &mut self.ctx,
                        &mut air_constraints,
                        "fptosi_denorm",
                    );
                    let implicit_bit = fp_logical_not(
                        &is_denormal,
                        &mut self.ctx,
                        &mut air_constraints,
                        "fptosi_impl_bit",
                    );
                    let full_significand = fp_add(
                        &op_m_expr,
                        &fp_mul(
                            &implicit_bit,
                            &AirExpression::Constant(1u128 << m_fp_bits),
                            &mut self.ctx,
                            &mut air_constraints,
                            "fptosi_full_sig_add",
                        ),
                        &mut self.ctx,
                        &mut air_constraints,
                        "fptosi_full_sig",
                    );
                    let effective_exp = fp_select(
                        &is_denormal,
                        &AirExpression::Constant(1),
                        &op_e_expr,
                        &mut self.ctx,
                        &mut air_constraints,
                        "fptosi_eff_exp",
                    );

                    let shift_threshold = bias + m_fp_bits as u128;
                    let is_left_shift = fp_icmp_uge(
                        &effective_exp,
                        &AirExpression::Constant(shift_threshold),
                        e_fp_bits + 1,
                        &mut self.ctx,
                        &mut air_constraints,
                        "fptosi_is_left",
                    );

                    let left_shift_amount = fp_sub(
                        &effective_exp,
                        &AirExpression::Constant(shift_threshold),
                        &mut self.ctx,
                        &mut air_constraints,
                        "fptosi_lshift",
                    );
                    let right_shift_amount = fp_sub(
                        &AirExpression::Constant(shift_threshold),
                        &effective_exp,
                        &mut self.ctx,
                        &mut air_constraints,
                        "fptosi_rshift",
                    );

                    let left_shifted_val = {
                        let power_of_2 = fp_power_of_2(
                            &left_shift_amount,
                            e_fp_bits + 1,
                            &mut self.ctx,
                            &mut air_constraints,
                            "fptosi_lshift_pow2",
                        );
                        fp_mul(
                            &full_significand,
                            &power_of_2,
                            &mut self.ctx,
                            &mut air_constraints,
                            "fptosi_lshift_res",
                        )
                    };
                    let right_shifted_val = {
                        let (quotient, _rem) = fp_variable_division(
                            &full_significand,
                            &right_shift_amount,
                            m_fp_bits + 1,
                            m_fp_bits + 1 + e_fp_bits,
                            &mut self.ctx,
                            &mut air_constraints,
                            "fptosi_rshift",
                        );
                        quotient
                    };

                    let abs_int_val = fp_select(
                        &is_left_shift,
                        &left_shifted_val,
                        &right_shifted_val,
                        &mut self.ctx,
                        &mut air_constraints,
                        "fptosi_abs_val",
                    );

                    let one_minus_2s = fp_sub(
                        &AirExpression::Constant(1),
                        &fp_mul(
                            &AirExpression::Constant(2),
                            &op_s_expr,
                            &mut self.ctx,
                            &mut air_constraints,
                            "fptosi_2s",
                        ),
                        &mut self.ctx,
                        &mut air_constraints,
                        "fptosi_1_2s",
                    );
                    let general_case_res = fp_mul(
                        &abs_int_val,
                        &one_minus_2s,
                        &mut self.ctx,
                        &mut air_constraints,
                        "fptosi_signed_res",
                    );

                    let final_res = fp_select(
                        &is_special,
                        &AirExpression::Constant(0),
                        &general_case_res,
                        &mut self.ctx,
                        &mut air_constraints,
                        "fptosi_final_res",
                    );
                    air_constraints.push(AirExpression::Sub(
                        Box::new(res_expr.clone()),
                        Box::new(final_res),
                    ));

                    self.ctx
                        .add_signed_range_proof_constraints(res_expr, result_bitwidth);
                }
                StructuredAirConstraint::SIToFP {
                    operand,
                    result,
                    operand_bitwidth,
                    result_bitwidth,
                    block_name: _,
                } => {
                    println!(
                        "  SITOFP: op={:?}, res={:?}, op_bw={}, res_bw={}",
                        operand, result, operand_bitwidth, result_bitwidth
                    );

                    let (s_fp_bits, e_fp_bits, m_fp_bits) = match result_bitwidth {
                        32 => (1, 8, 23),
                        64 => (1, 11, 52),
                        _ => panic!("Unsupported FP bitwidth for SIToFP"),
                    };
                    let (res_s_var, res_e_var, res_m_var) = setup_sem_aux_vars(
                        lang::Operand::Var(result),
                        "res_sitofp",
                        &mut self.ctx,
                        s_fp_bits,
                        e_fp_bits,
                        m_fp_bits,
                        &mut air_constraints,
                    );
                    let res_s_expr = AirExpression::Trace(res_s_var, RowOffset::Current);
                    let res_e_expr = AirExpression::Trace(res_e_var, RowOffset::Current);
                    let res_m_expr = AirExpression::Trace(res_m_var, RowOffset::Current);
                    let op_expr = lang_operand_to_air_expression(operand);

                    let (_op_bits, op_msb_expr_opt) = generate_signed_range_proof_constraints(
                        &op_expr,
                        operand_bitwidth,
                        &mut self.ctx,
                        &mut air_constraints,
                        "op_sitofp",
                    );

                    if let Some(op_msb_expr) = op_msb_expr_opt {
                        air_constraints.push(AirExpression::Sub(
                            Box::new(res_s_expr.clone()),
                            Box::new(op_msb_expr),
                        ));
                    }

                    let bias = (1u128 << (e_fp_bits - 1)) - 1;
                    let is_denormal = fp_is_value_zero(
                        &res_e_expr,
                        &mut self.ctx,
                        &mut air_constraints,
                        "sitofp_denorm",
                    );
                    let implicit_bit = fp_logical_not(
                        &is_denormal,
                        &mut self.ctx,
                        &mut air_constraints,
                        "sitofp_impl_bit",
                    );
                    let full_significand = fp_add(
                        &res_m_expr,
                        &fp_mul(
                            &implicit_bit,
                            &AirExpression::Constant(1u128 << m_fp_bits),
                            &mut self.ctx,
                            &mut air_constraints,
                            "sitofp_full_sig_add",
                        ),
                        &mut self.ctx,
                        &mut air_constraints,
                        "sitofp_full_sig",
                    );
                    let effective_exp = fp_select(
                        &is_denormal,
                        &AirExpression::Constant(1),
                        &res_e_expr,
                        &mut self.ctx,
                        &mut air_constraints,
                        "sitofp_eff_exp",
                    );

                    let shift_threshold = bias + m_fp_bits as u128;
                    let is_left_shift = fp_icmp_uge(
                        &effective_exp,
                        &AirExpression::Constant(shift_threshold),
                        e_fp_bits + 1,
                        &mut self.ctx,
                        &mut air_constraints,
                        "sitofp_is_left",
                    );

                    let left_shift_amount = fp_sub(
                        &effective_exp,
                        &AirExpression::Constant(shift_threshold),
                        &mut self.ctx,
                        &mut air_constraints,
                        "sitofp_lshift",
                    );
                    let right_shift_amount = fp_sub(
                        &AirExpression::Constant(shift_threshold),
                        &effective_exp,
                        &mut self.ctx,
                        &mut air_constraints,
                        "sitofp_rshift",
                    );

                    let (left_shifted_val, left_shift_rem) = (
                        {
                            let power_of_2 = fp_power_of_2(
                                &left_shift_amount,
                                e_fp_bits + 1,
                                &mut self.ctx,
                                &mut air_constraints,
                                "sitofp_lshift_pow2",
                            );
                            fp_mul(
                                &full_significand,
                                &power_of_2,
                                &mut self.ctx,
                                &mut air_constraints,
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
                        &mut self.ctx,
                        &mut air_constraints,
                        "sitofp_rshift",
                    );

                    let abs_int_val = fp_select(
                        &is_left_shift,
                        &left_shifted_val,
                        &right_shifted_val,
                        &mut self.ctx,
                        &mut air_constraints,
                        "sitofp_abs_val",
                    );
                    let remainder = fp_select(
                        &is_left_shift,
                        &left_shift_rem,
                        &right_shift_rem,
                        &mut self.ctx,
                        &mut air_constraints,
                        "sitofp_rem",
                    );

                    let one_minus_2s = fp_sub(
                        &AirExpression::Constant(1),
                        &fp_mul(
                            &AirExpression::Constant(2),
                            &res_s_expr,
                            &mut self.ctx,
                            &mut air_constraints,
                            "sitofp_2s",
                        ),
                        &mut self.ctx,
                        &mut air_constraints,
                        "sitofp_1_2s",
                    );
                    let calculated_int_val = fp_mul(
                        &abs_int_val,
                        &one_minus_2s,
                        &mut self.ctx,
                        &mut air_constraints,
                        "sitofp_signed_res",
                    );
                    air_constraints.push(AirExpression::Sub(
                        Box::new(op_expr),
                        Box::new(calculated_int_val),
                    ));

                    air_constraints.push(remainder);
                }
                StructuredAirConstraint::UIToFP {
                    operand,
                    result,
                    operand_bitwidth,
                    result_bitwidth,
                    block_name: _,
                } => {
                    println!(
                        "  UITOFP: op={:?}, res={:?}, op_bw={}, res_bw={}",
                        operand, result, operand_bitwidth, result_bitwidth
                    );

                    let op_expr = lang_operand_to_air_expression(operand);
                    self.ctx
                        .add_unsigned_range_proof_constraints(op_expr.clone(), operand_bitwidth);

                    let (s_fp_bits, e_fp_bits, m_fp_bits) = match result_bitwidth {
                        32 => (1, 8, 23),
                        64 => (1, 11, 52),
                        _ => panic!("Unsupported FP bitwidth for UIToFP"),
                    };

                    let (res_s_var, res_e_var, res_m_var) = setup_sem_aux_vars(
                        Operand::Var(result),
                        "res_uitofp",
                        &mut self.ctx,
                        s_fp_bits,
                        e_fp_bits,
                        m_fp_bits,
                        &mut air_constraints,
                    );

                    let res_s_expr = AirExpression::Trace(res_s_var, RowOffset::Current);
                    let res_e_expr = AirExpression::Trace(res_e_var, RowOffset::Current);
                    let res_m_expr = AirExpression::Trace(res_m_var, RowOffset::Current);

                    air_constraints.push(res_s_expr.clone());

                    let is_zero = fp_is_value_zero(
                        &op_expr,
                        &mut self.ctx,
                        &mut air_constraints,
                        "uitofp_is_zero",
                    );

                    air_constraints.push(AirExpression::Mul(
                        Box::new(is_zero.clone()),
                        Box::new(res_e_expr.clone()),
                    ));
                    air_constraints.push(AirExpression::Mul(
                        Box::new(is_zero.clone()),
                        Box::new(res_m_expr.clone()),
                    ));

                    let not_is_zero = fp_logical_not(
                        &is_zero,
                        &mut self.ctx,
                        &mut air_constraints,
                        "uitofp_not_zero",
                    );

                    let (msb_pos_expr, op_without_msb_expr) = fp_find_msb(
                        &op_expr,
                        operand_bitwidth,
                        &mut self.ctx,
                        &mut air_constraints,
                        "uitofp_msb",
                    );

                    let bias = (1u128 << (e_fp_bits - 1)) - 1;
                    let calculated_e = fp_add(
                        &msb_pos_expr,
                        &AirExpression::Constant(bias),
                        &mut self.ctx,
                        &mut air_constraints,
                        "uitofp_calc_e",
                    );

                    let e_constraint =
                        AirExpression::Sub(Box::new(res_e_expr.clone()), Box::new(calculated_e));

                    air_constraints.push(AirExpression::Mul(
                        Box::new(not_is_zero.clone()),
                        Box::new(e_constraint),
                    ));

                    let m_fp_bits_expr = AirExpression::Constant(m_fp_bits as u128);

                    let is_right_shift = fp_icmp_uge(
                        &msb_pos_expr,
                        &m_fp_bits_expr,
                        operand_bitwidth,
                        &mut self.ctx,
                        &mut air_constraints,
                        "uitofp_is_rshift",
                    );

                    let right_shift_amount = fp_sub(
                        &msb_pos_expr,
                        &m_fp_bits_expr,
                        &mut self.ctx,
                        &mut air_constraints,
                        "uitofp_rshift_amt",
                    );
                    let (rshifted_m, _r_rem) = fp_variable_division(
                        &op_without_msb_expr,
                        &right_shift_amount,
                        operand_bitwidth.saturating_sub(1),
                        operand_bitwidth,
                        &mut self.ctx,
                        &mut air_constraints,
                        "uitofp_rshift",
                    );

                    let left_shift_amount = fp_sub(
                        &m_fp_bits_expr,
                        &msb_pos_expr,
                        &mut self.ctx,
                        &mut air_constraints,
                        "uitofp_lshift_amt",
                    );
                    let pow2_lshift = fp_power_of_2(
                        &left_shift_amount,
                        m_fp_bits,
                        &mut self.ctx,
                        &mut air_constraints,
                        "uitofp_lshift_pow2",
                    );
                    let lshifted_m = fp_mul(
                        &op_without_msb_expr,
                        &pow2_lshift,
                        &mut self.ctx,
                        &mut air_constraints,
                        "uitofp_lshift",
                    );

                    let calculated_m = fp_select(
                        &is_right_shift,
                        &rshifted_m,
                        &lshifted_m,
                        &mut self.ctx,
                        &mut air_constraints,
                        "uitofp_calc_m",
                    );

                    let m_constraint =
                        AirExpression::Sub(Box::new(res_m_expr.clone()), Box::new(calculated_m));
                    air_constraints.push(AirExpression::Mul(
                        Box::new(not_is_zero.clone()),
                        Box::new(m_constraint),
                    ));
                }
                StructuredAirConstraint::FPToUI {
                    operand,
                    result,
                    operand_bitwidth,
                    result_bitwidth,
                    block_name: _,
                } => {
                    println!(
                        "  FPTOUI: op={:?}, res={:?}, op_bw={}, res_bw={}",
                        operand, result, operand_bitwidth, result_bitwidth
                    );

                    let (s_fp_bits, e_fp_bits, m_fp_bits) = match operand_bitwidth {
                        32 => (1, 8, 23),
                        64 => (1, 11, 52),
                        _ => panic!("Unsupported FP bitwidth for FPToUI"),
                    };
                    let (op_s_var, op_e_var, op_m_var) = setup_sem_aux_vars(
                        operand,
                        "op_fptoui",
                        &mut self.ctx,
                        s_fp_bits,
                        e_fp_bits,
                        m_fp_bits,
                        &mut air_constraints,
                    );
                    let op_s_expr = AirExpression::Trace(op_s_var, RowOffset::Current);
                    let op_e_expr = AirExpression::Trace(op_e_var, RowOffset::Current);
                    let op_m_expr = AirExpression::Trace(op_m_var, RowOffset::Current);
                    let res_expr =
                        AirExpression::Trace(AirTraceVariable(result.0), RowOffset::Current);

                    let is_nan = fp_is_nan(
                        &op_e_expr,
                        &op_m_expr,
                        e_fp_bits,
                        m_fp_bits,
                        &mut self.ctx,
                        &mut air_constraints,
                        "fptoui_nan",
                    );
                    let is_inf = fp_is_inf(
                        &op_e_expr,
                        &op_m_expr,
                        e_fp_bits,
                        m_fp_bits,
                        &mut self.ctx,
                        &mut air_constraints,
                        "fptoui_inf",
                    );
                    let is_special = fp_logical_or(
                        &is_nan,
                        &is_inf,
                        &mut self.ctx,
                        &mut air_constraints,
                        "fptoui_special",
                    );

                    let is_neg = op_s_expr.clone();
                    let is_invalid = fp_logical_or(
                        &is_special,
                        &is_neg,
                        &mut self.ctx,
                        &mut air_constraints,
                        "fptoui_invalid",
                    );

                    let bias = (1u128 << (e_fp_bits - 1)) - 1;
                    let is_denormal = fp_is_value_zero(
                        &op_e_expr,
                        &mut self.ctx,
                        &mut air_constraints,
                        "fptoui_denorm",
                    );
                    let implicit_bit = fp_logical_not(
                        &is_denormal,
                        &mut self.ctx,
                        &mut air_constraints,
                        "fptoui_impl_bit",
                    );
                    let full_significand = fp_add(
                        &op_m_expr,
                        &fp_mul(
                            &implicit_bit,
                            &AirExpression::Constant(1u128 << m_fp_bits),
                            &mut self.ctx,
                            &mut air_constraints,
                            "fptoui_full_sig_add",
                        ),
                        &mut self.ctx,
                        &mut air_constraints,
                        "fptoui_full_sig",
                    );
                    let effective_exp = fp_select(
                        &is_denormal,
                        &AirExpression::Constant(1),
                        &op_e_expr,
                        &mut self.ctx,
                        &mut air_constraints,
                        "fptoui_eff_exp",
                    );

                    let shift_threshold = bias + m_fp_bits as u128;
                    let is_left_shift = fp_icmp_uge(
                        &effective_exp,
                        &AirExpression::Constant(shift_threshold),
                        e_fp_bits + 1,
                        &mut self.ctx,
                        &mut air_constraints,
                        "fptoui_is_left",
                    );

                    let left_shift_amount = fp_sub(
                        &effective_exp,
                        &AirExpression::Constant(shift_threshold),
                        &mut self.ctx,
                        &mut air_constraints,
                        "fptoui_lshift",
                    );
                    let right_shift_amount = fp_sub(
                        &AirExpression::Constant(shift_threshold),
                        &effective_exp,
                        &mut self.ctx,
                        &mut air_constraints,
                        "fptoui_rshift",
                    );

                    let left_shifted_val = {
                        let power_of_2 = fp_power_of_2(
                            &left_shift_amount,
                            e_fp_bits + m_fp_bits + 2,
                            &mut self.ctx,
                            &mut air_constraints,
                            "fptoui_lshift_pow2",
                        );
                        fp_mul(
                            &full_significand,
                            &power_of_2,
                            &mut self.ctx,
                            &mut air_constraints,
                            "fptoui_lshift_res",
                        )
                    };
                    let right_shifted_val = {
                        let (quotient, _rem) = fp_variable_division(
                            &full_significand,
                            &right_shift_amount,
                            m_fp_bits + 1,
                            m_fp_bits + 1 + e_fp_bits,
                            &mut self.ctx,
                            &mut air_constraints,
                            "fptoui_rshift",
                        );
                        quotient
                    };

                    let general_case_res = fp_select(
                        &is_left_shift,
                        &left_shifted_val,
                        &right_shifted_val,
                        &mut self.ctx,
                        &mut air_constraints,
                        "fptoui_abs_val",
                    );

                    let final_res = fp_select(
                        &is_invalid,
                        &AirExpression::Constant(0),
                        &general_case_res,
                        &mut self.ctx,
                        &mut air_constraints,
                        "fptoui_final_res",
                    );
                    air_constraints.push(AirExpression::Sub(
                        Box::new(res_expr.clone()),
                        Box::new(final_res),
                    ));

                    self.ctx
                        .add_unsigned_range_proof_constraints(res_expr, result_bitwidth);
                }
                StructuredAirConstraint::Shr {
                    operand1,
                    operand2,
                    result,
                    operand_bitwidth,
                    block_name: _,
                } => {
                    let op1_expr = lang_operand_to_air_expression(operand1);
                    let op2_expr = lang_operand_to_air_expression(operand2);
                    let res_expr =
                        AirExpression::Trace(AirTraceVariable(result.0), RowOffset::Current);

                    let rem_aux_var = self.ctx.new_aux_variable();
                    let rem_expr = AirExpression::Trace(rem_aux_var, RowOffset::Current);
                    println!(
                        "  SHR: op1={:?}, op2={:?}, res={:?}, rem_aux_var={:?}, operand_bitwidth={}",
                        op1_expr, op2_expr, res_expr, rem_aux_var, operand_bitwidth
                    );

                    let mut rem_bit_sum_terms = Vec::new();
                    println!(
                        "    SHR: Decomposing remainder rem_expr ({:?}) into {} bits",
                        rem_expr, operand_bitwidth
                    );
                    for i in 0..operand_bitwidth {
                        let bit_aux = self.ctx.new_aux_variable();
                        let bit_expr = AirExpression::Trace(bit_aux, RowOffset::Current);
                        air_constraints.push(AirExpression::Mul(
                            Box::new(bit_expr.clone()),
                            Box::new(AirExpression::Sub(
                                Box::new(bit_expr.clone()),
                                Box::new(AirExpression::Constant(1)),
                            )),
                        ));
                        rem_bit_sum_terms.push(AirExpression::Mul(
                            Box::new(bit_expr.clone()),
                            Box::new(AirExpression::Constant(1u128 << i)),
                        ));
                        println!(
                            "      rem_bit_{} (trace col {}) created for remainder decomposition",
                            i, bit_aux.0
                        );
                    }
                    let rem_reconstructed = rem_bit_sum_terms
                        .into_iter()
                        .reduce(|acc, term| AirExpression::Add(Box::new(acc), Box::new(term)))
                        .unwrap_or_else(|| AirExpression::Constant(0));
                    air_constraints.push(AirExpression::Sub(
                        Box::new(rem_expr.clone()),
                        Box::new(rem_reconstructed),
                    ));
                    println!("    SHR: Remainder rem_expr decomposition constraint added.");

                    if let AirExpression::Constant(s_const_val) = op2_expr {
                        if s_const_val >= operand_bitwidth.into() {
                            air_constraints.push(res_expr.clone());

                            air_constraints.push(AirExpression::Sub(
                                Box::new(rem_expr.clone()),
                                Box::new(op1_expr.clone()),
                            ));
                            println!(
                                "    SHR: op2 is const {} >= bitwidth {}. res=0, rem=op1.",
                                s_const_val, operand_bitwidth
                            );
                        } else {
                            let power_of_2_s_val = 1u128.wrapping_shl(s_const_val as u32);
                            let power_of_2_s_expr = AirExpression::Constant(power_of_2_s_val);

                            let res_times_power_of_2 = AirExpression::Mul(
                                Box::new(res_expr.clone()),
                                Box::new(power_of_2_s_expr.clone()),
                            );
                            let res_term_plus_rem = AirExpression::Add(
                                Box::new(res_times_power_of_2),
                                Box::new(rem_expr.clone()),
                            );
                            air_constraints.push(AirExpression::Sub(
                                Box::new(op1_expr.clone()),
                                Box::new(res_term_plus_rem),
                            ));
                            println!(
                                "    SHR: op2 is const {}. Algebraic constraint op1 - (res*2^{} + rem) = 0 added.",
                                s_const_val, s_const_val
                            );
                        }
                    } else {
                        println!("    SHR: op2 is variable: {:?}", op2_expr);
                        let num_shift_bits = if operand_bitwidth == 1 {
                            1
                        } else {
                            (operand_bitwidth - 1).ilog2() + 1
                        };

                        let mut s_bit_exprs = Vec::new();
                        let mut op2_sum_terms_recon = Vec::new();
                        for i in 0..num_shift_bits {
                            let bit_aux_var = self.ctx.new_aux_variable();
                            let bit_expr = AirExpression::Trace(bit_aux_var, RowOffset::Current);
                            air_constraints.push(AirExpression::Mul(
                                Box::new(bit_expr.clone()),
                                Box::new(AirExpression::Sub(
                                    Box::new(bit_expr.clone()),
                                    Box::new(AirExpression::Constant(1)),
                                )),
                            ));
                            s_bit_exprs.push(bit_expr.clone());
                            op2_sum_terms_recon.push(AirExpression::Mul(
                                Box::new(bit_expr.clone()),
                                Box::new(AirExpression::Constant(1u128 << i)),
                            ));
                        }
                        let op2_reconstructed_expr = op2_sum_terms_recon
                            .into_iter()
                            .reduce(|acc, term| AirExpression::Add(Box::new(acc), Box::new(term)))
                            .unwrap_or_else(|| AirExpression::Constant(0));
                        air_constraints.push(AirExpression::Sub(
                            Box::new(op2_expr.clone()),
                            Box::new(op2_reconstructed_expr),
                        ));

                        let mut factor_exprs_for_prod = Vec::new();
                        println!("      SHR: (Variable s) Calculating factors for 2^s term...");
                        for i in 0..num_shift_bits {
                            let s_i_expr = &s_bit_exprs[i as usize];
                            let exp_base_power = 1u128 << i;
                            let exp_val_i = if exp_base_power >= 128 {
                                0
                            } else {
                                1u128.wrapping_shl(exp_base_power as u32)
                            };

                            let factor_i_aux_var = self.ctx.new_aux_variable();
                            let factor_i_expr_aux =
                                AirExpression::Trace(factor_i_aux_var, RowOffset::Current);
                            let exp_val_i_minus_1 = exp_val_i.saturating_sub(1);
                            let term_mul_factor = AirExpression::Mul(
                                Box::new(s_i_expr.clone()),
                                Box::new(AirExpression::Constant(exp_val_i_minus_1)),
                            );
                            let term_sum_factor = AirExpression::Add(
                                Box::new(term_mul_factor),
                                Box::new(AirExpression::Constant(1)),
                            );
                            air_constraints.push(AirExpression::Sub(
                                Box::new(factor_i_expr_aux.clone()),
                                Box::new(term_sum_factor),
                            ));
                            factor_exprs_for_prod.push(factor_i_expr_aux.clone());
                            println!(
                                "        factor_s_{} (trace col {}) for s_{} (using exp_val_i=2^(2^{})={}) created.",
                                i, factor_i_aux_var.0, i, i, exp_val_i
                            );
                        }

                        let mut final_power_of_2_op2_expr = AirExpression::Constant(1);
                        if !factor_exprs_for_prod.is_empty() {
                            final_power_of_2_op2_expr = factor_exprs_for_prod[0].clone();
                            println!(
                                "      SHR: (Variable s) Product for 2^s: init with factor_0 ({:?})",
                                final_power_of_2_op2_expr
                            );
                            for i in 1..factor_exprs_for_prod.len() {
                                let prev_product_expr_val = final_power_of_2_op2_expr.clone();
                                let factor_val_expr = &factor_exprs_for_prod[i];
                                let next_product_aux_var = self.ctx.new_aux_variable();
                                final_power_of_2_op2_expr =
                                    AirExpression::Trace(next_product_aux_var, RowOffset::Current);
                                let product_term_step = AirExpression::Mul(
                                    Box::new(prev_product_expr_val),
                                    Box::new(factor_val_expr.clone()),
                                );
                                air_constraints.push(AirExpression::Sub(
                                    Box::new(final_power_of_2_op2_expr.clone()),
                                    Box::new(product_term_step),
                                ));
                                println!(
                                    "        prod_step_s_{} (trace col {}): from prev_prod * factor_{}",
                                    i, next_product_aux_var.0, i
                                );
                            }
                        }
                        println!(
                            "      SHR: (Variable s) final_power_of_2_op2_expr (2^s) = {:?}",
                            final_power_of_2_op2_expr
                        );

                        let res_times_power_of_2 = AirExpression::Mul(
                            Box::new(res_expr.clone()),
                            Box::new(final_power_of_2_op2_expr.clone()),
                        );
                        let res_term_plus_rem = AirExpression::Add(
                            Box::new(res_times_power_of_2),
                            Box::new(rem_expr.clone()),
                        );
                        air_constraints.push(AirExpression::Sub(
                            Box::new(op1_expr.clone()),
                            Box::new(res_term_plus_rem),
                        ));
                        println!(
                            "    SHR: op2 is variable. Algebraic constraint op1 - (res*2^s + rem) = 0 added."
                        );

                        let ult_rem_lt_pow2s_res_var = self.ctx.new_aux_variable();
                        let ult_rem_lt_pow2s_res_expr =
                            AirExpression::Trace(ult_rem_lt_pow2s_res_var, RowOffset::Current);
                        println!(
                            "    SHR: ult_rem_lt_pow2s_res_var for (rem < 2^s) is {:?} (trace col {})",
                            ult_rem_lt_pow2s_res_var, ult_rem_lt_pow2s_res_var.0
                        );

                        air_constraints.push(AirExpression::Mul(
                            Box::new(ult_rem_lt_pow2s_res_expr.clone()),
                            Box::new(AirExpression::Sub(
                                Box::new(ult_rem_lt_pow2s_res_expr.clone()),
                                Box::new(AirExpression::Constant(1)),
                            )),
                        ));
                        air_constraints.push(AirExpression::Sub(
                            Box::new(ult_rem_lt_pow2s_res_expr.clone()),
                            Box::new(AirExpression::Constant(1)),
                        ));
                        println!(
                            "    SHR: Booleanity and assertion (must be 1) for ult_rem_lt_pow2s_res_expr added."
                        );

                        let mut pow2s_bit_exprs = Vec::new();
                        let mut pow2s_sum_terms = Vec::new();
                        println!(
                            "    SHR: Decomposing final_power_of_2_op2_expr ({:?}) into {} bits for ULT",
                            final_power_of_2_op2_expr, operand_bitwidth
                        );
                        for i in 0..operand_bitwidth {
                            let bit_aux = self.ctx.new_aux_variable();
                            let bit_expr = AirExpression::Trace(bit_aux, RowOffset::Current);
                            air_constraints.push(AirExpression::Mul(
                                Box::new(bit_expr.clone()),
                                Box::new(AirExpression::Sub(
                                    Box::new(bit_expr.clone()),
                                    Box::new(AirExpression::Constant(1)),
                                )),
                            ));
                            pow2s_bit_exprs.push(bit_expr.clone());
                            pow2s_sum_terms.push(AirExpression::Mul(
                                Box::new(bit_expr.clone()),
                                Box::new(AirExpression::Constant(1u128 << i)),
                            ));
                            println!(
                                "      pow2s_bit_{} (trace col {}) created for ULT decomposition",
                                i, bit_aux.0
                            );
                        }
                        let pow2s_reconstructed = pow2s_sum_terms
                            .into_iter()
                            .reduce(|acc, term| AirExpression::Add(Box::new(acc), Box::new(term)))
                            .unwrap_or_else(|| AirExpression::Constant(0));
                        air_constraints.push(AirExpression::Sub(
                            Box::new(final_power_of_2_op2_expr.clone()),
                            Box::new(pow2s_reconstructed),
                        ));
                        println!(
                            "    SHR: final_power_of_2_op2_expr decomposition constraint added for ULT."
                        );

                        let mut d_sum_bit_vars_ult_rem_pow2s = Vec::new();
                        println!(
                            "    SHR: Decomposing for D_sum in ULT(rem, 2^s) ({} bits)",
                            operand_bitwidth
                        );
                        for i in 0..operand_bitwidth {
                            let bit_aux_var = self.ctx.new_aux_variable();
                            let bit_expr_d = AirExpression::Trace(bit_aux_var, RowOffset::Current);
                            air_constraints.push(AirExpression::Mul(
                                Box::new(bit_expr_d.clone()),
                                Box::new(AirExpression::Sub(
                                    Box::new(bit_expr_d.clone()),
                                    Box::new(AirExpression::Constant(1)),
                                )),
                            ));
                            d_sum_bit_vars_ult_rem_pow2s.push(bit_expr_d);
                            println!(
                                "      ULT(rem, 2^s) D_sum bit_{} (trace col {}) created",
                                i, bit_aux_var.0
                            );
                        }
                        let d_sum_air_ult_rem_pow2s = d_sum_bit_vars_ult_rem_pow2s
                            .iter()
                            .enumerate()
                            .fold(AirExpression::Constant(0), |acc, (i, bit_e)| {
                                AirExpression::Add(
                                    Box::new(acc),
                                    Box::new(AirExpression::Mul(
                                        Box::new(bit_e.clone()),
                                        Box::new(AirExpression::Constant(1u128 << i)),
                                    )),
                                )
                            });
                        println!(
                            "    SHR: D_sum_air for ULT(rem, 2^s) constructed: {:?}",
                            d_sum_air_ult_rem_pow2s
                        );

                        let b_minus_a_minus_1_ult = AirExpression::Sub(
                            Box::new(AirExpression::Sub(
                                Box::new(final_power_of_2_op2_expr.clone()),
                                Box::new(rem_expr.clone()),
                            )),
                            Box::new(AirExpression::Constant(1)),
                        );
                        let term1_val_ult = AirExpression::Sub(
                            Box::new(b_minus_a_minus_1_ult),
                            Box::new(d_sum_air_ult_rem_pow2s.clone()),
                        );
                        air_constraints.push(AirExpression::Mul(
                            Box::new(ult_rem_lt_pow2s_res_expr.clone()),
                            Box::new(term1_val_ult),
                        ));
                        println!("    SHR: ULT(rem, 2^s) selector1 (res=1 path) constraint added.");

                        let one_minus_ult_res = AirExpression::Sub(
                            Box::new(AirExpression::Constant(1)),
                            Box::new(ult_rem_lt_pow2s_res_expr.clone()),
                        );
                        let a_minus_b_ult = AirExpression::Sub(
                            Box::new(rem_expr.clone()),
                            Box::new(final_power_of_2_op2_expr.clone()),
                        );
                        let term2_val_ult = AirExpression::Sub(
                            Box::new(a_minus_b_ult),
                            Box::new(d_sum_air_ult_rem_pow2s.clone()),
                        );
                        air_constraints.push(AirExpression::Mul(
                            Box::new(one_minus_ult_res),
                            Box::new(term2_val_ult),
                        ));
                        println!("    SHR: ULT(rem, 2^s) selector2 (res=0 path) constraint added.");
                    }
                }
                StructuredAirConstraint::AShr {
                    operand1,
                    operand2,
                    result,
                    operand_bitwidth,
                    block_name: _,
                } => {
                    let op1_expr = lang_operand_to_air_expression(operand1);
                    let op2_expr = lang_operand_to_air_expression(operand2);
                    let res_expr =
                        AirExpression::Trace(AirTraceVariable(result.0), RowOffset::Current);

                    let rem_ashr_aux_var = self.ctx.new_aux_variable();
                    let rem_ashr_expr = AirExpression::Trace(rem_ashr_aux_var, RowOffset::Current);
                    println!(
                        "  ASHR: op1={:?}, op2={:?}, res={:?}, rem_aux_var={:?}, operand_bitwidth={}",
                        op1_expr, op2_expr, res_expr, rem_ashr_aux_var, operand_bitwidth
                    );

                    let (_op1_bits, _op1_msb_expr_opt) = generate_signed_range_proof_constraints(
                        &op1_expr,
                        operand_bitwidth,
                        &mut self.ctx,
                        &mut air_constraints,
                        "ashr_op1",
                    );

                    let (_res_bits, _res_msb_expr_opt) = generate_signed_range_proof_constraints(
                        &res_expr,
                        operand_bitwidth,
                        &mut self.ctx,
                        &mut air_constraints,
                        "ashr_res",
                    );

                    let mut rem_ashr_bit_sum_terms = Vec::new();
                    println!(
                        "    ASHR: Decomposing remainder rem_ashr_expr ({:?}) into {} bits (unsigned proof)",
                        rem_ashr_expr, operand_bitwidth
                    );
                    for i in 0..operand_bitwidth {
                        let bit_aux = self.ctx.new_aux_variable();
                        let bit_expr = AirExpression::Trace(bit_aux, RowOffset::Current);
                        air_constraints.push(AirExpression::Mul(
                            Box::new(bit_expr.clone()),
                            Box::new(AirExpression::Sub(
                                Box::new(bit_expr.clone()),
                                Box::new(AirExpression::Constant(1)),
                            )),
                        ));
                        rem_ashr_bit_sum_terms.push(AirExpression::Mul(
                            Box::new(bit_expr.clone()),
                            Box::new(AirExpression::Constant(1u128 << i)),
                        ));
                        println!("      rem_ashr_bit_{} (trace col {}) created", i, bit_aux.0);
                    }
                    let rem_ashr_reconstructed = rem_ashr_bit_sum_terms
                        .into_iter()
                        .reduce(|acc, term| AirExpression::Add(Box::new(acc), Box::new(term)))
                        .unwrap_or_else(|| AirExpression::Constant(0));
                    air_constraints.push(AirExpression::Sub(
                        Box::new(rem_ashr_expr.clone()),
                        Box::new(rem_ashr_reconstructed),
                    ));
                    println!("    ASHR: Remainder rem_ashr_expr decomposition constraint added.");

                    if let AirExpression::Constant(s_const_val) = op2_expr {
                        if s_const_val >= operand_bitwidth.into() {
                            println!(
                                "    ASHR: op2 is const {} >= bitwidth {}. Constraining res based on op1_msb.",
                                s_const_val, operand_bitwidth
                            );
                            if let Some(op1_msb_expr) = _op1_msb_expr_opt.as_ref() {
                                let one_minus_op1_msb = AirExpression::Sub(
                                    Box::new(AirExpression::Constant(1)),
                                    Box::new(op1_msb_expr.clone()),
                                );
                                air_constraints.push(AirExpression::Mul(
                                    Box::new(one_minus_op1_msb),
                                    Box::new(res_expr.clone()),
                                ));
                                println!("      ASHR: Added constraint (1-op1_msb)*res = 0");

                                let res_plus_one = AirExpression::Add(
                                    Box::new(res_expr.clone()),
                                    Box::new(AirExpression::Constant(1)),
                                );
                                air_constraints.push(AirExpression::Mul(
                                    Box::new(op1_msb_expr.clone()),
                                    Box::new(res_plus_one),
                                ));
                                println!("      ASHR: Added constraint op1_msb*(res+1) = 0");
                            } else {
                                println!(
                                    "    ASHR: WARN - op1_msb_expr not available for s_const_val >= operand_bitwidth case. Cannot constrain res directly based on op1 sign."
                                );
                            }

                            let power_of_2_s_val = if s_const_val >= 128 {
                                0
                            } else {
                                1u128.wrapping_shl(s_const_val as u32)
                            };
                            let power_of_2_s_expr = AirExpression::Constant(power_of_2_s_val);
                            let res_times_power_of_2 = AirExpression::Mul(
                                Box::new(res_expr.clone()),
                                Box::new(power_of_2_s_expr.clone()),
                            );
                            let res_term_plus_rem = AirExpression::Add(
                                Box::new(res_times_power_of_2),
                                Box::new(rem_ashr_expr.clone()),
                            );
                            air_constraints.push(AirExpression::Sub(
                                Box::new(op1_expr.clone()),
                                Box::new(res_term_plus_rem),
                            ));
                            println!(
                                "    ASHR: op2 is const {} >= bitwidth {}. Main algebraic constraint op1 - (res*2^{} + rem) = 0 added, 2^{} evaluates to {}.",
                                s_const_val,
                                operand_bitwidth,
                                s_const_val,
                                s_const_val,
                                power_of_2_s_val
                            );
                        } else {
                            let power_of_2_s_val = 1u128.wrapping_shl(s_const_val as u32);
                            let power_of_2_s_expr = AirExpression::Constant(power_of_2_s_val);

                            let res_times_power_of_2 = AirExpression::Mul(
                                Box::new(res_expr.clone()),
                                Box::new(power_of_2_s_expr.clone()),
                            );
                            let res_term_plus_rem = AirExpression::Add(
                                Box::new(res_times_power_of_2),
                                Box::new(rem_ashr_expr.clone()),
                            );
                            air_constraints.push(AirExpression::Sub(
                                Box::new(op1_expr.clone()),
                                Box::new(res_term_plus_rem),
                            ));
                            println!(
                                "    ASHR: op2 is const {}. Algebraic constraint op1 - (res*2^{} + rem) = 0 added.",
                                s_const_val, s_const_val
                            );
                        }
                    } else {
                        println!("    ASHR: op2 is variable: {:?}", op2_expr);
                        let num_shift_bits = if operand_bitwidth == 1 {
                            1
                        } else {
                            (operand_bitwidth - 1).ilog2() + 1
                        };

                        let mut s_bit_exprs = Vec::new();
                        let mut op2_sum_terms_recon = Vec::new();
                        for i in 0..num_shift_bits {
                            let bit_aux_var = self.ctx.new_aux_variable();
                            let bit_expr = AirExpression::Trace(bit_aux_var, RowOffset::Current);
                            air_constraints.push(AirExpression::Mul(
                                Box::new(bit_expr.clone()),
                                Box::new(AirExpression::Sub(
                                    Box::new(bit_expr.clone()),
                                    Box::new(AirExpression::Constant(1)),
                                )),
                            ));
                            s_bit_exprs.push(bit_expr.clone());
                            op2_sum_terms_recon.push(AirExpression::Mul(
                                Box::new(bit_expr.clone()),
                                Box::new(AirExpression::Constant(1u128 << i)),
                            ));
                        }
                        let op2_reconstructed_expr = op2_sum_terms_recon
                            .into_iter()
                            .reduce(|acc, term| AirExpression::Add(Box::new(acc), Box::new(term)))
                            .unwrap_or_else(|| AirExpression::Constant(0));
                        air_constraints.push(AirExpression::Sub(
                            Box::new(op2_expr.clone()),
                            Box::new(op2_reconstructed_expr),
                        ));

                        let mut factor_exprs_for_prod = Vec::new();
                        for i in 0..num_shift_bits {
                            let s_i_expr = &s_bit_exprs[i as usize];
                            let exp_base_power = 1u128 << i;
                            let exp_val_i = if exp_base_power >= 128 {
                                0
                            } else {
                                1u128.wrapping_shl(exp_base_power as u32)
                            };
                            let factor_i_aux_var = self.ctx.new_aux_variable();
                            let factor_i_expr_aux =
                                AirExpression::Trace(factor_i_aux_var, RowOffset::Current);
                            let exp_val_i_minus_1 = exp_val_i.saturating_sub(1);
                            let term_mul_factor = AirExpression::Mul(
                                Box::new(s_i_expr.clone()),
                                Box::new(AirExpression::Constant(exp_val_i_minus_1)),
                            );
                            let term_sum_factor = AirExpression::Add(
                                Box::new(term_mul_factor),
                                Box::new(AirExpression::Constant(1)),
                            );
                            air_constraints.push(AirExpression::Sub(
                                Box::new(factor_i_expr_aux.clone()),
                                Box::new(term_sum_factor),
                            ));
                            factor_exprs_for_prod.push(factor_i_expr_aux.clone());
                        }

                        let mut final_power_of_2_op2_expr = AirExpression::Constant(1);
                        if !factor_exprs_for_prod.is_empty() {
                            final_power_of_2_op2_expr = factor_exprs_for_prod[0].clone();
                            for i in 1..factor_exprs_for_prod.len() {
                                let prev_product_expr_val = final_power_of_2_op2_expr.clone();
                                let factor_val_expr = &factor_exprs_for_prod[i];
                                let next_product_aux_var = self.ctx.new_aux_variable();
                                final_power_of_2_op2_expr =
                                    AirExpression::Trace(next_product_aux_var, RowOffset::Current);
                                let product_term_step = AirExpression::Mul(
                                    Box::new(prev_product_expr_val),
                                    Box::new(factor_val_expr.clone()),
                                );
                                air_constraints.push(AirExpression::Sub(
                                    Box::new(final_power_of_2_op2_expr.clone()),
                                    Box::new(product_term_step),
                                ));
                                println!(
                                    "        prod_step_s_{} (trace col {}): from prev_prod * factor_{}",
                                    i, next_product_aux_var.0, i
                                );
                            }
                        }

                        let res_times_power_of_2 = AirExpression::Mul(
                            Box::new(res_expr.clone()),
                            Box::new(final_power_of_2_op2_expr.clone()),
                        );
                        let res_term_plus_rem = AirExpression::Add(
                            Box::new(res_times_power_of_2),
                            Box::new(rem_ashr_expr.clone()),
                        );
                        air_constraints.push(AirExpression::Sub(
                            Box::new(op1_expr.clone()),
                            Box::new(res_term_plus_rem),
                        ));
                        println!(
                            "    ASHR: op2 is variable. Algebraic constraint op1 - (res*2^s + rem) = 0 added."
                        );

                        let ult_rem_ashr_lt_pow2s_res_var = self.ctx.new_aux_variable();
                        let ult_rem_ashr_lt_pow2s_res_expr =
                            AirExpression::Trace(ult_rem_ashr_lt_pow2s_res_var, RowOffset::Current);
                        println!(
                            "    ASHR: ult_rem_ashr_lt_pow2s_res_var for (rem_ashr < 2^s) is {:?} (trace col {})",
                            ult_rem_ashr_lt_pow2s_res_var, ult_rem_ashr_lt_pow2s_res_var.0
                        );

                        air_constraints.push(AirExpression::Mul(
                            Box::new(ult_rem_ashr_lt_pow2s_res_expr.clone()),
                            Box::new(AirExpression::Sub(
                                Box::new(ult_rem_ashr_lt_pow2s_res_expr.clone()),
                                Box::new(AirExpression::Constant(1)),
                            )),
                        ));
                        air_constraints.push(AirExpression::Sub(
                            Box::new(ult_rem_ashr_lt_pow2s_res_expr.clone()),
                            Box::new(AirExpression::Constant(1)),
                        ));
                        println!(
                            "    ASHR: Booleanity and assertion (must be 1) for ult_rem_ashr_lt_pow2s_res_expr added."
                        );

                        let mut pow2s_bit_exprs_ashr = Vec::new();
                        let mut pow2s_sum_terms_ashr = Vec::new();
                        println!(
                            "    ASHR: Decomposing final_power_of_2_op2_expr ({:?}) into {} bits for ULT",
                            final_power_of_2_op2_expr, operand_bitwidth
                        );
                        for i in 0..operand_bitwidth {
                            let bit_aux = self.ctx.new_aux_variable();
                            let bit_expr = AirExpression::Trace(bit_aux, RowOffset::Current);
                            air_constraints.push(AirExpression::Mul(
                                Box::new(bit_expr.clone()),
                                Box::new(AirExpression::Sub(
                                    Box::new(bit_expr.clone()),
                                    Box::new(AirExpression::Constant(1)),
                                )),
                            ));
                            pow2s_bit_exprs_ashr.push(bit_expr.clone());
                            pow2s_sum_terms_ashr.push(AirExpression::Mul(
                                Box::new(bit_expr.clone()),
                                Box::new(AirExpression::Constant(1u128 << i)),
                            ));
                            println!(
                                "      pow2s_ashr_bit_{} (trace col {}) created for ULT decomposition",
                                i, bit_aux.0
                            );
                        }
                        let pow2s_reconstructed_ashr = pow2s_sum_terms_ashr
                            .into_iter()
                            .reduce(|acc, term| AirExpression::Add(Box::new(acc), Box::new(term)))
                            .unwrap_or_else(|| AirExpression::Constant(0));
                        air_constraints.push(AirExpression::Sub(
                            Box::new(final_power_of_2_op2_expr.clone()),
                            Box::new(pow2s_reconstructed_ashr),
                        ));
                        println!(
                            "    ASHR: final_power_of_2_op2_expr decomposition constraint added for ULT."
                        );

                        let mut d_sum_bit_vars_ult_rem_ashr_pow2s = Vec::new();
                        println!(
                            "    ASHR: Decomposing for D_sum in ULT(rem_ashr, 2^s) ({} bits)",
                            operand_bitwidth
                        );
                        for i in 0..operand_bitwidth {
                            let bit_aux_var = self.ctx.new_aux_variable();
                            let bit_expr_d = AirExpression::Trace(bit_aux_var, RowOffset::Current);
                            air_constraints.push(AirExpression::Mul(
                                Box::new(bit_expr_d.clone()),
                                Box::new(AirExpression::Sub(
                                    Box::new(bit_expr_d.clone()),
                                    Box::new(AirExpression::Constant(1)),
                                )),
                            ));
                            d_sum_bit_vars_ult_rem_ashr_pow2s.push(bit_expr_d);
                            println!(
                                "      ULT(rem_ashr, 2^s) D_sum bit_{} (trace col {}) created",
                                i, bit_aux_var.0
                            );
                        }
                        let d_sum_air_ult_rem_ashr_pow2s = d_sum_bit_vars_ult_rem_ashr_pow2s
                            .iter()
                            .enumerate()
                            .fold(AirExpression::Constant(0), |acc, (i, bit_e)| {
                                AirExpression::Add(
                                    Box::new(acc),
                                    Box::new(AirExpression::Mul(
                                        Box::new(bit_e.clone()),
                                        Box::new(AirExpression::Constant(1u128 << i)),
                                    )),
                                )
                            });
                        println!(
                            "    ASHR: D_sum_air for ULT(rem_ashr, 2^s) constructed: {:?}",
                            d_sum_air_ult_rem_ashr_pow2s
                        );

                        let b_minus_a_minus_1_ult_ashr = AirExpression::Sub(
                            Box::new(AirExpression::Sub(
                                Box::new(final_power_of_2_op2_expr.clone()),
                                Box::new(rem_ashr_expr.clone()),
                            )),
                            Box::new(AirExpression::Constant(1)),
                        );
                        let term1_val_ult_ashr = AirExpression::Sub(
                            Box::new(b_minus_a_minus_1_ult_ashr),
                            Box::new(d_sum_air_ult_rem_ashr_pow2s.clone()),
                        );
                        air_constraints.push(AirExpression::Mul(
                            Box::new(ult_rem_ashr_lt_pow2s_res_expr.clone()),
                            Box::new(term1_val_ult_ashr),
                        ));
                        println!(
                            "    ASHR: ULT(rem_ashr, 2^s) selector1 (res=1 path) constraint added."
                        );

                        let one_minus_ult_res_ashr = AirExpression::Sub(
                            Box::new(AirExpression::Constant(1)),
                            Box::new(ult_rem_ashr_lt_pow2s_res_expr.clone()),
                        );
                        let a_minus_b_ult_ashr = AirExpression::Sub(
                            Box::new(rem_ashr_expr.clone()),
                            Box::new(final_power_of_2_op2_expr.clone()),
                        );
                        let term2_val_ult_ashr = AirExpression::Sub(
                            Box::new(a_minus_b_ult_ashr),
                            Box::new(d_sum_air_ult_rem_ashr_pow2s.clone()),
                        );
                        air_constraints.push(AirExpression::Mul(
                            Box::new(one_minus_ult_res_ashr),
                            Box::new(term2_val_ult_ashr),
                        ));
                        println!(
                            "    ASHR: ULT(rem_ashr, 2^s) selector2 (res=0 path) constraint added."
                        );
                    }
                }
                StructuredAirConstraint::UDiv {
                    operand1: dividend_op,
                    operand2: divisor_op,
                    result: quotient_var,
                    block_name: _,
                    operand_bitwidth,
                } => {
                    let a_expr = lang_operand_to_air_expression(dividend_op);
                    let b_expr = lang_operand_to_air_expression(divisor_op);
                    let q_expr =
                        AirExpression::Trace(AirTraceVariable(quotient_var.0), RowOffset::Current);

                    let r_aux_var = self.ctx.new_aux_variable();
                    let r_expr = AirExpression::Trace(r_aux_var, RowOffset::Current);
                    println!(
                        "  UDIV: dividend={:?}, divisor={:?}, quotient_var={:?}, remainder_aux_var={:?} (bitwidth {})",
                        dividend_op, divisor_op, quotient_var, r_aux_var, operand_bitwidth
                    );

                    self.ctx
                        .add_unsigned_range_proof_constraints(a_expr.clone(), operand_bitwidth);
                    self.ctx
                        .add_unsigned_range_proof_constraints(b_expr.clone(), operand_bitwidth);
                    self.ctx
                        .add_unsigned_range_proof_constraints(q_expr.clone(), operand_bitwidth);
                    self.ctx
                        .add_unsigned_range_proof_constraints(r_expr.clone(), operand_bitwidth);

                    let q_times_b =
                        AirExpression::Mul(Box::new(q_expr.clone()), Box::new(b_expr.clone()));
                    let qb_plus_r =
                        AirExpression::Add(Box::new(q_times_b), Box::new(r_expr.clone()));
                    air_constraints.push(AirExpression::Sub(
                        Box::new(a_expr.clone()),
                        Box::new(qb_plus_r),
                    ));
                    println!("    UDIV: Constraint a-(q*b+r)=0 added.");

                    let mut r_bit_vars_exprs = Vec::new();
                    let mut r_sum_terms = Vec::new();
                    println!(
                        "    UDIV: Decomposing remainder r ({:?}) into {} bits",
                        r_aux_var, operand_bitwidth
                    );
                    for i in 0..operand_bitwidth {
                        let bit_aux_var = self.ctx.new_aux_variable();
                        let bit_expr = AirExpression::Trace(bit_aux_var, RowOffset::Current);
                        let bit_minus_one = AirExpression::Sub(
                            Box::new(bit_expr.clone()),
                            Box::new(AirExpression::Constant(1)),
                        );
                        air_constraints.push(AirExpression::Mul(
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
                    air_constraints.push(AirExpression::Sub(
                        Box::new(r_expr.clone()),
                        Box::new(r_sum_from_bits),
                    ));
                    println!("    UDIV: Remainder r decomposition constraint added.");

                    let ult_res_r_lt_b_var = self.ctx.new_aux_variable();
                    let ult_res_r_lt_b_expr =
                        AirExpression::Trace(ult_res_r_lt_b_var, RowOffset::Current);
                    println!(
                        "    UDIV: ult_res_r_lt_b_var for (r < b) is {:?}",
                        ult_res_r_lt_b_var
                    );

                    let ult_res_minus_one = AirExpression::Sub(
                        Box::new(ult_res_r_lt_b_expr.clone()),
                        Box::new(AirExpression::Constant(1)),
                    );
                    air_constraints.push(AirExpression::Mul(
                        Box::new(ult_res_r_lt_b_expr.clone()),
                        Box::new(ult_res_minus_one),
                    ));

                    air_constraints.push(AirExpression::Sub(
                        Box::new(ult_res_r_lt_b_expr.clone()),
                        Box::new(AirExpression::Constant(1)),
                    ));
                    println!(
                        "    UDIV: Booleanity and assertion (must be 1) for ult_res_r_lt_b added."
                    );

                    let mut ult_bit_vars_air_exprs = Vec::new();
                    println!(
                        "    UDIV: Decomposing for D_sum in ULT(r,b) ({} bits)",
                        operand_bitwidth
                    );
                    for i in 0..operand_bitwidth {
                        let bit_aux_var = self.ctx.new_aux_variable();
                        let bit_expr_d = AirExpression::Trace(bit_aux_var, RowOffset::Current);
                        let bit_minus_one_d = AirExpression::Sub(
                            Box::new(bit_expr_d.clone()),
                            Box::new(AirExpression::Constant(1)),
                        );
                        air_constraints.push(AirExpression::Mul(
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
                            Some(current_sum) => {
                                Box::new(AirExpression::Add(current_sum, Box::new(term)))
                            }
                            None => Box::new(term),
                        });
                    }
                    let d_sum_air_ult =
                        d_sum_air_ult.unwrap_or_else(|| Box::new(AirExpression::Constant(0)));
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
                    let term1_val_ult =
                        AirExpression::Sub(Box::new(b_minus_r_minus_1), d_sum_air_ult.clone());
                    air_constraints.push(AirExpression::Mul(
                        Box::new(ult_res_r_lt_b_expr.clone()),
                        Box::new(term1_val_ult),
                    ));
                    println!("    UDIV: ULT(r,b) selector1 (res=1 path) constraint added.");

                    let one_minus_ult_res = AirExpression::Sub(
                        Box::new(AirExpression::Constant(1)),
                        Box::new(ult_res_r_lt_b_expr.clone()),
                    );
                    let r_minus_b =
                        AirExpression::Sub(Box::new(r_expr.clone()), Box::new(b_expr.clone()));
                    let term2_val_ult =
                        AirExpression::Sub(Box::new(r_minus_b), d_sum_air_ult.clone());
                    air_constraints.push(AirExpression::Mul(
                        Box::new(one_minus_ult_res),
                        Box::new(term2_val_ult),
                    ));
                    println!("    UDIV: ULT(r,b) selector2 (res=0 path) constraint added.");
                }
                StructuredAirConstraint::SDiv {
                    operand1: dividend_op,
                    operand2: divisor_op,
                    result: quotient_var,
                    block_name: _,
                    operand_bitwidth,
                } => {
                    let a_expr = lang_operand_to_air_expression(dividend_op);
                    let b_expr = lang_operand_to_air_expression(divisor_op);
                    let q_expr =
                        AirExpression::Trace(AirTraceVariable(quotient_var.0), RowOffset::Current);

                    let r_aux_var = self.ctx.new_aux_variable();
                    let r_expr = AirExpression::Trace(r_aux_var, RowOffset::Current);
                    println!(
                        "  SDIV: dividend={:?}, divisor={:?}, quotient_var={:?}, remainder_aux_var={:?} (bitwidth {})",
                        dividend_op, divisor_op, quotient_var, r_aux_var, operand_bitwidth
                    );

                    self.ctx
                        .add_signed_range_proof_constraints(a_expr.clone(), operand_bitwidth);
                    self.ctx
                        .add_signed_range_proof_constraints(b_expr.clone(), operand_bitwidth);
                    self.ctx
                        .add_signed_range_proof_constraints(q_expr.clone(), operand_bitwidth);

                    let is_a_zero_aux = self.ctx.new_aux_variable();
                    let is_a_zero_expr = AirExpression::Trace(is_a_zero_aux, RowOffset::Current);
                    air_constraints.push(AirExpression::Mul(
                        Box::new(is_a_zero_expr.clone()),
                        Box::new(AirExpression::Sub(
                            Box::new(is_a_zero_expr.clone()),
                            Box::new(AirExpression::Constant(1)),
                        )),
                    ));
                    air_constraints.push(AirExpression::Mul(
                        Box::new(is_a_zero_expr.clone()),
                        Box::new(a_expr.clone()),
                    ));
                    println!(
                        "    SDIV: is_a_zero_aux {:?} (bool + def: is_a_zero*a=0) added early.",
                        is_a_zero_aux
                    );

                    let q_times_b =
                        AirExpression::Mul(Box::new(q_expr.clone()), Box::new(b_expr.clone()));
                    let qb_plus_r =
                        AirExpression::Add(Box::new(q_times_b), Box::new(r_expr.clone()));
                    air_constraints.push(AirExpression::Sub(
                        Box::new(a_expr.clone()),
                        Box::new(qb_plus_r),
                    ));
                    println!("    SDIV: Constraint a-(q*b+r)=0 added.");

                    let (_a_bits, a_msb_expr_opt) = generate_signed_range_proof_constraints(
                        &a_expr,
                        operand_bitwidth,
                        &mut self.ctx,
                        &mut air_constraints,
                        "a",
                    );
                    let (_b_bits, b_msb_expr_opt) = generate_signed_range_proof_constraints(
                        &b_expr,
                        operand_bitwidth,
                        &mut self.ctx,
                        &mut air_constraints,
                        "b",
                    );
                    let (_q_bits, q_msb_expr_opt) = generate_signed_range_proof_constraints(
                        &q_expr,
                        operand_bitwidth,
                        &mut self.ctx,
                        &mut air_constraints,
                        "q",
                    );
                    let (_r_bits, r_msb_expr_opt) = generate_signed_range_proof_constraints(
                        &r_expr,
                        operand_bitwidth,
                        &mut self.ctx,
                        &mut air_constraints,
                        "r",
                    );

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
                        air_constraints.push(AirExpression::Mul(
                            Box::new(one_minus_is_a_zero),
                            Box::new(a_msb_minus_r_msb),
                        ));
                        println!("      SDIV RemSign: (1-is_a_zero)*(a_msb-r_msb)=0 added.");

                        air_constraints.push(AirExpression::Mul(
                            Box::new(is_a_zero_expr.clone()),
                            Box::new(r_expr.clone()),
                        ));
                        println!("      SDIV RemSign: is_a_zero * r = 0 added.");
                    } else {
                        println!(
                            "    SDIV: WARN - Could not implement Remainder Sign constraint due to missing MSB for 'a' or 'r'. operand_bitwidth: {}",
                            operand_bitwidth
                        );
                    }

                    if let (Some(r_msb_expr_val_mag), Some(b_msb_expr_val_mag)) =
                        (r_msb_expr_opt.as_ref(), b_msb_expr_opt.as_ref())
                    {
                        println!(
                            "    SDIV: Implementing Remainder Magnitude Constraint abs(r) < abs(b)"
                        );

                        let one_const = AirExpression::Constant(1);
                        let two_const = AirExpression::Constant(2);

                        let one_minus_two_r_msb = AirExpression::Sub(
                            Box::new(one_const.clone()),
                            Box::new(AirExpression::Mul(
                                Box::new(two_const.clone()),
                                Box::new(r_msb_expr_val_mag.clone()),
                            )),
                        );
                        let abs_r_expr = AirExpression::Mul(
                            Box::new(r_expr.clone()),
                            Box::new(one_minus_two_r_msb),
                        );
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
                        let abs_b_expr = AirExpression::Mul(
                            Box::new(b_expr.clone()),
                            Box::new(one_minus_two_b_msb),
                        );
                        println!(
                            "      SDIV Mag: abs_b_expr = b * (1 - 2*b_msb) = {:?}",
                            abs_b_expr
                        );

                        let ult_res_abs_r_lt_abs_b_var = self.ctx.new_aux_variable();
                        let ult_res_abs_r_lt_abs_b_expr =
                            AirExpression::Trace(ult_res_abs_r_lt_abs_b_var, RowOffset::Current);
                        println!(
                            "      SDIV Mag: ult_res_var for (abs(r) < abs(b)) is {:?}",
                            ult_res_abs_r_lt_abs_b_var
                        );

                        air_constraints.push(AirExpression::Mul(
                            Box::new(ult_res_abs_r_lt_abs_b_expr.clone()),
                            Box::new(AirExpression::Sub(
                                Box::new(ult_res_abs_r_lt_abs_b_expr.clone()),
                                Box::new(AirExpression::Constant(1)),
                            )),
                        ));
                        air_constraints.push(AirExpression::Sub(
                            Box::new(ult_res_abs_r_lt_abs_b_expr.clone()),
                            Box::new(AirExpression::Constant(1)),
                        ));
                        println!(
                            "      SDIV Mag: Booleanity and assertion (must be 1) for ult_res_var added."
                        );

                        let mut d_sum_bit_vars_ult_mag = Vec::new();
                        println!(
                            "      SDIV Mag: Decomposing for D_sum in ULT(abs_r, abs_b) ({} bits)",
                            operand_bitwidth
                        );
                        if operand_bitwidth > 0 {
                            for i in 0..operand_bitwidth {
                                let bit_aux_var = self.ctx.new_aux_variable();
                                let bit_expr_d =
                                    AirExpression::Trace(bit_aux_var, RowOffset::Current);
                                air_constraints.push(AirExpression::Mul(
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
                        air_constraints.push(ult_final_constraint);
                        println!(
                            "      SDIV Mag: ULT(abs_r,abs_b) constraint ( (abs_b - abs_r - 1) - D_sum = 0) added."
                        );
                    } else {
                        println!(
                            "    SDIV: WARN - Could not implement Remainder Magnitude constraint due to missing MSB for 'r' or 'b'. operand_bitwidth: {}",
                            operand_bitwidth
                        );
                    }

                    if let (
                        Some(a_msb_expr_val_qs),
                        Some(b_msb_expr_val_qs),
                        Some(q_msb_expr_val_qs),
                    ) = (
                        a_msb_expr_opt.as_ref(),
                        b_msb_expr_opt.as_ref(),
                        q_msb_expr_opt.as_ref(),
                    ) {
                        println!(
                            "    SDIV: Implementing Quotient Sign Constraint using a_msb={:?}, b_msb={:?}, q_msb={:?}",
                            a_msb_expr_val_qs, b_msb_expr_val_qs, q_msb_expr_val_qs
                        );

                        let is_b_zero_aux = self.ctx.new_aux_variable();
                        let is_b_zero_expr =
                            AirExpression::Trace(is_b_zero_aux, RowOffset::Current);
                        air_constraints.push(AirExpression::Mul(
                            Box::new(is_b_zero_expr.clone()),
                            Box::new(AirExpression::Sub(
                                Box::new(is_b_zero_expr.clone()),
                                Box::new(AirExpression::Constant(1)),
                            )),
                        ));
                        air_constraints.push(AirExpression::Mul(
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

                        let condition_apply_sign_logic_aux = self.ctx.new_aux_variable();
                        let condition_apply_sign_logic_expr = AirExpression::Trace(
                            condition_apply_sign_logic_aux,
                            RowOffset::Current,
                        );
                        air_constraints.push(AirExpression::Mul(
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
                        air_constraints.push(AirExpression::Sub(
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
                        let xor_val_expr = AirExpression::Sub(
                            Box::new(a_msb_plus_b_msb),
                            Box::new(two_a_msb_b_msb),
                        );

                        let xor_minus_q_msb = AirExpression::Sub(
                            Box::new(xor_val_expr),
                            Box::new(q_msb_expr_val_qs.clone()),
                        );
                        air_constraints.push(AirExpression::Mul(
                            Box::new(condition_apply_sign_logic_expr.clone()),
                            Box::new(xor_minus_q_msb),
                        ));
                        println!("      SDIV QuotSign: conditional XOR logic for q_msb added.");

                        air_constraints.push(AirExpression::Mul(
                            Box::new(is_a_zero_expr.clone()),
                            Box::new(q_msb_expr_val_qs.clone()),
                        ));
                        println!("      SDIV QuotSign: is_a_zero * q_msb = 0 added.");
                    } else {
                        println!(
                            "    SDIV: WARN - Could not implement Quotient Sign constraint due to missing MSB for 'a', 'b', or 'q'. operand_bitwidth: {}",
                            operand_bitwidth
                        );
                    }
                }
                StructuredAirConstraint::Icmp {
                    cond,
                    operand1,
                    operand2,
                    result,
                    operand_bitwidth,
                    block_name: _,
                } => {
                    let res_air_var = AirTraceVariable(result.0);
                    let res_expr = AirExpression::Trace(res_air_var, RowOffset::Current);

                    let res_minus_one = AirExpression::Sub(
                        Box::new(res_expr.clone()),
                        Box::new(AirExpression::Constant(1)),
                    );
                    air_constraints.push(AirExpression::Mul(
                        Box::new(res_expr.clone()),
                        Box::new(res_minus_one),
                    ));

                    match cond {
                        LangIntPredicate::EQ => {
                            let op1_air = lang_operand_to_air_expression(operand1);
                            let op2_air = lang_operand_to_air_expression(operand2);
                            let diff_expr =
                                AirExpression::Sub(Box::new(op1_air), Box::new(op2_air));
                            air_constraints.push(AirExpression::Mul(
                                Box::new(diff_expr),
                                Box::new(res_expr.clone()),
                            ));
                        }
                        LangIntPredicate::NE => {
                            let op1_air = lang_operand_to_air_expression(operand1);
                            let op2_air = lang_operand_to_air_expression(operand2);
                            let one_minus_res = AirExpression::Sub(
                                Box::new(AirExpression::Constant(1)),
                                Box::new(res_expr.clone()),
                            );
                            let diff_expr =
                                AirExpression::Sub(Box::new(op1_air), Box::new(op2_air));
                            air_constraints.push(AirExpression::Mul(
                                Box::new(diff_expr),
                                Box::new(one_minus_res),
                            ));
                        }
                        LangIntPredicate::ULT | LangIntPredicate::UGT => {
                            let op1_air_orig = lang_operand_to_air_expression(operand1);
                            let op2_air_orig = lang_operand_to_air_expression(operand2);

                            let a_expr = if cond == LangIntPredicate::ULT {
                                op1_air_orig.clone()
                            } else {
                                op2_air_orig.clone()
                            };
                            let b_expr = if cond == LangIntPredicate::ULT {
                                op2_air_orig.clone()
                            } else {
                                op1_air_orig.clone()
                            };

                            println!(
                                "ICMP {:?}: op_bitwidth = {}, a={:?}, b={:?}, res={:?}",
                                cond, operand_bitwidth, a_expr, b_expr, res_expr
                            );

                            let mut bit_vars_air_exprs = Vec::new();
                            for i in 0..operand_bitwidth {
                                let bit_aux_var = self.ctx.new_aux_variable();
                                let bit_expr_aux =
                                    AirExpression::Trace(bit_aux_var, RowOffset::Current);
                                let bit_minus_one_aux = AirExpression::Sub(
                                    Box::new(bit_expr_aux.clone()),
                                    Box::new(AirExpression::Constant(1)),
                                );
                                air_constraints.push(AirExpression::Mul(
                                    Box::new(bit_expr_aux.clone()),
                                    Box::new(bit_minus_one_aux),
                                ));
                                bit_vars_air_exprs.push(bit_expr_aux);
                                println!(
                                    "  {:?}: Added booleanity for bit_aux_var {:?} (orig idx {}), trace col idx {}",
                                    cond, bit_aux_var, i, bit_aux_var.0
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
                            let d_sum_air =
                                d_sum_air.unwrap_or_else(|| Box::new(AirExpression::Constant(0)));
                            println!("  {:?}: D_sum_air constructed: {:?}", cond, d_sum_air);

                            let b_minus_a_minus_1 = AirExpression::Sub(
                                Box::new(AirExpression::Sub(
                                    Box::new(b_expr.clone()),
                                    Box::new(a_expr.clone()),
                                )),
                                Box::new(AirExpression::Constant(1)),
                            );
                            let term1_val =
                                AirExpression::Sub(Box::new(b_minus_a_minus_1), d_sum_air.clone());
                            air_constraints.push(AirExpression::Mul(
                                Box::new(res_expr.clone()),
                                Box::new(term1_val),
                            ));
                            println!("  {:?}: Constraint (res=1 path) generated.", cond);

                            let one_minus_res = AirExpression::Sub(
                                Box::new(AirExpression::Constant(1)),
                                Box::new(res_expr.clone()),
                            );
                            let a_minus_b = AirExpression::Sub(
                                Box::new(a_expr.clone()),
                                Box::new(b_expr.clone()),
                            );
                            let term2_val =
                                AirExpression::Sub(Box::new(a_minus_b), d_sum_air.clone());
                            air_constraints.push(AirExpression::Mul(
                                Box::new(one_minus_res),
                                Box::new(term2_val),
                            ));
                            println!("  {:?}: Constraint (res=0 path) generated.", cond);
                        }
                        LangIntPredicate::ULE | LangIntPredicate::UGE => {
                            let op1_air_orig = lang_operand_to_air_expression(operand1);
                            let op2_air_orig = lang_operand_to_air_expression(operand2);

                            let is_ule = cond == LangIntPredicate::ULE;
                            let internal_predicate = if is_ule {
                                LangIntPredicate::UGT
                            } else {
                                LangIntPredicate::ULT
                            };

                            println!(
                                "ICMP {:?}: Internally using {:?} with op_bitwidth = {}",
                                cond, internal_predicate, operand_bitwidth
                            );

                            let aux_res_var = self.ctx.new_aux_variable();
                            let aux_res_expr =
                                AirExpression::Trace(aux_res_var, RowOffset::Current);

                            let aux_res_minus_one = AirExpression::Sub(
                                Box::new(aux_res_expr.clone()),
                                Box::new(AirExpression::Constant(1)),
                            );
                            air_constraints.push(AirExpression::Mul(
                                Box::new(aux_res_expr.clone()),
                                Box::new(aux_res_minus_one),
                            ));
                            println!(
                                "  {:?}: Added booleanity for aux_res_var {:?}",
                                cond, aux_res_var
                            );

                            let a_expr_internal: AirExpression;
                            let b_expr_internal: AirExpression;

                            if internal_predicate == LangIntPredicate::ULT {
                                a_expr_internal = op1_air_orig.clone();
                                b_expr_internal = op2_air_orig.clone();
                            } else {
                                a_expr_internal = op2_air_orig.clone();
                                b_expr_internal = op1_air_orig.clone();
                            }
                            println!(
                                "  {:?}: Internal predicate {:?} uses a_internal={:?}, b_internal={:?}, aux_res={:?}",
                                cond,
                                internal_predicate,
                                a_expr_internal,
                                b_expr_internal,
                                aux_res_expr
                            );

                            let mut bit_vars_air_exprs = Vec::new();
                            for i in 0..operand_bitwidth {
                                let bit_aux_var = self.ctx.new_aux_variable();
                                let bit_expr_d =
                                    AirExpression::Trace(bit_aux_var, RowOffset::Current);
                                let bit_minus_one_d = AirExpression::Sub(
                                    Box::new(bit_expr_d.clone()),
                                    Box::new(AirExpression::Constant(1)),
                                );
                                air_constraints.push(AirExpression::Mul(
                                    Box::new(bit_expr_d.clone()),
                                    Box::new(bit_minus_one_d),
                                ));
                                bit_vars_air_exprs.push(bit_expr_d);
                                println!(
                                    "    {:?}: Added booleanity for bit_aux_var {:?} (orig idx {}), trace col idx {}",
                                    cond, bit_aux_var, i, bit_aux_var.0
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
                            let d_sum_air =
                                d_sum_air.unwrap_or_else(|| Box::new(AirExpression::Constant(0)));
                            println!(
                                "  {:?}: D_sum_air for internal op constructed: {:?}",
                                cond, d_sum_air
                            );

                            let b_i_minus_a_i_minus_1 = AirExpression::Sub(
                                Box::new(AirExpression::Sub(
                                    Box::new(b_expr_internal.clone()),
                                    Box::new(a_expr_internal.clone()),
                                )),
                                Box::new(AirExpression::Constant(1)),
                            );
                            let term1_val_internal = AirExpression::Sub(
                                Box::new(b_i_minus_a_i_minus_1),
                                d_sum_air.clone(),
                            );
                            air_constraints.push(AirExpression::Mul(
                                Box::new(aux_res_expr.clone()),
                                Box::new(term1_val_internal),
                            ));
                            println!("  {:?}: Internal selector1 generated.", cond);

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
                            air_constraints.push(AirExpression::Mul(
                                Box::new(one_minus_aux_res),
                                Box::new(term2_val_internal),
                            ));
                            println!("  {:?}: Internal selector2 generated.", cond);

                            let sum_res_aux = AirExpression::Add(
                                Box::new(res_expr.clone()),
                                Box::new(aux_res_expr.clone()),
                            );
                            let final_relation_constraint = AirExpression::Sub(
                                Box::new(sum_res_aux),
                                Box::new(AirExpression::Constant(1)),
                            );
                            air_constraints.push(final_relation_constraint);
                            println!(
                                "  {:?}: Final relation constraint (res + aux_res - 1 = 0) generated.",
                                cond
                            );
                        }
                        LangIntPredicate::SLT => {
                            let op1_air_orig = lang_operand_to_air_expression(operand1);
                            let op2_air_orig = lang_operand_to_air_expression(operand2);

                            println!(
                                "ICMP SLT: op_bitwidth = {}, op1={:?}, op2={:?}, res={:?}",
                                operand_bitwidth, op1_air_orig, op2_air_orig, res_expr
                            );

                            let mut op1_bit_vars_exprs = Vec::new();
                            let mut op1_sum_terms = Vec::new();
                            println!(
                                "  SLT: Decomposing op1 ({:?}) into {} bits",
                                op1_air_orig, operand_bitwidth
                            );
                            for i in 0..operand_bitwidth {
                                let bit_aux_var = self.ctx.new_aux_variable();
                                let bit_expr =
                                    AirExpression::Trace(bit_aux_var, RowOffset::Current);

                                let bit_minus_one = AirExpression::Sub(
                                    Box::new(bit_expr.clone()),
                                    Box::new(AirExpression::Constant(1)),
                                );
                                air_constraints.push(AirExpression::Mul(
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
                                .reduce(|acc, term| {
                                    AirExpression::Add(Box::new(acc), Box::new(term))
                                })
                                .unwrap_or_else(|| AirExpression::Constant(0));
                            air_constraints.push(AirExpression::Sub(
                                Box::new(op1_air_orig.clone()),
                                Box::new(op1_sum_from_bits),
                            ));
                            println!("  SLT: op1 decomposition constraint added.");

                            let mut op2_bit_vars_exprs = Vec::new();
                            let mut op2_sum_terms = Vec::new();
                            println!(
                                "  SLT: Decomposing op2 ({:?}) into {} bits",
                                op2_air_orig, operand_bitwidth
                            );
                            for i in 0..operand_bitwidth {
                                let bit_aux_var = self.ctx.new_aux_variable();
                                let bit_expr =
                                    AirExpression::Trace(bit_aux_var, RowOffset::Current);

                                let bit_minus_one = AirExpression::Sub(
                                    Box::new(bit_expr.clone()),
                                    Box::new(AirExpression::Constant(1)),
                                );
                                air_constraints.push(AirExpression::Mul(
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
                                .reduce(|acc, term| {
                                    AirExpression::Add(Box::new(acc), Box::new(term))
                                })
                                .unwrap_or_else(|| AirExpression::Constant(0));
                            air_constraints.push(AirExpression::Sub(
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

                            let ult_ab_aux_res_var = self.ctx.new_aux_variable();
                            let ult_ab_res_expr =
                                AirExpression::Trace(ult_ab_aux_res_var, RowOffset::Current);
                            println!(
                                "  SLT: ult_ab_aux_res_var (for ULT(op1,op2)) is {:?}",
                                ult_ab_aux_res_var
                            );

                            air_constraints.push(AirExpression::Mul(
                                Box::new(ult_ab_res_expr.clone()),
                                Box::new(AirExpression::Sub(
                                    Box::new(ult_ab_res_expr.clone()),
                                    Box::new(AirExpression::Constant(1)),
                                )),
                            ));

                            let mut ult_intern_bit_vars = Vec::new();
                            for i_ult in 0..operand_bitwidth {
                                let ult_bit_aux = self.ctx.new_aux_variable();
                                let ult_bit_expr =
                                    AirExpression::Trace(ult_bit_aux, RowOffset::Current);
                                air_constraints.push(AirExpression::Mul(
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
                            air_constraints.push(AirExpression::Mul(
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
                            air_constraints.push(AirExpression::Mul(
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

                            let b_is_pos_aux_var = self.ctx.new_aux_variable();
                            let b_is_pos_expr =
                                AirExpression::Trace(b_is_pos_aux_var, RowOffset::Current);
                            air_constraints.push(AirExpression::Mul(
                                Box::new(b_is_pos_expr.clone()),
                                Box::new(AirExpression::Sub(
                                    Box::new(b_is_pos_expr.clone()),
                                    Box::new(AirExpression::Constant(1)),
                                )),
                            ));
                            air_constraints.push(AirExpression::Sub(
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

                            let cond1_aux_var = self.ctx.new_aux_variable();
                            let cond1_expr =
                                AirExpression::Trace(cond1_aux_var, RowOffset::Current);
                            air_constraints.push(AirExpression::Mul(
                                Box::new(cond1_expr.clone()),
                                Box::new(AirExpression::Sub(
                                    Box::new(cond1_expr.clone()),
                                    Box::new(AirExpression::Constant(1)),
                                )),
                            ));
                            air_constraints.push(AirExpression::Sub(
                                Box::new(cond1_expr.clone()),
                                Box::new(AirExpression::Mul(
                                    Box::new(a_msb_expr.clone()),
                                    Box::new(b_is_pos_expr.clone()),
                                )),
                            ));
                            println!("  SLT: cond1_expr (trace col {}) created.", cond1_aux_var.0);

                            let signs_eq_aux_var = self.ctx.new_aux_variable();
                            let signs_eq_expr =
                                AirExpression::Trace(signs_eq_aux_var, RowOffset::Current);
                            air_constraints.push(AirExpression::Mul(
                                Box::new(signs_eq_expr.clone()),
                                Box::new(AirExpression::Sub(
                                    Box::new(signs_eq_expr.clone()),
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
                            air_constraints.push(AirExpression::Sub(
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

                            let cond2_aux_var = self.ctx.new_aux_variable();
                            let cond2_expr =
                                AirExpression::Trace(cond2_aux_var, RowOffset::Current);
                            air_constraints.push(AirExpression::Mul(
                                Box::new(cond2_expr.clone()),
                                Box::new(AirExpression::Sub(
                                    Box::new(cond2_expr.clone()),
                                    Box::new(AirExpression::Constant(1)),
                                )),
                            ));
                            air_constraints.push(AirExpression::Sub(
                                Box::new(cond2_expr.clone()),
                                Box::new(AirExpression::Mul(
                                    Box::new(signs_eq_expr.clone()),
                                    Box::new(ult_ab_res_expr.clone()),
                                )),
                            ));
                            println!("  SLT: cond2_expr (trace col {}) created.", cond2_aux_var.0);

                            let sum_conds = AirExpression::Add(
                                Box::new(cond1_expr.clone()),
                                Box::new(cond2_expr.clone()),
                            );
                            let prod_conds = AirExpression::Mul(
                                Box::new(cond1_expr.clone()),
                                Box::new(cond2_expr.clone()),
                            );
                            let or_expr_val =
                                AirExpression::Sub(Box::new(sum_conds), Box::new(prod_conds));
                            air_constraints.push(AirExpression::Sub(
                                Box::new(res_expr.clone()),
                                Box::new(or_expr_val),
                            ));
                            println!("  SLT: Final OR constraint for result added.");
                        }
                        LangIntPredicate::SGT => {
                            let op1_air_orig = lang_operand_to_air_expression(operand1);
                            let op2_air_orig = lang_operand_to_air_expression(operand2);

                            println!(
                                "ICMP SGT: op_bitwidth = {}, op1={:?}, op2={:?}, res={:?}",
                                operand_bitwidth, op1_air_orig, op2_air_orig, res_expr
                            );

                            let mut slt_a_bit_vars_exprs = Vec::new();
                            let mut slt_a_sum_terms = Vec::new();
                            for i in 0..operand_bitwidth {
                                let bit_aux_var = self.ctx.new_aux_variable();
                                let bit_expr =
                                    AirExpression::Trace(bit_aux_var, RowOffset::Current);
                                air_constraints.push(AirExpression::Mul(
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
                                .reduce(|acc, term| {
                                    AirExpression::Add(Box::new(acc), Box::new(term))
                                })
                                .unwrap_or_else(|| AirExpression::Constant(0));
                            air_constraints.push(AirExpression::Sub(
                                Box::new(op2_air_orig.clone()),
                                Box::new(slt_a_sum_from_bits),
                            ));

                            let mut slt_b_bit_vars_exprs = Vec::new();
                            let mut slt_b_sum_terms = Vec::new();
                            for i in 0..operand_bitwidth {
                                let bit_aux_var = self.ctx.new_aux_variable();
                                let bit_expr =
                                    AirExpression::Trace(bit_aux_var, RowOffset::Current);
                                air_constraints.push(AirExpression::Mul(
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
                                .reduce(|acc, term| {
                                    AirExpression::Add(Box::new(acc), Box::new(term))
                                })
                                .unwrap_or_else(|| AirExpression::Constant(0));
                            air_constraints.push(AirExpression::Sub(
                                Box::new(op1_air_orig.clone()),
                                Box::new(slt_b_sum_from_bits),
                            ));

                            let slt_a_msb_expr = slt_a_bit_vars_exprs.last().unwrap().clone();
                            let slt_b_msb_expr = slt_b_bit_vars_exprs.last().unwrap().clone();

                            let ult_slt_ab_aux_res_var = self.ctx.new_aux_variable();
                            let ult_slt_ab_res_expr =
                                AirExpression::Trace(ult_slt_ab_aux_res_var, RowOffset::Current);
                            air_constraints.push(AirExpression::Mul(
                                Box::new(ult_slt_ab_res_expr.clone()),
                                Box::new(AirExpression::Sub(
                                    Box::new(ult_slt_ab_res_expr.clone()),
                                    Box::new(AirExpression::Constant(1)),
                                )),
                            ));

                            let mut ult_slt_intern_bit_vars = Vec::new();
                            for _ in 0..operand_bitwidth {
                                let bit_aux = self.ctx.new_aux_variable();
                                ult_slt_intern_bit_vars
                                    .push(AirExpression::Trace(bit_aux, RowOffset::Current));
                                air_constraints.push(AirExpression::Mul(
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
                            air_constraints.push(AirExpression::Mul(
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
                            air_constraints.push(AirExpression::Mul(
                                Box::new(AirExpression::Sub(
                                    Box::new(AirExpression::Constant(1)),
                                    Box::new(ult_slt_ab_res_expr.clone()),
                                )),
                                Box::new(AirExpression::Sub(
                                    Box::new(a_ult_minus_b_ult),
                                    Box::new(ult_slt_d_sum.clone()),
                                )),
                            ));

                            let slt_b_is_pos_aux_var = self.ctx.new_aux_variable();
                            let slt_b_is_pos_expr =
                                AirExpression::Trace(slt_b_is_pos_aux_var, RowOffset::Current);
                            air_constraints.push(AirExpression::Mul(
                                Box::new(slt_b_is_pos_expr.clone()),
                                Box::new(AirExpression::Sub(
                                    Box::new(slt_b_is_pos_expr.clone()),
                                    Box::new(AirExpression::Constant(1)),
                                )),
                            ));
                            air_constraints.push(AirExpression::Sub(
                                Box::new(slt_b_is_pos_expr.clone()),
                                Box::new(AirExpression::Sub(
                                    Box::new(AirExpression::Constant(1)),
                                    Box::new(slt_b_msb_expr.clone()),
                                )),
                            ));

                            let slt_cond1_aux_var = self.ctx.new_aux_variable();
                            let slt_cond1_expr =
                                AirExpression::Trace(slt_cond1_aux_var, RowOffset::Current);
                            air_constraints.push(AirExpression::Mul(
                                Box::new(slt_cond1_expr.clone()),
                                Box::new(AirExpression::Sub(
                                    Box::new(slt_cond1_expr.clone()),
                                    Box::new(AirExpression::Constant(1)),
                                )),
                            ));
                            air_constraints.push(AirExpression::Sub(
                                Box::new(slt_cond1_expr.clone()),
                                Box::new(AirExpression::Mul(
                                    Box::new(slt_a_msb_expr.clone()),
                                    Box::new(slt_b_is_pos_expr.clone()),
                                )),
                            ));

                            let slt_signs_eq_aux_var = self.ctx.new_aux_variable();
                            let slt_signs_eq_expr =
                                AirExpression::Trace(slt_signs_eq_aux_var, RowOffset::Current);
                            air_constraints.push(AirExpression::Mul(
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
                            air_constraints.push(AirExpression::Sub(
                                Box::new(slt_signs_eq_expr.clone()),
                                Box::new(AirExpression::Add(
                                    Box::new(slt_term_ab),
                                    Box::new(slt_term_not_a_not_b),
                                )),
                            ));

                            let slt_cond2_aux_var = self.ctx.new_aux_variable();
                            let slt_cond2_expr =
                                AirExpression::Trace(slt_cond2_aux_var, RowOffset::Current);
                            air_constraints.push(AirExpression::Mul(
                                Box::new(slt_cond2_expr.clone()),
                                Box::new(AirExpression::Sub(
                                    Box::new(slt_cond2_expr.clone()),
                                    Box::new(AirExpression::Constant(1)),
                                )),
                            ));
                            air_constraints.push(AirExpression::Sub(
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
                            let slt_or_expr_val = AirExpression::Sub(
                                Box::new(slt_sum_conds),
                                Box::new(slt_prod_conds),
                            );

                            air_constraints.push(AirExpression::Sub(
                                Box::new(res_expr.clone()),
                                Box::new(slt_or_expr_val),
                            ));
                            println!(
                                "  SGT: Logic for SLT(op2,op1) generated, result mapped to SGT's res_expr."
                            );
                        }
                        LangIntPredicate::SGE => {
                            let op1_air_orig = lang_operand_to_air_expression(operand1);
                            let op2_air_orig = lang_operand_to_air_expression(operand2);

                            println!(
                                "ICMP SGE: op_bitwidth = {}, op1={:?}, op2={:?}, res={:?}",
                                operand_bitwidth, op1_air_orig, op2_air_orig, res_expr
                            );

                            let slt_aux_res_var = self.ctx.new_aux_variable();
                            let slt_aux_res_expr =
                                AirExpression::Trace(slt_aux_res_var, RowOffset::Current);
                            air_constraints.push(AirExpression::Mul(
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
                            for i in 0..operand_bitwidth {
                                let bit_aux_var = self.ctx.new_aux_variable();
                                let bit_expr =
                                    AirExpression::Trace(bit_aux_var, RowOffset::Current);
                                air_constraints.push(AirExpression::Mul(
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
                                .reduce(|acc, term| {
                                    AirExpression::Add(Box::new(acc), Box::new(term))
                                })
                                .unwrap_or_else(|| AirExpression::Constant(0));
                            air_constraints.push(AirExpression::Sub(
                                Box::new(op1_air_orig.clone()),
                                Box::new(slt_a_sum_from_bits),
                            ));

                            let mut slt_b_bit_vars_exprs = Vec::new();
                            let mut slt_b_sum_terms = Vec::new();
                            for i in 0..operand_bitwidth {
                                let bit_aux_var = self.ctx.new_aux_variable();
                                let bit_expr =
                                    AirExpression::Trace(bit_aux_var, RowOffset::Current);
                                air_constraints.push(AirExpression::Mul(
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
                                .reduce(|acc, term| {
                                    AirExpression::Add(Box::new(acc), Box::new(term))
                                })
                                .unwrap_or_else(|| AirExpression::Constant(0));
                            air_constraints.push(AirExpression::Sub(
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

                            let ult_ab_aux_res_var = self.ctx.new_aux_variable();
                            let ult_ab_res_expr =
                                AirExpression::Trace(ult_ab_aux_res_var, RowOffset::Current);
                            air_constraints.push(AirExpression::Mul(
                                Box::new(ult_ab_res_expr.clone()),
                                Box::new(AirExpression::Sub(
                                    Box::new(ult_ab_res_expr.clone()),
                                    Box::new(AirExpression::Constant(1)),
                                )),
                            ));
                            let mut ult_intern_bit_vars = Vec::new();
                            for _ in 0..operand_bitwidth {
                                let bit_aux = self.ctx.new_aux_variable();
                                let current_bit_expr =
                                    AirExpression::Trace(bit_aux, RowOffset::Current);
                                air_constraints.push(AirExpression::Mul(
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
                            air_constraints.push(AirExpression::Mul(
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
                            air_constraints.push(AirExpression::Mul(
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
                                let aux_var = self.ctx.new_aux_variable();
                                let expr = AirExpression::Trace(aux_var, RowOffset::Current);
                                air_constraints.push(AirExpression::Mul(
                                    Box::new(expr.clone()),
                                    Box::new(AirExpression::Sub(
                                        Box::new(expr.clone()),
                                        Box::new(AirExpression::Constant(1)),
                                    )),
                                ));
                                air_constraints.push(AirExpression::Sub(
                                    Box::new(expr.clone()),
                                    Box::new(AirExpression::Sub(
                                        Box::new(AirExpression::Constant(1)),
                                        Box::new(b_msb_expr.clone()),
                                    )),
                                ));
                                expr
                            };
                            let cond1_expr_slt = {
                                let aux_var = self.ctx.new_aux_variable();
                                let expr = AirExpression::Trace(aux_var, RowOffset::Current);
                                air_constraints.push(AirExpression::Mul(
                                    Box::new(expr.clone()),
                                    Box::new(AirExpression::Sub(
                                        Box::new(expr.clone()),
                                        Box::new(AirExpression::Constant(1)),
                                    )),
                                ));
                                air_constraints.push(AirExpression::Sub(
                                    Box::new(expr.clone()),
                                    Box::new(AirExpression::Mul(
                                        Box::new(a_msb_expr.clone()),
                                        Box::new(b_is_pos_expr_slt.clone()),
                                    )),
                                ));
                                expr
                            };
                            let signs_eq_expr_slt = {
                                let aux_var = self.ctx.new_aux_variable();
                                let expr = AirExpression::Trace(aux_var, RowOffset::Current);
                                air_constraints.push(AirExpression::Mul(
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
                                air_constraints.push(AirExpression::Sub(
                                    Box::new(expr.clone()),
                                    Box::new(AirExpression::Add(
                                        Box::new(term_ab),
                                        Box::new(term_not_a_not_b),
                                    )),
                                ));
                                expr
                            };
                            let cond2_expr_slt = {
                                let aux_var = self.ctx.new_aux_variable();
                                let expr = AirExpression::Trace(aux_var, RowOffset::Current);
                                air_constraints.push(AirExpression::Mul(
                                    Box::new(expr.clone()),
                                    Box::new(AirExpression::Sub(
                                        Box::new(expr.clone()),
                                        Box::new(AirExpression::Constant(1)),
                                    )),
                                ));
                                air_constraints.push(AirExpression::Sub(
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
                            let or_expr_val_slt = AirExpression::Sub(
                                Box::new(sum_conds_slt),
                                Box::new(prod_conds_slt),
                            );
                            air_constraints.push(AirExpression::Sub(
                                Box::new(slt_aux_res_expr.clone()),
                                Box::new(or_expr_val_slt),
                            ));

                            air_constraints.push(AirExpression::Sub(
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
                        LangIntPredicate::SLE => {
                            let op1_air_orig = lang_operand_to_air_expression(operand1);
                            let op2_air_orig = lang_operand_to_air_expression(operand2);

                            println!(
                                "ICMP SLE: op_bitwidth = {}, op1={:?}, op2={:?}, res={:?}",
                                operand_bitwidth, op1_air_orig, op2_air_orig, res_expr
                            );

                            let sgt_aux_res_var = self.ctx.new_aux_variable();
                            let sgt_aux_res_expr =
                                AirExpression::Trace(sgt_aux_res_var, RowOffset::Current);
                            air_constraints.push(AirExpression::Mul(
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
                            for i in 0..operand_bitwidth {
                                let bit_aux_var = self.ctx.new_aux_variable();
                                let bit_expr =
                                    AirExpression::Trace(bit_aux_var, RowOffset::Current);
                                air_constraints.push(AirExpression::Mul(
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
                                .reduce(|acc, term| {
                                    AirExpression::Add(Box::new(acc), Box::new(term))
                                })
                                .unwrap_or_else(|| AirExpression::Constant(0));
                            air_constraints.push(AirExpression::Sub(
                                Box::new(op2_air_orig.clone()),
                                Box::new(slt_a_sum_from_bits),
                            ));

                            let mut slt_b_bit_vars_exprs = Vec::new();
                            let mut slt_b_sum_terms = Vec::new();
                            for i in 0..operand_bitwidth {
                                let bit_aux_var = self.ctx.new_aux_variable();
                                let bit_expr =
                                    AirExpression::Trace(bit_aux_var, RowOffset::Current);
                                air_constraints.push(AirExpression::Mul(
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
                                .reduce(|acc, term| {
                                    AirExpression::Add(Box::new(acc), Box::new(term))
                                })
                                .unwrap_or_else(|| AirExpression::Constant(0));
                            air_constraints.push(AirExpression::Sub(
                                Box::new(op1_air_orig.clone()),
                                Box::new(slt_b_sum_from_bits),
                            ));

                            let a_msb_expr_for_slt_op2_op1 = slt_a_bit_vars_exprs
                                .last()
                                .expect(
                                    "slt_a_bit_vars_exprs should not be empty for SLE->SGT->SLT",
                                )
                                .clone();
                            let b_msb_expr_for_slt_op2_op1 = slt_b_bit_vars_exprs
                                .last()
                                .expect(
                                    "slt_b_bit_vars_exprs should not be empty for SLE->SGT->SLT",
                                )
                                .clone();

                            let ult_for_slt_op2_op1_aux_res_var = self.ctx.new_aux_variable();
                            let ult_for_slt_op2_op1_res_expr = AirExpression::Trace(
                                ult_for_slt_op2_op1_aux_res_var,
                                RowOffset::Current,
                            );
                            air_constraints.push(AirExpression::Mul(
                                Box::new(ult_for_slt_op2_op1_res_expr.clone()),
                                Box::new(AirExpression::Sub(
                                    Box::new(ult_for_slt_op2_op1_res_expr.clone()),
                                    Box::new(AirExpression::Constant(1)),
                                )),
                            ));
                            let mut ult_intern_bits_for_slt_op2_op1 = Vec::new();
                            for _ in 0..operand_bitwidth {
                                let bit_aux = self.ctx.new_aux_variable();
                                let current_bit_expr =
                                    AirExpression::Trace(bit_aux, RowOffset::Current);
                                air_constraints.push(AirExpression::Mul(
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
                            air_constraints.push(AirExpression::Mul(
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
                            air_constraints.push(AirExpression::Mul(
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
                                let aux_var = self.ctx.new_aux_variable();
                                let expr = AirExpression::Trace(aux_var, RowOffset::Current);
                                air_constraints.push(AirExpression::Mul(
                                    Box::new(expr.clone()),
                                    Box::new(AirExpression::Sub(
                                        Box::new(expr.clone()),
                                        Box::new(AirExpression::Constant(1)),
                                    )),
                                ));
                                air_constraints.push(AirExpression::Sub(
                                    Box::new(expr.clone()),
                                    Box::new(AirExpression::Sub(
                                        Box::new(AirExpression::Constant(1)),
                                        Box::new(b_msb_expr_for_slt_op2_op1.clone()),
                                    )),
                                ));
                                expr
                            };
                            let cond1_for_slt_op2_op1 = {
                                let aux_var = self.ctx.new_aux_variable();
                                let expr = AirExpression::Trace(aux_var, RowOffset::Current);
                                air_constraints.push(AirExpression::Mul(
                                    Box::new(expr.clone()),
                                    Box::new(AirExpression::Sub(
                                        Box::new(expr.clone()),
                                        Box::new(AirExpression::Constant(1)),
                                    )),
                                ));
                                air_constraints.push(AirExpression::Sub(
                                    Box::new(expr.clone()),
                                    Box::new(AirExpression::Mul(
                                        Box::new(a_msb_expr_for_slt_op2_op1.clone()),
                                        Box::new(b_is_pos_for_slt_op2_op1.clone()),
                                    )),
                                ));
                                expr
                            };
                            let signs_eq_for_slt_op2_op1 = {
                                let aux_var = self.ctx.new_aux_variable();
                                let expr = AirExpression::Trace(aux_var, RowOffset::Current);
                                air_constraints.push(AirExpression::Mul(
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
                                air_constraints.push(AirExpression::Sub(
                                    Box::new(expr.clone()),
                                    Box::new(AirExpression::Add(
                                        Box::new(term_ab),
                                        Box::new(term_not_a_not_b),
                                    )),
                                ));
                                expr
                            };
                            let cond2_for_slt_op2_op1 = {
                                let aux_var = self.ctx.new_aux_variable();
                                let expr = AirExpression::Trace(aux_var, RowOffset::Current);
                                air_constraints.push(AirExpression::Mul(
                                    Box::new(expr.clone()),
                                    Box::new(AirExpression::Sub(
                                        Box::new(expr.clone()),
                                        Box::new(AirExpression::Constant(1)),
                                    )),
                                ));
                                air_constraints.push(AirExpression::Sub(
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

                            air_constraints.push(AirExpression::Sub(
                                Box::new(sgt_aux_res_expr.clone()),
                                Box::new(or_val_slt_op2_op1),
                            ));

                            air_constraints.push(AirExpression::Sub(
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
                StructuredAirConstraint::Phi {
                    result,
                    incoming_values,
                    block_name: header_block_name,
                } => {
                    let phi_res_air_var = AirTraceVariable(result.0);
                    let phi_res_expr_current =
                        AirExpression::Trace(phi_res_air_var, RowOffset::Current);

                    if incoming_values.len() == 2 {
                        let val1_op = incoming_values[0].0;
                        let pred1_name = &incoming_values[0].1;
                        let val2_op = incoming_values[1].0;
                        let pred2_name = &incoming_values[1].1;

                        if let Some(cond_var_lang) = phi_condition_map
                            .get(&(pred1_name.clone(), pred2_name.clone()))
                            .or_else(|| {
                                phi_condition_map.get(&(pred2_name.clone(), pred1_name.clone()))
                            })
                        {
                            let cond_var = *cond_var_lang;
                            let val_true_op = if pred1_name
                                == phi_condition_map
                                    .get_key_value(&(pred1_name.clone(), pred2_name.clone()))
                                    .map_or(pred2_name, |(k, _)| &k.0)
                            {
                                val1_op
                            } else {
                                val2_op
                            };
                            let val_false_op = if pred1_name
                                == phi_condition_map
                                    .get_key_value(&(pred1_name.clone(), pred2_name.clone()))
                                    .map_or(pred2_name, |(k, _)| &k.0)
                            {
                                val2_op
                            } else {
                                val1_op
                            };

                            let cond_expr = AirExpression::Trace(
                                AirTraceVariable(cond_var.0),
                                RowOffset::Current,
                            );
                            let val_true_expr = lang_operand_to_air_expression(val_true_op);
                            let val_false_expr = lang_operand_to_air_expression(val_false_op);

                            let vt_minus_vf = AirExpression::Sub(
                                Box::new(val_true_expr),
                                Box::new(val_false_expr.clone()),
                            );
                            let c_mult_vt_minus_vf =
                                AirExpression::Mul(Box::new(cond_expr), Box::new(vt_minus_vf));
                            let pr_minus_vf = AirExpression::Sub(
                                Box::new(phi_res_expr_current.clone()),
                                Box::new(val_false_expr),
                            );
                            let final_phi_constraint = AirExpression::Sub(
                                Box::new(pr_minus_vf),
                                Box::new(c_mult_vt_minus_vf),
                            );

                            air_constraints.push(final_phi_constraint.clone());
                            println!(
                                "    PHI (2-input from CondBr): Generated constraint: {:?}",
                                final_phi_constraint
                            );
                        } else {
                            let mut handled_by_other_phi_logic = false;
                            for (val_op, pred_name) in &incoming_values {
                                if pred_name.as_str() == "entry" {
                                    if let Operand::Const(_) = val_op {
                                        let init_val_expr = lang_operand_to_air_expression(*val_op);
                                        let init_constraint = AirExpression::Sub(
                                            Box::new(phi_res_expr_current.clone()),
                                            Box::new(init_val_expr),
                                        );
                                        air_constraints.push(init_constraint.clone());
                                        println!(
                                            "  PHI Init: Added Current Row constraint for {:?}: {:?} from block '{}' = 0",
                                            phi_res_air_var, phi_res_expr_current, pred_name
                                        );
                                        handled_by_other_phi_logic = true;
                                        break;
                                    }
                                }
                            }

                            if !handled_by_other_phi_logic {
                                println!(
                                    "WARN: PHI (2-input) not from CondBr/Switch/EntryInit: Var {:?} in {}, preds: {} (val {:?}), {} (val {:?}). Map: {:?}",
                                    result,
                                    header_block_name,
                                    pred1_name,
                                    val1_op,
                                    pred2_name,
                                    val2_op,
                                    phi_condition_map
                                );
                            }
                        }
                    } else if !incoming_values.is_empty() {
                        let mut found_controlling_switch = false;
                        for sw_instr_variant in switch_instructions {
                            if let StructuredAirConstraint::Switch {
                                condition_operand: switch_cond_lang_op,
                                default_target_block_name: switch_default_name,
                                cases: switch_cases,
                                ..
                            } = sw_instr_variant
                            {
                                let mut relevant_to_phi = true;
                                for (_phi_op, phi_pred_name) in &incoming_values {
                                    if !(phi_pred_name.as_str() == switch_default_name.as_str()
                                        || switch_cases.iter().any(|(_, case_target)| {
                                            case_target.as_str() == phi_pred_name.as_str()
                                        }))
                                    {
                                        relevant_to_phi = false;
                                        break;
                                    }
                                }
                                if !relevant_to_phi {
                                    continue;
                                }
                                found_controlling_switch = true;
                                println!(
                                    "  PHI (multi-input): Found potentially controlling Switch: cond {:?}, default {}, cases {:?}",
                                    switch_cond_lang_op, switch_default_name, switch_cases
                                );

                                let switch_cond_expr =
                                    lang_operand_to_air_expression(*switch_cond_lang_op);

                                let mut case_selector_exprs = Vec::new();
                                let mut sum_of_is_case_k_terms_for_default_check: Option<
                                    Box<AirExpression>,
                                > = None;

                                for (case_val_lang_op, case_target_name) in switch_cases {
                                    let case_val_expr =
                                        lang_operand_to_air_expression(*case_val_lang_op);

                                    let is_this_case_aux_var = self.ctx.new_aux_variable();
                                    let is_this_case_expr = AirExpression::Trace(
                                        is_this_case_aux_var,
                                        RowOffset::Current,
                                    );

                                    air_constraints.push(AirExpression::Mul(
                                        Box::new(is_this_case_expr.clone()),
                                        Box::new(AirExpression::Sub(
                                            Box::new(is_this_case_expr.clone()),
                                            Box::new(AirExpression::Constant(1)),
                                        )),
                                    ));

                                    let diff_cond_case = AirExpression::Sub(
                                        Box::new(switch_cond_expr.clone()),
                                        Box::new(case_val_expr.clone()),
                                    );
                                    air_constraints.push(AirExpression::Mul(
                                        Box::new(diff_cond_case),
                                        Box::new(is_this_case_expr.clone()),
                                    ));

                                    let phi_op_for_this_case = incoming_values.iter().find(|(_, pred_name)| pred_name.as_str() == case_target_name.as_str())
                                        .map(|(op, _)| lang_operand_to_air_expression(*op))
                                        .expect(&format!("PHI from Switch: Could not find PHI incoming value for case target {}", case_target_name));

                                    case_selector_exprs
                                        .push((is_this_case_expr.clone(), phi_op_for_this_case));

                                    sum_of_is_case_k_terms_for_default_check =
                                        Some(match sum_of_is_case_k_terms_for_default_check {
                                            Some(current_sum) => Box::new(AirExpression::Add(
                                                current_sum,
                                                Box::new(is_this_case_expr.clone()),
                                            )),
                                            None => Box::new(is_this_case_expr.clone()),
                                        });
                                }

                                let is_default_aux_var = self.ctx.new_aux_variable();
                                let is_default_expr =
                                    AirExpression::Trace(is_default_aux_var, RowOffset::Current);
                                air_constraints.push(AirExpression::Mul(
                                    Box::new(is_default_expr.clone()),
                                    Box::new(AirExpression::Sub(
                                        Box::new(is_default_expr.clone()),
                                        Box::new(AirExpression::Constant(1)),
                                    )),
                                ));

                                let sum_is_cases = sum_of_is_case_k_terms_for_default_check
                                    .unwrap_or_else(|| Box::new(AirExpression::Constant(0)));
                                air_constraints.push(AirExpression::Sub(
                                    Box::new(AirExpression::Add(
                                        Box::new(is_default_expr.clone()),
                                        sum_is_cases,
                                    )),
                                    Box::new(AirExpression::Constant(1)),
                                ));

                                let phi_op_for_default = incoming_values.iter().find(|(_, pred_name)| pred_name.as_str() == switch_default_name.as_str())
                                    .map(|(op, _)| lang_operand_to_air_expression(*op))
                                    .expect(&format!("PHI from Switch: Could not find PHI incoming value for default target {}", switch_default_name));

                                let mut selected_value_sum: Option<Box<AirExpression>> = None;
                                for (is_case_expr, phi_val_expr) in case_selector_exprs {
                                    let term = AirExpression::Mul(
                                        Box::new(is_case_expr),
                                        Box::new(phi_val_expr),
                                    );
                                    selected_value_sum = Some(match selected_value_sum {
                                        Some(current_sum) => Box::new(AirExpression::Add(
                                            current_sum,
                                            Box::new(term),
                                        )),
                                        None => Box::new(term),
                                    });
                                }
                                let default_term = AirExpression::Mul(
                                    Box::new(is_default_expr),
                                    Box::new(phi_op_for_default),
                                );
                                selected_value_sum = Some(match selected_value_sum {
                                    Some(current_sum) => Box::new(AirExpression::Add(
                                        current_sum,
                                        Box::new(default_term),
                                    )),
                                    None => Box::new(default_term),
                                });

                                let final_sum_expr = selected_value_sum.expect(
                                    "Should have at least a default term for PHI from switch",
                                );
                                let phi_switch_constraint = AirExpression::Sub(
                                    Box::new(phi_res_expr_current.clone()),
                                    final_sum_expr,
                                );
                                air_constraints.push(phi_switch_constraint.clone());
                                println!(
                                    "    PHI (from Switch): Generated constraint: {:?}",
                                    phi_switch_constraint
                                );

                                break;
                            }
                        }
                        if !found_controlling_switch {
                            println!(
                                "WARN: PHI ({} inputs): Could not find controlling Switch instruction. PHI result {:?}, incoming_values: {:?}. Skipping.",
                                incoming_values.len(),
                                result,
                                incoming_values
                            );
                        }
                    } else {
                        println!(
                            "WARN: PHI: Node with 0 incoming values found for result {:?}. Skipping.",
                            result
                        );
                    }
                }
                StructuredAirConstraint::Return { .. } => { /* Translation handled if needed, or just ignored */
                }
                StructuredAirConstraint::Alloca { .. } => { /* No direct AIR constraint, memory handled abstractly */
                }
                StructuredAirConstraint::Branch { .. } => { /* No direct constraint, affects control flow only */
                }
                StructuredAirConstraint::ConditionalBranch { .. } => { /* No direct constraint, affects control flow only */
                }
                StructuredAirConstraint::Switch { .. } => { /* No direct constraint, affects control flow only */
                }
                StructuredAirConstraint::URem {
                    operand1: dividend_op,
                    operand2: divisor_op,
                    result: remainder_var,
                    block_name: _,
                    operand_bitwidth,
                } => {
                    let a_expr = lang_operand_to_air_expression(dividend_op);
                    let b_expr = lang_operand_to_air_expression(divisor_op);
                    let r_expr =
                        AirExpression::Trace(AirTraceVariable(remainder_var.0), RowOffset::Current);

                    let q_aux_var = self.ctx.new_aux_variable();
                    let q_expr = AirExpression::Trace(q_aux_var, RowOffset::Current);
                    println!(
                        "  UREM: dividend(a)={:?}, divisor(b)={:?}, remainder(r)={:?}, quotient_aux(q)={:?} (bitwidth {})",
                        dividend_op, divisor_op, remainder_var, q_aux_var, operand_bitwidth
                    );

                    self.ctx
                        .add_unsigned_range_proof_constraints(a_expr.clone(), operand_bitwidth);
                    self.ctx
                        .add_unsigned_range_proof_constraints(b_expr.clone(), operand_bitwidth);
                    self.ctx
                        .add_unsigned_range_proof_constraints(q_expr.clone(), operand_bitwidth);
                    self.ctx
                        .add_unsigned_range_proof_constraints(r_expr.clone(), operand_bitwidth);

                    let q_times_b =
                        AirExpression::Mul(Box::new(q_expr.clone()), Box::new(b_expr.clone()));
                    let qb_plus_r =
                        AirExpression::Add(Box::new(q_times_b), Box::new(r_expr.clone()));
                    air_constraints.push(AirExpression::Sub(
                        Box::new(a_expr.clone()),
                        Box::new(qb_plus_r),
                    ));
                    println!("    UREM: Constraint a-(q*b+r)=0 added.");

                    let ult_res_r_lt_b_var = self.ctx.new_aux_variable();
                    let ult_res_r_lt_b_expr =
                        AirExpression::Trace(ult_res_r_lt_b_var, RowOffset::Current);
                    println!(
                        "    UREM: ult_res_r_lt_b_var for (r < b) is {:?}",
                        ult_res_r_lt_b_var
                    );

                    let ult_res_minus_one = AirExpression::Sub(
                        Box::new(ult_res_r_lt_b_expr.clone()),
                        Box::new(AirExpression::Constant(1)),
                    );
                    air_constraints.push(AirExpression::Mul(
                        Box::new(ult_res_r_lt_b_expr.clone()),
                        Box::new(ult_res_minus_one),
                    ));
                    air_constraints.push(AirExpression::Sub(
                        Box::new(ult_res_r_lt_b_expr.clone()),
                        Box::new(AirExpression::Constant(1)),
                    ));
                    println!(
                        "    UREM: Booleanity and assertion (must be 1) for ult_res_r_lt_b added."
                    );

                    let mut ult_bit_vars_air_exprs = Vec::new();
                    for _ in 0..operand_bitwidth {
                        let bit_aux_var = self.ctx.new_aux_variable();
                        let bit_expr_d = AirExpression::Trace(bit_aux_var, RowOffset::Current);
                        let bit_minus_one_d = AirExpression::Sub(
                            Box::new(bit_expr_d.clone()),
                            Box::new(AirExpression::Constant(1)),
                        );
                        air_constraints.push(AirExpression::Mul(
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
                            Some(current_sum) => {
                                Box::new(AirExpression::Add(current_sum, Box::new(term)))
                            }
                            None => Box::new(term),
                        });
                    }
                    let d_sum_air_ult =
                        d_sum_air_ult.unwrap_or_else(|| Box::new(AirExpression::Constant(0)));

                    let b_minus_r_minus_1 = AirExpression::Sub(
                        Box::new(AirExpression::Sub(
                            Box::new(b_expr.clone()),
                            Box::new(r_expr.clone()),
                        )),
                        Box::new(AirExpression::Constant(1)),
                    );
                    let term1_val_ult =
                        AirExpression::Sub(Box::new(b_minus_r_minus_1), d_sum_air_ult.clone());
                    air_constraints.push(AirExpression::Mul(
                        Box::new(ult_res_r_lt_b_expr.clone()),
                        Box::new(term1_val_ult),
                    ));

                    let one_minus_ult_res = AirExpression::Sub(
                        Box::new(AirExpression::Constant(1)),
                        Box::new(ult_res_r_lt_b_expr.clone()),
                    );
                    let r_minus_b =
                        AirExpression::Sub(Box::new(r_expr.clone()), Box::new(b_expr.clone()));
                    let term2_val_ult =
                        AirExpression::Sub(Box::new(r_minus_b), d_sum_air_ult.clone());
                    air_constraints.push(AirExpression::Mul(
                        Box::new(one_minus_ult_res),
                        Box::new(term2_val_ult),
                    ));
                    println!("    UREM: ULT(r,b) selectors added.");
                }
                StructuredAirConstraint::SRem {
                    operand1: dividend_op,
                    operand2: divisor_op,
                    result: remainder_var,
                    block_name: _,
                    operand_bitwidth,
                } => {
                    let a_expr = lang_operand_to_air_expression(dividend_op);
                    let b_expr = lang_operand_to_air_expression(divisor_op);
                    let r_expr =
                        AirExpression::Trace(AirTraceVariable(remainder_var.0), RowOffset::Current);

                    let q_aux_var = self.ctx.new_aux_variable();
                    let q_expr = AirExpression::Trace(q_aux_var, RowOffset::Current);
                    println!(
                        "  SREM: dividend(a)={:?}, divisor(b)={:?}, remainder(r)={:?}, quotient_aux(q)={:?} (bitwidth {})",
                        dividend_op, divisor_op, remainder_var, q_aux_var, operand_bitwidth
                    );

                    let (_a_bits, a_msb_expr_opt) = generate_signed_range_proof_constraints(
                        &a_expr,
                        operand_bitwidth,
                        &mut self.ctx,
                        &mut air_constraints,
                        "srem_a",
                    );
                    let (_b_bits, b_msb_expr_opt) = generate_signed_range_proof_constraints(
                        &b_expr,
                        operand_bitwidth,
                        &mut self.ctx,
                        &mut air_constraints,
                        "srem_b",
                    );
                    let (_q_bits, _q_msb_expr_opt) = generate_signed_range_proof_constraints(
                        &q_expr,
                        operand_bitwidth,
                        &mut self.ctx,
                        &mut air_constraints,
                        "srem_q_aux",
                    );
                    let (_r_bits, r_msb_expr_opt) = generate_signed_range_proof_constraints(
                        &r_expr,
                        operand_bitwidth,
                        &mut self.ctx,
                        &mut air_constraints,
                        "srem_r",
                    );

                    let q_times_b =
                        AirExpression::Mul(Box::new(q_expr.clone()), Box::new(b_expr.clone()));
                    let qb_plus_r =
                        AirExpression::Add(Box::new(q_times_b), Box::new(r_expr.clone()));
                    air_constraints.push(AirExpression::Sub(
                        Box::new(a_expr.clone()),
                        Box::new(qb_plus_r),
                    ));
                    println!("    SREM: Constraint a-(q*b+r)=0 added.");

                    let is_a_zero_aux = self.ctx.new_aux_variable();
                    let is_a_zero_expr = AirExpression::Trace(is_a_zero_aux, RowOffset::Current);
                    air_constraints.push(AirExpression::Mul(
                        Box::new(is_a_zero_expr.clone()),
                        Box::new(AirExpression::Sub(
                            Box::new(is_a_zero_expr.clone()),
                            Box::new(AirExpression::Constant(1)),
                        )),
                    ));
                    air_constraints.push(AirExpression::Mul(
                        Box::new(is_a_zero_expr.clone()),
                        Box::new(a_expr.clone()),
                    ));

                    if let (Some(a_msb_expr_val), Some(r_msb_expr_val)) =
                        (a_msb_expr_opt.as_ref(), r_msb_expr_opt.as_ref())
                    {
                        let one_minus_is_a_zero = AirExpression::Sub(
                            Box::new(AirExpression::Constant(1)),
                            Box::new(is_a_zero_expr.clone()),
                        );
                        let a_msb_minus_r_msb = AirExpression::Sub(
                            Box::new(a_msb_expr_val.clone()),
                            Box::new(r_msb_expr_val.clone()),
                        );
                        air_constraints.push(AirExpression::Mul(
                            Box::new(one_minus_is_a_zero),
                            Box::new(a_msb_minus_r_msb),
                        ));
                        air_constraints.push(AirExpression::Mul(
                            Box::new(is_a_zero_expr.clone()),
                            Box::new(r_expr.clone()),
                        ));
                        println!("    SREM: Remainder sign constraints added.");
                    } else {
                        println!(
                            "    SREM: WARN - MSBs for a or r not available for sign constraint."
                        );
                    }

                    if let (Some(r_msb_expr_val_mag), Some(b_msb_expr_val_mag)) =
                        (r_msb_expr_opt.as_ref(), b_msb_expr_opt.as_ref())
                    {
                        let one_const = AirExpression::Constant(1);
                        let two_const = AirExpression::Constant(2);

                        let one_minus_two_r_msb = AirExpression::Sub(
                            Box::new(one_const.clone()),
                            Box::new(AirExpression::Mul(
                                Box::new(two_const.clone()),
                                Box::new(r_msb_expr_val_mag.clone()),
                            )),
                        );
                        let abs_r_expr = AirExpression::Mul(
                            Box::new(r_expr.clone()),
                            Box::new(one_minus_two_r_msb),
                        );

                        let one_minus_two_b_msb = AirExpression::Sub(
                            Box::new(one_const.clone()),
                            Box::new(AirExpression::Mul(
                                Box::new(two_const.clone()),
                                Box::new(b_msb_expr_val_mag.clone()),
                            )),
                        );
                        let abs_b_expr = AirExpression::Mul(
                            Box::new(b_expr.clone()),
                            Box::new(one_minus_two_b_msb),
                        );

                        let ult_res_abs_r_lt_abs_b_var = self.ctx.new_aux_variable();
                        let ult_res_abs_r_lt_abs_b_expr =
                            AirExpression::Trace(ult_res_abs_r_lt_abs_b_var, RowOffset::Current);

                        air_constraints.push(AirExpression::Mul(
                            Box::new(ult_res_abs_r_lt_abs_b_expr.clone()),
                            Box::new(AirExpression::Sub(
                                Box::new(ult_res_abs_r_lt_abs_b_expr.clone()),
                                Box::new(AirExpression::Constant(1)),
                            )),
                        ));
                        air_constraints.push(AirExpression::Sub(
                            Box::new(ult_res_abs_r_lt_abs_b_expr.clone()),
                            Box::new(AirExpression::Constant(1)),
                        ));

                        let mut d_sum_bit_vars_ult_mag = Vec::new();
                        if operand_bitwidth > 0 {
                            for _ in 0..operand_bitwidth {
                                let bit_aux_var = self.ctx.new_aux_variable();
                                let bit_expr_d =
                                    AirExpression::Trace(bit_aux_var, RowOffset::Current);
                                air_constraints.push(AirExpression::Mul(
                                    Box::new(bit_expr_d.clone()),
                                    Box::new(AirExpression::Sub(
                                        Box::new(bit_expr_d.clone()),
                                        Box::new(AirExpression::Constant(1)),
                                    )),
                                ));
                                d_sum_bit_vars_ult_mag.push(bit_expr_d);
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
                        air_constraints.push(ult_final_constraint);
                        println!("    SREM: Remainder magnitude constraints added.");
                    } else {
                        println!(
                            "    SREM: WARN - MSBs for r or b not available for magnitude constraint."
                        );
                    }
                }
                StructuredAirConstraint::Trunc {
                    operand,
                    result,
                    operand_bitwidth,
                    result_bitwidth,
                    block_name: _,
                } => {
                    println!(
                        "  TRUNC: op={:?}, res={:?} ({}->{} bits)",
                        operand, result, operand_bitwidth, result_bitwidth
                    );
                    let op_expr = lang_operand_to_air_expression(operand);
                    let res_expr = AirExpression::Trace(
                        AirTraceVariable(result.0.clone()),
                        RowOffset::Current,
                    );
                    let upper_bits_bitwidth = operand_bitwidth - result_bitwidth;

                    let upper_bits_vars = (0..upper_bits_bitwidth)
                        .map(|_| {
                            let bit_var = self.ctx.new_aux_variable();
                            let bit_expr =
                                AirExpression::Trace(bit_var.clone(), RowOffset::Current);

                            let bit_constraint = AirExpression::Mul(
                                Box::new(bit_expr.clone()),
                                Box::new(AirExpression::Sub(
                                    Box::new(bit_expr),
                                    Box::new(AirExpression::Constant(1)),
                                )),
                            );
                            air_constraints.push(bit_constraint);
                            bit_var
                        })
                        .collect::<Vec<_>>();

                    let mut upper_bits_expr = AirExpression::Constant(0);
                    for (i, bit_var) in upper_bits_vars.iter().enumerate() {
                        let bit_expr = AirExpression::Trace(bit_var.clone(), RowOffset::Current);
                        let bit_shift = AirExpression::Constant(1u128 << i);
                        let bit_term = AirExpression::Mul(Box::new(bit_expr), Box::new(bit_shift));
                        upper_bits_expr =
                            AirExpression::Add(Box::new(upper_bits_expr), Box::new(bit_term));
                    }

                    let upper_bits_shift = AirExpression::Constant(1u128 << result_bitwidth);
                    let upper_bits_term =
                        AirExpression::Mul(Box::new(upper_bits_expr), Box::new(upper_bits_shift));
                    let trunc_expr =
                        AirExpression::Add(Box::new(res_expr), Box::new(upper_bits_term));
                    let final_expr = AirExpression::Sub(Box::new(op_expr), Box::new(trunc_expr));
                    air_constraints.push(final_expr);
                    println!("      TRUNC: Main constraint added.");
                }
                StructuredAirConstraint::FPTrunc {
                    operand,
                    result,
                    operand_bitwidth,
                    result_bitwidth,
                    block_name: _,
                } => {
                    println!(
                        "  FPTRUNC: op={:?}, res={:?} (bitwidth {}) - Setting up S/E/M aux vars.",
                        operand, result, operand_bitwidth
                    );

                    let (s_bit_count, exp_bit_count, mant_bit_count) = match operand_bitwidth {
                        16 => (1u32, 5u32, 10u32),
                        32 => (1u32, 8u32, 23u32),
                        64 => (1u32, 11u32, 52u32),
                        80 => (1u32, 15u32, 63u32),
                        128 => (1u32, 15u32, 112u32),
                        _ => panic!(
                            "Unsupported operand_bitwidth {} for FAdd S/E/M decomposition.",
                            operand_bitwidth
                        ),
                    };

                    let (res_s_bit_count, res_exp_bit_count, res_mant_bit_count) =
                        match result_bitwidth {
                            16 => (1u32, 5u32, 10u32),
                            32 => (1u32, 8u32, 23u32),
                            64 => (1u32, 11u32, 52u32),
                            80 => (1u32, 15u32, 63u32),
                            128 => (1u32, 15u32, 112u32),
                            _ => panic!(
                                "Unsupported result_bitwidth {} for FPTrunc S/E/M decomposition.",
                                result_bitwidth
                            ),
                        };

                    let (op_s_var, op_e_var, op_m_var) = setup_sem_aux_vars(
                        operand,
                        "op",
                        &mut self.ctx,
                        s_bit_count,
                        exp_bit_count,
                        mant_bit_count,
                        &mut air_constraints,
                    );
                    let (res_s_var, res_e_var, res_m_var) = setup_sem_aux_vars(
                        lang::Operand::Var(result),
                        "res",
                        &mut self.ctx,
                        res_s_bit_count,
                        res_exp_bit_count,
                        res_mant_bit_count,
                        &mut air_constraints,
                    );

                    let op_s_expr = AirExpression::Trace(op_s_var, RowOffset::Current);
                    let op_e_expr = AirExpression::Trace(op_e_var, RowOffset::Current);
                    let op_m_expr = AirExpression::Trace(op_m_var, RowOffset::Current);
                    let res_s_expr = AirExpression::Trace(res_s_var, RowOffset::Current);
                    let res_e_expr = AirExpression::Trace(res_e_var, RowOffset::Current);
                    let res_m_expr = AirExpression::Trace(res_m_var, RowOffset::Current);

                    let op_is_nan = fp_is_nan(
                        &op_e_expr,
                        &op_m_expr,
                        exp_bit_count,
                        mant_bit_count,
                        &mut self.ctx,
                        &mut air_constraints,
                        "op_fptrunc_nan",
                    );
                    let op_is_inf = fp_is_inf(
                        &op_e_expr,
                        &op_m_expr,
                        exp_bit_count,
                        mant_bit_count,
                        &mut self.ctx,
                        &mut air_constraints,
                        "op_fptrunc_inf",
                    );
                    let op_is_true_zero = fp_is_true_zero(
                        &op_e_expr,
                        &op_m_expr,
                        exp_bit_count,
                        mant_bit_count,
                        &mut self.ctx,
                        &mut air_constraints,
                        "op_fptrunc_zero",
                    );

                    let res_qnan_sign = AirExpression::Constant(0);
                    let res_qnan_exp = AirExpression::Constant((1u128 << res_exp_bit_count) - 1);
                    let res_qnan_mant = AirExpression::Constant(1u128 << (res_mant_bit_count - 1));

                    let res_inf_sign = op_s_expr.clone();
                    let res_inf_exp = res_qnan_exp.clone();
                    let res_inf_mant = AirExpression::Constant(0);

                    let res_zero_sign = op_s_expr.clone();
                    let res_zero_exp = AirExpression::Constant(0);
                    let res_zero_mant = AirExpression::Constant(0);

                    let op_bias_val = (1u128 << (exp_bit_count - 1)) - 1;
                    let res_bias_val = (1u128 << (res_exp_bit_count - 1)) - 1;

                    let op_is_denormal = fp_is_value_equal(
                        &op_e_expr,
                        &AirExpression::Constant(0),
                        &mut self.ctx,
                        &mut air_constraints,
                        "op_is_denorm_e_check_fptrunc",
                    );
                    let implicit_bit_val_op = fp_logical_not(
                        &op_is_denormal,
                        &mut self.ctx,
                        &mut air_constraints,
                        "op_implicit_bit_fptrunc",
                    );
                    let full_significand_op = fp_add(
                        &op_m_expr,
                        &fp_mul(
                            &implicit_bit_val_op,
                            &AirExpression::Constant(1u128 << mant_bit_count),
                            &mut self.ctx,
                            &mut air_constraints,
                            "op_impl_shifted_fptrunc",
                        ),
                        &mut self.ctx,
                        &mut air_constraints,
                        "full_sig_op_fptrunc",
                    );

                    let effective_exp_op = fp_select(
                        &op_is_denormal,
                        &AirExpression::Constant(1),
                        &op_e_expr,
                        &mut self.ctx,
                        &mut air_constraints,
                        "eff_exp_op_fptrunc",
                    );
                    let unbiased_exp_op = fp_sub(
                        &effective_exp_op,
                        &AirExpression::Constant(op_bias_val),
                        &mut self.ctx,
                        &mut air_constraints,
                        "unbiased_e_op_fptrunc",
                    );
                    let initial_biased_exp_for_norm = fp_add(
                        &unbiased_exp_op,
                        &AirExpression::Constant(res_bias_val),
                        &mut self.ctx,
                        &mut air_constraints,
                        "init_biased_exp_res_fptrunc",
                    );

                    let (gen_case_s_val, gen_case_e_val, gen_case_m_val, _) =
                        fp_normalize_and_round_significand(
                            &full_significand_op,
                            &op_s_expr,
                            &initial_biased_exp_for_norm,
                            &AirExpression::Constant(0),
                            &AirExpression::Constant(0),
                            &AirExpression::Constant(0),
                            res_mant_bit_count,
                            res_exp_bit_count,
                            &mut self.ctx,
                            &mut air_constraints,
                            "fptrunc_norm_round",
                        );

                    let s_if_not_inf = fp_select(
                        &op_is_true_zero,
                        &res_zero_sign,
                        &gen_case_s_val,
                        &mut self.ctx,
                        &mut air_constraints,
                        "s_zero_vs_gen_fptrunc",
                    );
                    let e_if_not_inf = fp_select(
                        &op_is_true_zero,
                        &res_zero_exp,
                        &gen_case_e_val,
                        &mut self.ctx,
                        &mut air_constraints,
                        "e_zero_vs_gen_fptrunc",
                    );
                    let m_if_not_inf = fp_select(
                        &op_is_true_zero,
                        &res_zero_mant,
                        &gen_case_m_val,
                        &mut self.ctx,
                        &mut air_constraints,
                        "m_zero_vs_gen_fptrunc",
                    );

                    let s_if_not_nan = fp_select(
                        &op_is_inf,
                        &res_inf_sign,
                        &s_if_not_inf,
                        &mut self.ctx,
                        &mut air_constraints,
                        "s_inf_vs_else_fptrunc",
                    );
                    let e_if_not_nan = fp_select(
                        &op_is_inf,
                        &res_inf_exp,
                        &e_if_not_inf,
                        &mut self.ctx,
                        &mut air_constraints,
                        "e_inf_vs_else_fptrunc",
                    );
                    let m_if_not_nan = fp_select(
                        &op_is_inf,
                        &res_inf_mant,
                        &m_if_not_inf,
                        &mut self.ctx,
                        &mut air_constraints,
                        "m_inf_vs_else_fptrunc",
                    );

                    let final_res_s_val = fp_select(
                        &op_is_nan,
                        &res_qnan_sign,
                        &s_if_not_nan,
                        &mut self.ctx,
                        &mut air_constraints,
                        "s_nan_vs_else_fptrunc",
                    );
                    let final_res_e_val = fp_select(
                        &op_is_nan,
                        &res_qnan_exp,
                        &e_if_not_nan,
                        &mut self.ctx,
                        &mut air_constraints,
                        "e_nan_vs_else_fptrunc",
                    );
                    let final_res_m_val = fp_select(
                        &op_is_nan,
                        &res_qnan_mant,
                        &m_if_not_nan,
                        &mut self.ctx,
                        &mut air_constraints,
                        "m_nan_vs_else_fptrunc",
                    );

                    air_constraints.push(AirExpression::Sub(
                        Box::new(res_s_expr),
                        Box::new(final_res_s_val),
                    ));
                    air_constraints.push(AirExpression::Sub(
                        Box::new(res_e_expr),
                        Box::new(final_res_e_val),
                    ));
                    air_constraints.push(AirExpression::Sub(
                        Box::new(res_m_expr),
                        Box::new(final_res_m_val),
                    ));
                    println!("      FPTRUNC: Main constraint added.");
                }
                StructuredAirConstraint::FAdd {
                    operand1,
                    operand2,
                    result,
                    operand_bitwidth,
                    block_name: _,
                } => {
                    println!(
                        "  FADD: op1={:?}, op2={:?}, res={:?} (bitwidth {}) - Setting up S/E/M aux vars.",
                        operand1, operand2, result, operand_bitwidth
                    );

                    let (s_bit_count, exp_bit_count, mant_bit_count) = match operand_bitwidth {
                        16 => (1u32, 5u32, 10u32),
                        32 => (1u32, 8u32, 23u32),
                        64 => (1u32, 11u32, 52u32),
                        80 => (1u32, 15u32, 63u32),
                        128 => (1u32, 15u32, 112u32),
                        _ => panic!(
                            "Unsupported operand_bitwidth {} for FAdd S/E/M decomposition.",
                            operand_bitwidth
                        ),
                    };

                    let (op1_s_var, op1_e_var, op1_m_var) = setup_sem_aux_vars(
                        operand1,
                        "op1",
                        &mut self.ctx,
                        s_bit_count,
                        exp_bit_count,
                        mant_bit_count,
                        &mut air_constraints,
                    );
                    let (op2_s_var, op2_e_var, op2_m_var) = setup_sem_aux_vars(
                        operand2,
                        "op2",
                        &mut self.ctx,
                        s_bit_count,
                        exp_bit_count,
                        mant_bit_count,
                        &mut air_constraints,
                    );
                    let (res_s_var, res_e_var, res_m_var) = setup_sem_aux_vars(
                        lang::Operand::Var(result),
                        "res",
                        &mut self.ctx,
                        s_bit_count,
                        exp_bit_count,
                        mant_bit_count,
                        &mut air_constraints,
                    );

                    let op1_s_expr = AirExpression::Trace(op1_s_var, RowOffset::Current);
                    let op1_e_val_expr = AirExpression::Trace(op1_e_var, RowOffset::Current);
                    let op1_m_val_expr = AirExpression::Trace(op1_m_var, RowOffset::Current);

                    let op2_s_expr = AirExpression::Trace(op2_s_var, RowOffset::Current);
                    let op2_e_val_expr = AirExpression::Trace(op2_e_var, RowOffset::Current);
                    let op2_m_val_expr = AirExpression::Trace(op2_m_var, RowOffset::Current);

                    let res_s_expr = AirExpression::Trace(res_s_var, RowOffset::Current);
                    let res_e_val_expr = AirExpression::Trace(res_e_var, RowOffset::Current);
                    let res_m_val_expr = AirExpression::Trace(res_m_var, RowOffset::Current);

                    let op1_is_nan = fp_is_nan(
                        &op1_e_val_expr,
                        &op1_m_val_expr,
                        exp_bit_count,
                        mant_bit_count,
                        &mut self.ctx,
                        &mut air_constraints,
                        "op1",
                    );
                    let op2_is_nan = fp_is_nan(
                        &op2_e_val_expr,
                        &op2_m_val_expr,
                        exp_bit_count,
                        mant_bit_count,
                        &mut self.ctx,
                        &mut air_constraints,
                        "op2",
                    );

                    let op1_is_inf = fp_is_inf(
                        &op1_e_val_expr,
                        &op1_m_val_expr,
                        exp_bit_count,
                        mant_bit_count,
                        &mut self.ctx,
                        &mut air_constraints,
                        "op1",
                    );
                    let op2_is_inf = fp_is_inf(
                        &op2_e_val_expr,
                        &op2_m_val_expr,
                        exp_bit_count,
                        mant_bit_count,
                        &mut self.ctx,
                        &mut air_constraints,
                        "op2",
                    );

                    let op1_is_pos_inf = fp_logical_and(
                        &op1_is_inf,
                        &fp_is_value_zero(
                            &op1_s_expr,
                            &mut self.ctx,
                            &mut air_constraints,
                            "op1_s_is_zero",
                        ),
                        &mut self.ctx,
                        &mut air_constraints,
                        "op1_is_pos_inf",
                    );
                    let op1_is_neg_inf = fp_logical_and(
                        &op1_is_inf,
                        &fp_logical_not(
                            &fp_is_value_zero(
                                &op1_s_expr,
                                &mut self.ctx,
                                &mut air_constraints,
                                "op1_s_is_zero_for_neg",
                            ),
                            &mut self.ctx,
                            &mut air_constraints,
                            "op1_s_is_one",
                        ),
                        &mut self.ctx,
                        &mut air_constraints,
                        "op1_is_neg_inf",
                    );
                    let op2_is_pos_inf = fp_logical_and(
                        &op2_is_inf,
                        &fp_is_value_zero(
                            &op2_s_expr,
                            &mut self.ctx,
                            &mut air_constraints,
                            "op2_s_is_zero",
                        ),
                        &mut self.ctx,
                        &mut air_constraints,
                        "op2_is_pos_inf",
                    );
                    let op2_is_neg_inf = fp_logical_and(
                        &op2_is_inf,
                        &fp_logical_not(
                            &fp_is_value_zero(
                                &op2_s_expr,
                                &mut self.ctx,
                                &mut air_constraints,
                                "op2_s_is_zero_for_neg",
                            ),
                            &mut self.ctx,
                            &mut air_constraints,
                            "op2_s_is_one",
                        ),
                        &mut self.ctx,
                        &mut air_constraints,
                        "op2_is_neg_inf",
                    );

                    let op1_is_true_zero = fp_is_true_zero(
                        &op1_e_val_expr,
                        &op1_m_val_expr,
                        exp_bit_count,
                        mant_bit_count,
                        &mut self.ctx,
                        &mut air_constraints,
                        "op1",
                    );
                    let op2_is_true_zero = fp_is_true_zero(
                        &op2_e_val_expr,
                        &op2_m_val_expr,
                        exp_bit_count,
                        mant_bit_count,
                        &mut self.ctx,
                        &mut air_constraints,
                        "op2",
                    );

                    let qnan_sign = AirExpression::Constant(0);
                    let qnan_exp = AirExpression::Constant((1u128 << exp_bit_count) - 1);
                    let qnan_mant = AirExpression::Constant(1u128 << (mant_bit_count - 1));

                    let res_is_nan_due_to_op_nan = fp_logical_or(
                        &op1_is_nan,
                        &op2_is_nan,
                        &mut self.ctx,
                        &mut air_constraints,
                        "res_is_nan_from_op",
                    );

                    let inf_plus_neg_inf = fp_logical_and(
                        &op1_is_pos_inf,
                        &op2_is_neg_inf,
                        &mut self.ctx,
                        &mut air_constraints,
                        "pInf_nInf",
                    );
                    let neg_inf_plus_pos_inf = fp_logical_and(
                        &op1_is_neg_inf,
                        &op2_is_pos_inf,
                        &mut self.ctx,
                        &mut air_constraints,
                        "nInf_pInf",
                    );
                    let res_is_nan_due_to_inf_cancel = fp_logical_or(
                        &inf_plus_neg_inf,
                        &neg_inf_plus_pos_inf,
                        &mut self.ctx,
                        &mut air_constraints,
                        "res_is_nan_inf_cancel",
                    );

                    let final_res_is_nan = fp_logical_or(
                        &res_is_nan_due_to_op_nan,
                        &res_is_nan_due_to_inf_cancel,
                        &mut self.ctx,
                        &mut air_constraints,
                        "final_res_is_nan",
                    );

                    let general_case_res_s_expr =
                        AirExpression::Trace(self.ctx.new_aux_variable(), RowOffset::Current);
                    let general_case_res_e_expr =
                        AirExpression::Trace(self.ctx.new_aux_variable(), RowOffset::Current);
                    let general_case_res_m_expr =
                        AirExpression::Trace(self.ctx.new_aux_variable(), RowOffset::Current);

                    air_constraints.push(AirExpression::Mul(
                        Box::new(general_case_res_s_expr.clone()),
                        Box::new(AirExpression::Sub(
                            Box::new(general_case_res_s_expr.clone()),
                            Box::new(AirExpression::Constant(1)),
                        )),
                    ));

                    let op1_is_inf_not_nan = fp_logical_and(
                        &op1_is_inf,
                        &fp_logical_not(
                            &op1_is_nan,
                            &mut self.ctx,
                            &mut air_constraints,
                            "op1_not_nan",
                        ),
                        &mut self.ctx,
                        &mut air_constraints,
                        "op1_inf_not_nan",
                    );
                    let op2_is_inf_not_nan = fp_logical_and(
                        &op2_is_inf,
                        &fp_logical_not(
                            &op2_is_nan,
                            &mut self.ctx,
                            &mut air_constraints,
                            "op2_not_nan",
                        ),
                        &mut self.ctx,
                        &mut air_constraints,
                        "op2_inf_not_nan",
                    );
                    let op1_is_fin_not_nan = fp_logical_not(
                        &op1_is_inf_not_nan,
                        &mut self.ctx,
                        &mut air_constraints,
                        "op1_fin_not_nan",
                    );
                    let op2_is_fin_not_nan = fp_logical_not(
                        &op2_is_inf_not_nan,
                        &mut self.ctx,
                        &mut air_constraints,
                        "op2_fin_not_nan",
                    );

                    let inf_plus_finite_res_s = fp_select(
                        &op1_is_inf_not_nan,
                        &op1_s_expr,
                        &op2_s_expr,
                        &mut self.ctx,
                        &mut air_constraints,
                        "inf_fin_s",
                    );

                    let cond_inf_plus_finite = fp_logical_or(
                        &fp_logical_and(
                            &op1_is_inf_not_nan,
                            &op2_is_fin_not_nan,
                            &mut self.ctx,
                            &mut air_constraints,
                            "op1inf_op2fin",
                        ),
                        &fp_logical_and(
                            &op2_is_inf_not_nan,
                            &op1_is_fin_not_nan,
                            &mut self.ctx,
                            &mut air_constraints,
                            "op2inf_op1fin",
                        ),
                        &mut self.ctx,
                        &mut air_constraints,
                        "cond_inf_plus_fin",
                    );

                    let op1_is_pos_inf_not_nan = fp_logical_and(
                        &op1_is_pos_inf,
                        &fp_logical_not(
                            &op1_is_nan,
                            &mut self.ctx,
                            &mut air_constraints,
                            "op1_pos_inf_nn_aux1",
                        ),
                        &mut self.ctx,
                        &mut air_constraints,
                        "op1_pos_inf_nn",
                    );
                    let op2_is_pos_inf_not_nan = fp_logical_and(
                        &op2_is_pos_inf,
                        &fp_logical_not(
                            &op2_is_nan,
                            &mut self.ctx,
                            &mut air_constraints,
                            "op2_pos_inf_nn_aux1",
                        ),
                        &mut self.ctx,
                        &mut air_constraints,
                        "op2_pos_inf_nn",
                    );
                    let op1_is_neg_inf_not_nan = fp_logical_and(
                        &op1_is_neg_inf,
                        &fp_logical_not(
                            &op1_is_nan,
                            &mut self.ctx,
                            &mut air_constraints,
                            "op1_neg_inf_nn_aux1",
                        ),
                        &mut self.ctx,
                        &mut air_constraints,
                        "op1_neg_inf_nn",
                    );
                    let op2_is_neg_inf_not_nan = fp_logical_and(
                        &op2_is_neg_inf,
                        &fp_logical_not(
                            &op2_is_nan,
                            &mut self.ctx,
                            &mut air_constraints,
                            "op2_neg_inf_nn_aux1",
                        ),
                        &mut self.ctx,
                        &mut air_constraints,
                        "op2_neg_inf_nn",
                    );

                    let both_pos_inf = fp_logical_and(
                        &op1_is_pos_inf_not_nan,
                        &op2_is_pos_inf_not_nan,
                        &mut self.ctx,
                        &mut air_constraints,
                        "both_pos_inf",
                    );
                    let both_neg_inf = fp_logical_and(
                        &op1_is_neg_inf_not_nan,
                        &op2_is_neg_inf_not_nan,
                        &mut self.ctx,
                        &mut air_constraints,
                        "both_neg_inf",
                    );
                    let cond_both_inf_same_sign = fp_logical_or(
                        &both_pos_inf,
                        &both_neg_inf,
                        &mut self.ctx,
                        &mut air_constraints,
                        "both_inf_same_sign",
                    );
                    let both_inf_same_sign_res_s = op1_s_expr.clone();

                    let is_inf_result_scenario = fp_logical_or(
                        &cond_inf_plus_finite,
                        &cond_both_inf_same_sign,
                        &mut self.ctx,
                        &mut air_constraints,
                        "is_inf_res_scenario",
                    );
                    let inter_res_s_if_inf = fp_select(
                        &cond_inf_plus_finite,
                        &inf_plus_finite_res_s,
                        &both_inf_same_sign_res_s,
                        &mut self.ctx,
                        &mut air_constraints,
                        "inter_s_if_inf",
                    );
                    let inter_res_e_if_inf = qnan_exp.clone();
                    let inter_res_m_if_inf = AirExpression::Constant(0);

                    let op1_is_zero_not_special = fp_logical_and(
                        &op1_is_true_zero,
                        &fp_logical_not(
                            &op1_is_nan,
                            &mut self.ctx,
                            &mut air_constraints,
                            "op1_not_nan_z",
                        ),
                        &mut self.ctx,
                        &mut air_constraints,
                        "op1_zero_not_nan",
                    );
                    let op1_is_zero_not_special = fp_logical_and(
                        &op1_is_zero_not_special,
                        &fp_logical_not(
                            &op1_is_inf,
                            &mut self.ctx,
                            &mut air_constraints,
                            "op1_not_inf_z",
                        ),
                        &mut self.ctx,
                        &mut air_constraints,
                        "op1_zero_not_spec",
                    );

                    let op2_is_zero_not_special = fp_logical_and(
                        &op2_is_true_zero,
                        &fp_logical_not(
                            &op2_is_nan,
                            &mut self.ctx,
                            &mut air_constraints,
                            "op2_not_nan_z",
                        ),
                        &mut self.ctx,
                        &mut air_constraints,
                        "op2_zero_not_nan",
                    );
                    let op2_is_zero_not_special = fp_logical_and(
                        &op2_is_zero_not_special,
                        &fp_logical_not(
                            &op2_is_inf,
                            &mut self.ctx,
                            &mut air_constraints,
                            "op2_not_inf_z",
                        ),
                        &mut self.ctx,
                        &mut air_constraints,
                        "op2_zero_not_spec",
                    );

                    let cond_op1_zero_op2_fin = fp_logical_and(
                        &op1_is_zero_not_special,
                        &op2_is_fin_not_nan,
                        &mut self.ctx,
                        &mut air_constraints,
                        "op1z_op2fin",
                    );
                    let cond_op2_zero_op1_fin = fp_logical_and(
                        &op2_is_zero_not_special,
                        &op1_is_fin_not_nan,
                        &mut self.ctx,
                        &mut air_constraints,
                        "op2z_op1fin",
                    );

                    let zero_plus_fin_res_s = fp_select(
                        &cond_op1_zero_op2_fin,
                        &op2_s_expr,
                        &op1_s_expr,
                        &mut self.ctx,
                        &mut air_constraints,
                        "zero_fin_s",
                    );
                    let zero_plus_fin_res_e = fp_select(
                        &cond_op1_zero_op2_fin,
                        &op2_e_val_expr,
                        &op1_e_val_expr,
                        &mut self.ctx,
                        &mut air_constraints,
                        "zero_fin_e",
                    );
                    let zero_plus_fin_res_m = fp_select(
                        &cond_op1_zero_op2_fin,
                        &op2_m_val_expr,
                        &op1_m_val_expr,
                        &mut self.ctx,
                        &mut air_constraints,
                        "zero_fin_m",
                    );
                    let cond_zero_plus_finite = fp_logical_or(
                        &cond_op1_zero_op2_fin,
                        &cond_op2_zero_op1_fin,
                        &mut self.ctx,
                        &mut air_constraints,
                        "cond_zero_plus_fin",
                    );

                    let both_true_zero = fp_logical_and(
                        &op1_is_zero_not_special,
                        &op2_is_zero_not_special,
                        &mut self.ctx,
                        &mut air_constraints,
                        "both_zero",
                    );
                    let both_zero_res_s = fp_logical_and(
                        &op1_s_expr,
                        &op2_s_expr,
                        &mut self.ctx,
                        &mut air_constraints,
                        "both_zero_s_logic",
                    );
                    let both_zero_res_e = AirExpression::Constant(0);
                    let both_zero_res_m = AirExpression::Constant(0);

                    let is_zero_result_scenario = fp_logical_or(
                        &cond_zero_plus_finite,
                        &both_true_zero,
                        &mut self.ctx,
                        &mut air_constraints,
                        "is_zero_res_scenario",
                    );
                    let inter_res_s_if_zero = fp_select(
                        &cond_zero_plus_finite,
                        &zero_plus_fin_res_s,
                        &both_zero_res_s,
                        &mut self.ctx,
                        &mut air_constraints,
                        "inter_s_if_zero",
                    );
                    let inter_res_e_if_zero = fp_select(
                        &cond_zero_plus_finite,
                        &zero_plus_fin_res_e,
                        &both_zero_res_e,
                        &mut self.ctx,
                        &mut air_constraints,
                        "inter_e_if_zero",
                    );
                    let inter_res_m_if_zero = fp_select(
                        &cond_zero_plus_finite,
                        &zero_plus_fin_res_m,
                        &both_zero_res_m,
                        &mut self.ctx,
                        &mut air_constraints,
                        "inter_m_if_zero",
                    );

                    let res_s_if_not_nan = fp_select(
                        &is_inf_result_scenario,
                        &inter_res_s_if_inf,
                        &general_case_res_s_expr,
                        &mut self.ctx,
                        &mut air_constraints,
                        "s_not_nan_inf_vs_gen",
                    );
                    let res_e_if_not_nan = fp_select(
                        &is_inf_result_scenario,
                        &inter_res_e_if_inf,
                        &general_case_res_e_expr,
                        &mut self.ctx,
                        &mut air_constraints,
                        "e_not_nan_inf_vs_gen",
                    );
                    let res_m_if_not_nan = fp_select(
                        &is_inf_result_scenario,
                        &inter_res_m_if_inf,
                        &general_case_res_m_expr,
                        &mut self.ctx,
                        &mut air_constraints,
                        "m_not_nan_inf_vs_gen",
                    );

                    let res_s_if_not_nan_not_inf = fp_select(
                        &is_zero_result_scenario,
                        &inter_res_s_if_zero,
                        &res_s_if_not_nan,
                        &mut self.ctx,
                        &mut air_constraints,
                        "s_not_nan_not_inf_zero_vs_else",
                    );
                    let res_e_if_not_nan_not_inf = fp_select(
                        &is_zero_result_scenario,
                        &inter_res_e_if_zero,
                        &res_e_if_not_nan,
                        &mut self.ctx,
                        &mut air_constraints,
                        "e_not_nan_not_inf_zero_vs_else",
                    );
                    let res_m_if_not_nan_not_inf = fp_select(
                        &is_zero_result_scenario,
                        &inter_res_m_if_zero,
                        &res_m_if_not_nan,
                        &mut self.ctx,
                        &mut air_constraints,
                        "m_not_nan_not_inf_zero_vs_else",
                    );

                    let final_res_s_val = fp_select(
                        &final_res_is_nan,
                        &qnan_sign,
                        &res_s_if_not_nan_not_inf,
                        &mut self.ctx,
                        &mut air_constraints,
                        "final_s",
                    );
                    let final_res_e_val = fp_select(
                        &final_res_is_nan,
                        &qnan_exp,
                        &res_e_if_not_nan_not_inf,
                        &mut self.ctx,
                        &mut air_constraints,
                        "final_e",
                    );
                    let final_res_m_val = fp_select(
                        &final_res_is_nan,
                        &qnan_mant,
                        &res_m_if_not_nan_not_inf,
                        &mut self.ctx,
                        &mut air_constraints,
                        "final_m",
                    );

                    air_constraints.push(AirExpression::Sub(
                        Box::new(res_s_expr),
                        Box::new(final_res_s_val),
                    ));
                    air_constraints.push(AirExpression::Sub(
                        Box::new(res_e_val_expr),
                        Box::new(final_res_e_val),
                    ));
                    air_constraints.push(AirExpression::Sub(
                        Box::new(res_m_val_expr),
                        Box::new(final_res_m_val),
                    ));

                    let not_special_scenario_intermediate1 = fp_logical_not(
                        &final_res_is_nan,
                        &mut self.ctx,
                        &mut air_constraints,
                        "not_nan_for_gen",
                    );
                    let not_special_scenario_intermediate2 = fp_logical_not(
                        &is_inf_result_scenario,
                        &mut self.ctx,
                        &mut air_constraints,
                        "not_inf_for_gen",
                    );
                    let not_special_scenario_intermediate3 = fp_logical_not(
                        &is_zero_result_scenario,
                        &mut self.ctx,
                        &mut air_constraints,
                        "not_zero_for_gen",
                    );
                    let is_general_case_cond_pt1 = fp_logical_and(
                        &not_special_scenario_intermediate1,
                        &not_special_scenario_intermediate2,
                        &mut self.ctx,
                        &mut air_constraints,
                        "gen_case_pt1",
                    );
                    let is_general_case_condition = fp_logical_and(
                        &is_general_case_cond_pt1,
                        &not_special_scenario_intermediate3,
                        &mut self.ctx,
                        &mut air_constraints,
                        "is_general_case",
                    );

                    let implicit_mant_bit_pos = mant_bit_count;

                    let all_ones_exp_biased = (1u128 << exp_bit_count) - 1;
                    let min_exp_biased_val = 1u128;
                    let zero_exp_biased_val = 0u128;

                    let op1_is_denormal = fp_is_value_equal(
                        &op1_e_val_expr,
                        &AirExpression::Constant(zero_exp_biased_val),
                        &mut self.ctx,
                        &mut air_constraints,
                        "op1_is_denorm_e_check",
                    );
                    let op2_is_denormal = fp_is_value_equal(
                        &op2_e_val_expr,
                        &AirExpression::Constant(zero_exp_biased_val),
                        &mut self.ctx,
                        &mut air_constraints,
                        "op2_is_denorm_e_check",
                    );

                    let implicit_bit_val_op1 = fp_logical_not(
                        &op1_is_denormal,
                        &mut self.ctx,
                        &mut air_constraints,
                        "op1_implicit_bit",
                    );
                    let implicit_bit_val_op2 = fp_logical_not(
                        &op2_is_denormal,
                        &mut self.ctx,
                        &mut air_constraints,
                        "op2_implicit_bit",
                    );

                    let full_significand_op1 = fp_add(
                        &op1_m_val_expr,
                        &fp_mul(
                            &implicit_bit_val_op1,
                            &AirExpression::Constant(1u128 << implicit_mant_bit_pos),
                            &mut self.ctx,
                            &mut air_constraints,
                            "op1_impl_shifted",
                        ),
                        &mut self.ctx,
                        &mut air_constraints,
                        "full_sig_op1",
                    );
                    let full_significand_op2 = fp_add(
                        &op2_m_val_expr,
                        &fp_mul(
                            &implicit_bit_val_op2,
                            &AirExpression::Constant(1u128 << implicit_mant_bit_pos),
                            &mut self.ctx,
                            &mut air_constraints,
                            "op2_impl_shifted",
                        ),
                        &mut self.ctx,
                        &mut air_constraints,
                        "full_sig_op2",
                    );

                    let effective_exp_op1 = fp_select(
                        &op1_is_denormal,
                        &AirExpression::Constant(min_exp_biased_val),
                        &op1_e_val_expr,
                        &mut self.ctx,
                        &mut air_constraints,
                        "eff_exp_op1",
                    );
                    let effective_exp_op2 = fp_select(
                        &op2_is_denormal,
                        &AirExpression::Constant(min_exp_biased_val),
                        &op2_e_val_expr,
                        &mut self.ctx,
                        &mut air_constraints,
                        "eff_exp_op2",
                    );

                    let op1_exp_lt_op2_exp = fp_icmp_ult(
                        &effective_exp_op1,
                        &effective_exp_op2,
                        exp_bit_count + 1,
                        &mut self.ctx,
                        &mut air_constraints,
                        "op1e_lt_op2e",
                    );

                    let e1_eff = fp_select(
                        &op1_exp_lt_op2_exp,
                        &effective_exp_op2,
                        &effective_exp_op1,
                        &mut self.ctx,
                        &mut air_constraints,
                        "e1_eff_sel",
                    );
                    let e2_eff = fp_select(
                        &op1_exp_lt_op2_exp,
                        &effective_exp_op1,
                        &effective_exp_op2,
                        &mut self.ctx,
                        &mut air_constraints,
                        "e2_eff_sel",
                    );
                    let sig1_full = fp_select(
                        &op1_exp_lt_op2_exp,
                        &full_significand_op2,
                        &full_significand_op1,
                        &mut self.ctx,
                        &mut air_constraints,
                        "sig1_sel",
                    );
                    let sig2_full = fp_select(
                        &op1_exp_lt_op2_exp,
                        &full_significand_op1,
                        &full_significand_op2,
                        &mut self.ctx,
                        &mut air_constraints,
                        "sig2_sel",
                    );
                    let s1_orig = fp_select(
                        &op1_exp_lt_op2_exp,
                        &op2_s_expr,
                        &op1_s_expr,
                        &mut self.ctx,
                        &mut air_constraints,
                        "s1_orig_sel",
                    );
                    let s2_orig = fp_select(
                        &op1_exp_lt_op2_exp,
                        &op1_s_expr,
                        &op2_s_expr,
                        &mut self.ctx,
                        &mut air_constraints,
                        "s2_orig_sel",
                    );

                    let exp_diff = fp_sub(
                        &e1_eff,
                        &e2_eff,
                        &mut self.ctx,
                        &mut air_constraints,
                        "exp_diff",
                    );
                    let final_calc_exp_biased = e1_eff.clone();

                    let (sig2_aligned, _guard_bit, _round_bit, _sticky_bit) =
                        fp_variable_right_shift_with_grs(
                            &sig2_full,
                            &exp_diff,
                            mant_bit_count + 1,
                            mant_bit_count + 3,
                            &mut self.ctx,
                            &mut air_constraints,
                            "sig2_align_shift",
                        );

                    let effective_op_is_sub = fp_icmp_neq(
                        &s1_orig,
                        &s2_orig,
                        &mut self.ctx,
                        &mut air_constraints,
                        "eff_op_is_sub",
                    );

                    let sig1_lt_sig2_aligned = fp_icmp_ult(
                        &sig1_full,
                        &sig2_aligned,
                        mant_bit_count + 3,
                        &mut self.ctx,
                        &mut air_constraints,
                        "sig1_lt_sig2a_for_sub",
                    );

                    let diff_sig1_minus_sig2 = fp_sub(
                        &sig1_full,
                        &sig2_aligned,
                        &mut self.ctx,
                        &mut air_constraints,
                        "diff_s1_minus_s2",
                    );
                    let diff_sig2_minus_sig1 = fp_sub(
                        &sig2_aligned,
                        &sig1_full,
                        &mut self.ctx,
                        &mut air_constraints,
                        "diff_s2_minus_s1",
                    );

                    let sub_magnitude = fp_select(
                        &sig1_lt_sig2_aligned,
                        &diff_sig2_minus_sig1,
                        &diff_sig1_minus_sig2,
                        &mut self.ctx,
                        &mut air_constraints,
                        "sub_magnitude",
                    );
                    let sub_sign = fp_select(
                        &sig1_lt_sig2_aligned,
                        &s2_orig,
                        &s1_orig,
                        &mut self.ctx,
                        &mut air_constraints,
                        "sub_sign",
                    );

                    let add_magnitude = fp_add(
                        &sig1_full,
                        &sig2_aligned,
                        &mut self.ctx,
                        &mut air_constraints,
                        "add_magnitude",
                    );
                    let add_sign = s1_orig.clone();

                    let intermediate_significand_val = fp_select(
                        &effective_op_is_sub,
                        &sub_magnitude,
                        &add_magnitude,
                        &mut self.ctx,
                        &mut air_constraints,
                        "intermediate_significand",
                    );
                    let result_sign_intermediate_val = fp_select(
                        &effective_op_is_sub,
                        &sub_sign,
                        &add_sign,
                        &mut self.ctx,
                        &mut air_constraints,
                        "result_sign_intermediate",
                    );

                    let (
                        normalized_sign,
                        adjusted_biased_exp,
                        normalized_significand,
                        _is_true_zero_after_norm_round,
                    ) = fp_normalize_and_round_significand(
                        &intermediate_significand_val,
                        &result_sign_intermediate_val,
                        &final_calc_exp_biased,
                        &_guard_bit,
                        &_round_bit,
                        &_sticky_bit,
                        mant_bit_count,
                        exp_bit_count,
                        &mut self.ctx,
                        &mut air_constraints,
                        "fadd_norm_round",
                    );

                    let exp_overflows = fp_icmp_ule(
                        &AirExpression::Constant(all_ones_exp_biased),
                        &adjusted_biased_exp,
                        exp_bit_count + 1,
                        &mut self.ctx,
                        &mut air_constraints,
                        "exp_overflows",
                    );
                    let exp_underflows_to_zero = fp_icmp_ule(
                        &adjusted_biased_exp,
                        &AirExpression::Constant(zero_exp_biased_val),
                        exp_bit_count + 1,
                        &mut self.ctx,
                        &mut air_constraints,
                        "exp_underflows",
                    );

                    let gen_case_final_s = fp_select(
                        &exp_overflows,
                        &normalized_sign,
                        &normalized_sign,
                        &mut self.ctx,
                        &mut air_constraints,
                        "gen_s_ovf",
                    );
                    let gen_case_final_s = fp_select(
                        &exp_underflows_to_zero,
                        &normalized_sign,
                        &gen_case_final_s,
                        &mut self.ctx,
                        &mut air_constraints,
                        "gen_s_undf",
                    );

                    let gen_case_final_e = fp_select(
                        &exp_overflows,
                        &AirExpression::Constant(all_ones_exp_biased),
                        &adjusted_biased_exp,
                        &mut self.ctx,
                        &mut air_constraints,
                        "gen_e_ovf",
                    );
                    let gen_case_final_e = fp_select(
                        &exp_underflows_to_zero,
                        &AirExpression::Constant(zero_exp_biased_val),
                        &gen_case_final_e,
                        &mut self.ctx,
                        &mut air_constraints,
                        "gen_e_undf",
                    );

                    let gen_case_final_m = fp_select(
                        &exp_overflows,
                        &AirExpression::Constant(0),
                        &normalized_significand,
                        &mut self.ctx,
                        &mut air_constraints,
                        "gen_m_ovf",
                    );
                    let gen_case_final_m = fp_select(
                        &exp_underflows_to_zero,
                        &AirExpression::Constant(0),
                        &gen_case_final_m,
                        &mut self.ctx,
                        &mut air_constraints,
                        "gen_m_undf",
                    );

                    let gen_s_val_diff = fp_sub(
                        &general_case_res_s_expr,
                        &gen_case_final_s,
                        &mut self.ctx,
                        &mut air_constraints,
                        "gen_s_val_diff",
                    );
                    let gen_s_constraint = fp_mul(
                        &is_general_case_condition,
                        &gen_s_val_diff,
                        &mut self.ctx,
                        &mut air_constraints,
                        "gen_s_constr_mul",
                    );
                    air_constraints.push(gen_s_constraint);

                    let gen_e_val_diff = fp_sub(
                        &general_case_res_e_expr,
                        &gen_case_final_e,
                        &mut self.ctx,
                        &mut air_constraints,
                        "gen_e_val_diff",
                    );
                    let gen_e_constraint = fp_mul(
                        &is_general_case_condition,
                        &gen_e_val_diff,
                        &mut self.ctx,
                        &mut air_constraints,
                        "gen_e_constr_mul",
                    );
                    air_constraints.push(gen_e_constraint);

                    let gen_m_val_diff = fp_sub(
                        &general_case_res_m_expr,
                        &gen_case_final_m,
                        &mut self.ctx,
                        &mut air_constraints,
                        "gen_m_val_diff",
                    );
                    let gen_m_constraint = fp_mul(
                        &is_general_case_condition,
                        &gen_m_val_diff,
                        &mut self.ctx,
                        &mut air_constraints,
                        "gen_m_constr_mul",
                    );
                    air_constraints.push(gen_m_constraint);
                }
                StructuredAirConstraint::FSub {
                    operand1,
                    operand2,
                    result,
                    operand_bitwidth,
                    block_name: _,
                } => {
                    println!(
                        "  FSUB: op1={:?}, op2={:?}, res={:?} (bitwidth {}) - Setting up S/E/M aux vars.",
                        operand1, operand2, result, operand_bitwidth
                    );

                    let (s_bit_count, exp_bit_count, mant_bit_count) = match operand_bitwidth {
                        16 => (1u32, 5u32, 10u32),
                        32 => (1u32, 8u32, 23u32),
                        64 => (1u32, 11u32, 52u32),
                        80 => (1u32, 15u32, 63u32),
                        128 => (1u32, 15u32, 112u32),
                        _ => panic!(
                            "Unsupported operand_bitwidth {} for FSub S/E/M decomposition.",
                            operand_bitwidth
                        ),
                    };

                    let (op1_s_var, op1_e_var, op1_m_var) = setup_sem_aux_vars(
                        operand1,
                        "op1",
                        &mut self.ctx,
                        s_bit_count,
                        exp_bit_count,
                        mant_bit_count,
                        &mut air_constraints,
                    );
                    let (op2_s_var, op2_e_var, op2_m_var) = setup_sem_aux_vars(
                        operand2,
                        "op2_fsub",
                        &mut self.ctx,
                        s_bit_count,
                        exp_bit_count,
                        mant_bit_count,
                        &mut air_constraints,
                    );
                    let (res_s_var, res_e_var, res_m_var) = setup_sem_aux_vars(
                        lang::Operand::Var(result),
                        "res",
                        &mut self.ctx,
                        s_bit_count,
                        exp_bit_count,
                        mant_bit_count,
                        &mut air_constraints,
                    );

                    let op1_s_expr = AirExpression::Trace(op1_s_var, RowOffset::Current);
                    let op1_e_val_expr = AirExpression::Trace(op1_e_var, RowOffset::Current);
                    let op1_m_val_expr = AirExpression::Trace(op1_m_var, RowOffset::Current);

                    let op2_s_original_expr = AirExpression::Trace(op2_s_var, RowOffset::Current);

                    let op2_s_expr = fp_logical_not(
                        &op2_s_original_expr,
                        &mut self.ctx,
                        &mut air_constraints,
                        "op2_s_flipped_fsub",
                    );

                    let op2_e_val_expr = AirExpression::Trace(op2_e_var, RowOffset::Current);
                    let op2_m_val_expr = AirExpression::Trace(op2_m_var, RowOffset::Current);

                    let res_s_expr = AirExpression::Trace(res_s_var, RowOffset::Current);
                    let res_e_val_expr = AirExpression::Trace(res_e_var, RowOffset::Current);
                    let res_m_val_expr = AirExpression::Trace(res_m_var, RowOffset::Current);

                    let op1_is_nan = fp_is_nan(
                        &op1_e_val_expr,
                        &op1_m_val_expr,
                        exp_bit_count,
                        mant_bit_count,
                        &mut self.ctx,
                        &mut air_constraints,
                        "op1_fsub",
                    );

                    let op2_is_nan = fp_is_nan(
                        &op2_e_val_expr,
                        &op2_m_val_expr,
                        exp_bit_count,
                        mant_bit_count,
                        &mut self.ctx,
                        &mut air_constraints,
                        "op2_fsub",
                    );

                    let op1_is_inf = fp_is_inf(
                        &op1_e_val_expr,
                        &op1_m_val_expr,
                        exp_bit_count,
                        mant_bit_count,
                        &mut self.ctx,
                        &mut air_constraints,
                        "op1_fsub",
                    );

                    let op2_is_inf_original_sign = fp_is_inf(
                        &op2_e_val_expr,
                        &op2_m_val_expr,
                        exp_bit_count,
                        mant_bit_count,
                        &mut self.ctx,
                        &mut air_constraints,
                        "op2_orig_inf_fsub",
                    );

                    let op1_is_pos_inf = fp_logical_and(
                        &op1_is_inf,
                        &fp_is_value_zero(
                            &op1_s_expr,
                            &mut self.ctx,
                            &mut air_constraints,
                            "op1_s_is_zero_fsub",
                        ),
                        &mut self.ctx,
                        &mut air_constraints,
                        "op1_is_pos_inf_fsub",
                    );
                    let op1_is_neg_inf = fp_logical_and(
                        &op1_is_inf,
                        &fp_logical_not(
                            &fp_is_value_zero(
                                &op1_s_expr,
                                &mut self.ctx,
                                &mut air_constraints,
                                "op1_s_is_zero_for_neg_fsub",
                            ),
                            &mut self.ctx,
                            &mut air_constraints,
                            "op1_s_is_one_fsub",
                        ),
                        &mut self.ctx,
                        &mut air_constraints,
                        "op1_is_neg_inf_fsub",
                    );

                    let op2_is_pos_inf_effective = fp_logical_and(
                        &op2_is_inf_original_sign,
                        &fp_is_value_zero(
                            &op2_s_expr,
                            &mut self.ctx,
                            &mut air_constraints,
                            "op2_s_flipped_is_zero_fsub",
                        ),
                        &mut self.ctx,
                        &mut air_constraints,
                        "op2_is_pos_inf_eff_fsub",
                    );
                    let op2_is_neg_inf_effective = fp_logical_and(
                        &op2_is_inf_original_sign,
                        &fp_logical_not(
                            &fp_is_value_zero(
                                &op2_s_expr,
                                &mut self.ctx,
                                &mut air_constraints,
                                "op2_s_flipped_is_zero_for_neg_fsub",
                            ),
                            &mut self.ctx,
                            &mut air_constraints,
                            "op2_s_flipped_is_one_fsub",
                        ),
                        &mut self.ctx,
                        &mut air_constraints,
                        "op2_is_neg_inf_eff_fsub",
                    );

                    let op1_is_true_zero = fp_is_true_zero(
                        &op1_e_val_expr,
                        &op1_m_val_expr,
                        exp_bit_count,
                        mant_bit_count,
                        &mut self.ctx,
                        &mut air_constraints,
                        "op1_fsub",
                    );
                    let op2_is_true_zero = fp_is_true_zero(
                        &op2_e_val_expr,
                        &op2_m_val_expr,
                        exp_bit_count,
                        mant_bit_count,
                        &mut self.ctx,
                        &mut air_constraints,
                        "op2_fsub",
                    );

                    let qnan_sign = AirExpression::Constant(0);
                    let qnan_exp = AirExpression::Constant((1u128 << exp_bit_count) - 1);
                    let qnan_mant = AirExpression::Constant(1u128 << (mant_bit_count - 1));

                    let res_is_nan_due_to_op_nan = fp_logical_or(
                        &op1_is_nan,
                        &op2_is_nan,
                        &mut self.ctx,
                        &mut air_constraints,
                        "res_is_nan_from_op_fsub",
                    );

                    let inf_plus_neg_inf = fp_logical_and(
                        &op1_is_pos_inf,
                        &op2_is_neg_inf_effective,
                        &mut self.ctx,
                        &mut air_constraints,
                        "pInf_nInf_fsub",
                    );
                    let neg_inf_plus_pos_inf = fp_logical_and(
                        &op1_is_neg_inf,
                        &op2_is_pos_inf_effective,
                        &mut self.ctx,
                        &mut air_constraints,
                        "nInf_pInf_fsub",
                    );
                    let res_is_nan_due_to_inf_cancel = fp_logical_or(
                        &inf_plus_neg_inf,
                        &neg_inf_plus_pos_inf,
                        &mut self.ctx,
                        &mut air_constraints,
                        "res_is_nan_inf_cancel_fsub",
                    );

                    let final_res_is_nan = fp_logical_or(
                        &res_is_nan_due_to_op_nan,
                        &res_is_nan_due_to_inf_cancel,
                        &mut self.ctx,
                        &mut air_constraints,
                        "final_res_is_nan_fsub",
                    );

                    let general_case_res_s_expr =
                        AirExpression::Trace(self.ctx.new_aux_variable(), RowOffset::Current);
                    let general_case_res_e_expr =
                        AirExpression::Trace(self.ctx.new_aux_variable(), RowOffset::Current);
                    let general_case_res_m_expr =
                        AirExpression::Trace(self.ctx.new_aux_variable(), RowOffset::Current);
                    air_constraints.push(AirExpression::Mul(
                        Box::new(general_case_res_s_expr.clone()),
                        Box::new(AirExpression::Sub(
                            Box::new(general_case_res_s_expr.clone()),
                            Box::new(AirExpression::Constant(1)),
                        )),
                    ));

                    let op1_is_inf_not_nan = fp_logical_and(
                        &op1_is_inf,
                        &fp_logical_not(
                            &op1_is_nan,
                            &mut self.ctx,
                            &mut air_constraints,
                            "op1_not_nan_fsub",
                        ),
                        &mut self.ctx,
                        &mut air_constraints,
                        "op1_inf_not_nan_fsub",
                    );

                    let op2_is_inf_eff_not_nan = fp_logical_and(
                        &op2_is_inf_original_sign,
                        &fp_logical_not(
                            &op2_is_nan,
                            &mut self.ctx,
                            &mut air_constraints,
                            "op2_not_nan_fsub",
                        ),
                        &mut self.ctx,
                        &mut air_constraints,
                        "op2_inf_eff_not_nan_fsub",
                    );

                    let op1_is_fin_not_nan = fp_logical_not(
                        &op1_is_inf_not_nan,
                        &mut self.ctx,
                        &mut air_constraints,
                        "op1_fin_not_nan_fsub",
                    );
                    let op2_is_fin_eff_not_nan = fp_logical_not(
                        &op2_is_inf_eff_not_nan,
                        &mut self.ctx,
                        &mut air_constraints,
                        "op2_fin_eff_not_nan_fsub",
                    );

                    let inf_plus_finite_res_s = fp_select(
                        &op1_is_inf_not_nan,
                        &op1_s_expr,
                        &op2_s_expr,
                        &mut self.ctx,
                        &mut air_constraints,
                        "inf_fin_s_fsub",
                    );
                    let cond_inf_plus_finite = fp_logical_or(
                        &fp_logical_and(
                            &op1_is_inf_not_nan,
                            &op2_is_fin_eff_not_nan,
                            &mut self.ctx,
                            &mut air_constraints,
                            "op1inf_op2fin_fsub",
                        ),
                        &fp_logical_and(
                            &op2_is_inf_eff_not_nan,
                            &op1_is_fin_not_nan,
                            &mut self.ctx,
                            &mut air_constraints,
                            "op2inf_op1fin_fsub",
                        ),
                        &mut self.ctx,
                        &mut air_constraints,
                        "cond_inf_plus_fin_fsub",
                    );

                    let op1_is_pos_inf_not_nan = fp_logical_and(
                        &op1_is_pos_inf,
                        &fp_logical_not(
                            &op1_is_nan,
                            &mut self.ctx,
                            &mut air_constraints,
                            "op1_pos_inf_nn_aux1_fsub",
                        ),
                        &mut self.ctx,
                        &mut air_constraints,
                        "op1_pos_inf_nn_fsub",
                    );

                    let op2_is_eff_pos_inf_not_nan = fp_logical_and(
                        &op2_is_pos_inf_effective,
                        &fp_logical_not(
                            &op2_is_nan,
                            &mut self.ctx,
                            &mut air_constraints,
                            "op2_eff_pos_inf_nn_aux1_fsub",
                        ),
                        &mut self.ctx,
                        &mut air_constraints,
                        "op2_eff_pos_inf_nn_fsub",
                    );

                    let op1_is_neg_inf_not_nan = fp_logical_and(
                        &op1_is_neg_inf,
                        &fp_logical_not(
                            &op1_is_nan,
                            &mut self.ctx,
                            &mut air_constraints,
                            "op1_neg_inf_nn_aux1_fsub",
                        ),
                        &mut self.ctx,
                        &mut air_constraints,
                        "op1_neg_inf_nn_fsub",
                    );

                    let op2_is_eff_neg_inf_not_nan = fp_logical_and(
                        &op2_is_neg_inf_effective,
                        &fp_logical_not(
                            &op2_is_nan,
                            &mut self.ctx,
                            &mut air_constraints,
                            "op2_eff_neg_inf_nn_aux1_fsub",
                        ),
                        &mut self.ctx,
                        &mut air_constraints,
                        "op2_eff_neg_inf_nn_fsub",
                    );

                    let both_eff_pos_inf = fp_logical_and(
                        &op1_is_pos_inf_not_nan,
                        &op2_is_eff_pos_inf_not_nan,
                        &mut self.ctx,
                        &mut air_constraints,
                        "both_eff_pos_inf_fsub",
                    );
                    let both_eff_neg_inf = fp_logical_and(
                        &op1_is_neg_inf_not_nan,
                        &op2_is_eff_neg_inf_not_nan,
                        &mut self.ctx,
                        &mut air_constraints,
                        "both_eff_neg_inf_fsub",
                    );
                    let cond_both_inf_same_eff_sign = fp_logical_or(
                        &both_eff_pos_inf,
                        &both_eff_neg_inf,
                        &mut self.ctx,
                        &mut air_constraints,
                        "both_inf_same_eff_sign_fsub",
                    );
                    let both_inf_same_eff_sign_res_s = op1_s_expr.clone();

                    let is_inf_result_scenario = fp_logical_or(
                        &cond_inf_plus_finite,
                        &cond_both_inf_same_eff_sign,
                        &mut self.ctx,
                        &mut air_constraints,
                        "is_inf_res_scenario_fsub",
                    );
                    let inter_res_s_if_inf = fp_select(
                        &cond_inf_plus_finite,
                        &inf_plus_finite_res_s,
                        &both_inf_same_eff_sign_res_s,
                        &mut self.ctx,
                        &mut air_constraints,
                        "inter_s_if_inf_fsub",
                    );
                    let inter_res_e_if_inf = qnan_exp.clone();
                    let inter_res_m_if_inf = AirExpression::Constant(0);

                    let op1_is_zero_not_special = fp_logical_and(
                        &op1_is_true_zero,
                        &fp_logical_not(
                            &op1_is_nan,
                            &mut self.ctx,
                            &mut air_constraints,
                            "op1_not_nan_z_fsub",
                        ),
                        &mut self.ctx,
                        &mut air_constraints,
                        "op1_zero_not_nan_fsub",
                    );
                    let op1_is_zero_not_special = fp_logical_and(
                        &op1_is_zero_not_special,
                        &fp_logical_not(
                            &op1_is_inf,
                            &mut self.ctx,
                            &mut air_constraints,
                            "op1_not_inf_z_fsub",
                        ),
                        &mut self.ctx,
                        &mut air_constraints,
                        "op1_zero_not_spec_fsub",
                    );

                    let op2_is_zero_not_special = fp_logical_and(
                        &op2_is_true_zero,
                        &fp_logical_not(
                            &op2_is_nan,
                            &mut self.ctx,
                            &mut air_constraints,
                            "op2_not_nan_z_fsub",
                        ),
                        &mut self.ctx,
                        &mut air_constraints,
                        "op2_zero_not_nan_fsub",
                    );
                    let op2_is_zero_not_special = fp_logical_and(
                        &op2_is_zero_not_special,
                        &fp_logical_not(
                            &op2_is_inf_original_sign,
                            &mut self.ctx,
                            &mut air_constraints,
                            "op2_not_inf_z_fsub",
                        ),
                        &mut self.ctx,
                        &mut air_constraints,
                        "op2_zero_not_spec_fsub",
                    );

                    let cond_op1_zero_op2_fin = fp_logical_and(
                        &op1_is_zero_not_special,
                        &op2_is_fin_eff_not_nan,
                        &mut self.ctx,
                        &mut air_constraints,
                        "op1z_op2fin_fsub",
                    );

                    let cond_op2_zero_op1_fin = fp_logical_and(
                        &op2_is_zero_not_special,
                        &op1_is_fin_not_nan,
                        &mut self.ctx,
                        &mut air_constraints,
                        "op2z_op1fin_fsub",
                    );

                    let zero_plus_fin_res_s = fp_select(
                        &cond_op1_zero_op2_fin,
                        &op2_s_expr,
                        &op1_s_expr,
                        &mut self.ctx,
                        &mut air_constraints,
                        "zero_fin_s_fsub",
                    );
                    let zero_plus_fin_res_e = fp_select(
                        &cond_op1_zero_op2_fin,
                        &op2_e_val_expr,
                        &op1_e_val_expr,
                        &mut self.ctx,
                        &mut air_constraints,
                        "zero_fin_e_fsub",
                    );
                    let zero_plus_fin_res_m = fp_select(
                        &cond_op1_zero_op2_fin,
                        &op2_m_val_expr,
                        &op1_m_val_expr,
                        &mut self.ctx,
                        &mut air_constraints,
                        "zero_fin_m_fsub",
                    );
                    let cond_zero_plus_finite = fp_logical_or(
                        &cond_op1_zero_op2_fin,
                        &cond_op2_zero_op1_fin,
                        &mut self.ctx,
                        &mut air_constraints,
                        "cond_zero_plus_fin_fsub",
                    );

                    let both_true_zero = fp_logical_and(
                        &op1_is_zero_not_special,
                        &op2_is_zero_not_special,
                        &mut self.ctx,
                        &mut air_constraints,
                        "both_zero_fsub",
                    );

                    let both_zero_res_s = fp_logical_and(
                        &op1_s_expr,
                        &op2_s_expr,
                        &mut self.ctx,
                        &mut air_constraints,
                        "both_zero_s_logic_fsub",
                    );
                    let both_zero_res_e = AirExpression::Constant(0);
                    let both_zero_res_m = AirExpression::Constant(0);

                    let is_zero_result_scenario = fp_logical_or(
                        &cond_zero_plus_finite,
                        &both_true_zero,
                        &mut self.ctx,
                        &mut air_constraints,
                        "is_zero_res_scenario_fsub",
                    );
                    let inter_res_s_if_zero = fp_select(
                        &cond_zero_plus_finite,
                        &zero_plus_fin_res_s,
                        &both_zero_res_s,
                        &mut self.ctx,
                        &mut air_constraints,
                        "inter_s_if_zero_fsub",
                    );
                    let inter_res_e_if_zero = fp_select(
                        &cond_zero_plus_finite,
                        &zero_plus_fin_res_e,
                        &both_zero_res_e,
                        &mut self.ctx,
                        &mut air_constraints,
                        "inter_e_if_zero_fsub",
                    );
                    let inter_res_m_if_zero = fp_select(
                        &cond_zero_plus_finite,
                        &zero_plus_fin_res_m,
                        &both_zero_res_m,
                        &mut self.ctx,
                        &mut air_constraints,
                        "inter_m_if_zero_fsub",
                    );

                    let res_s_if_not_nan = fp_select(
                        &is_inf_result_scenario,
                        &inter_res_s_if_inf,
                        &general_case_res_s_expr,
                        &mut self.ctx,
                        &mut air_constraints,
                        "s_not_nan_inf_vs_gen_fsub",
                    );
                    let res_e_if_not_nan = fp_select(
                        &is_inf_result_scenario,
                        &inter_res_e_if_inf,
                        &general_case_res_e_expr,
                        &mut self.ctx,
                        &mut air_constraints,
                        "e_not_nan_inf_vs_gen_fsub",
                    );
                    let res_m_if_not_nan = fp_select(
                        &is_inf_result_scenario,
                        &inter_res_m_if_inf,
                        &general_case_res_m_expr,
                        &mut self.ctx,
                        &mut air_constraints,
                        "m_not_nan_inf_vs_gen_fsub",
                    );

                    let res_s_if_not_nan_not_inf = fp_select(
                        &is_zero_result_scenario,
                        &inter_res_s_if_zero,
                        &res_s_if_not_nan,
                        &mut self.ctx,
                        &mut air_constraints,
                        "s_not_nan_not_inf_zero_vs_else_fsub",
                    );
                    let res_e_if_not_nan_not_inf = fp_select(
                        &is_zero_result_scenario,
                        &inter_res_e_if_zero,
                        &res_e_if_not_nan,
                        &mut self.ctx,
                        &mut air_constraints,
                        "e_not_nan_not_inf_zero_vs_else_fsub",
                    );
                    let res_m_if_not_nan_not_inf = fp_select(
                        &is_zero_result_scenario,
                        &inter_res_m_if_zero,
                        &res_m_if_not_nan,
                        &mut self.ctx,
                        &mut air_constraints,
                        "m_not_nan_not_inf_zero_vs_else_fsub",
                    );

                    let final_res_s_val = fp_select(
                        &final_res_is_nan,
                        &qnan_sign,
                        &res_s_if_not_nan_not_inf,
                        &mut self.ctx,
                        &mut air_constraints,
                        "final_s_fsub",
                    );
                    let final_res_e_val = fp_select(
                        &final_res_is_nan,
                        &qnan_exp,
                        &res_e_if_not_nan_not_inf,
                        &mut self.ctx,
                        &mut air_constraints,
                        "final_e_fsub",
                    );
                    let final_res_m_val = fp_select(
                        &final_res_is_nan,
                        &qnan_mant,
                        &res_m_if_not_nan_not_inf,
                        &mut self.ctx,
                        &mut air_constraints,
                        "final_m_fsub",
                    );

                    air_constraints.push(AirExpression::Sub(
                        Box::new(res_s_expr),
                        Box::new(final_res_s_val),
                    ));
                    air_constraints.push(AirExpression::Sub(
                        Box::new(res_e_val_expr),
                        Box::new(final_res_e_val),
                    ));
                    air_constraints.push(AirExpression::Sub(
                        Box::new(res_m_val_expr),
                        Box::new(final_res_m_val),
                    ));

                    let not_special_scenario_intermediate1 = fp_logical_not(
                        &final_res_is_nan,
                        &mut self.ctx,
                        &mut air_constraints,
                        "not_nan_for_gen_fsub",
                    );
                    let not_special_scenario_intermediate2 = fp_logical_not(
                        &is_inf_result_scenario,
                        &mut self.ctx,
                        &mut air_constraints,
                        "not_inf_for_gen_fsub",
                    );
                    let not_special_scenario_intermediate3 = fp_logical_not(
                        &is_zero_result_scenario,
                        &mut self.ctx,
                        &mut air_constraints,
                        "not_zero_for_gen_fsub",
                    );
                    let is_general_case_cond_pt1 = fp_logical_and(
                        &not_special_scenario_intermediate1,
                        &not_special_scenario_intermediate2,
                        &mut self.ctx,
                        &mut air_constraints,
                        "gen_case_pt1_fsub",
                    );
                    let is_general_case_condition = fp_logical_and(
                        &is_general_case_cond_pt1,
                        &not_special_scenario_intermediate3,
                        &mut self.ctx,
                        &mut air_constraints,
                        "is_general_case_fsub",
                    );

                    let implicit_mant_bit_pos = mant_bit_count;
                    let all_ones_exp_biased = (1u128 << exp_bit_count) - 1;
                    let min_exp_biased_val = 1u128;
                    let zero_exp_biased_val = 0u128;

                    let op1_is_denormal = fp_is_value_equal(
                        &op1_e_val_expr,
                        &AirExpression::Constant(zero_exp_biased_val),
                        &mut self.ctx,
                        &mut air_constraints,
                        "op1_is_denorm_e_check_fsub",
                    );

                    let op2_is_denormal = fp_is_value_equal(
                        &op2_e_val_expr,
                        &AirExpression::Constant(zero_exp_biased_val),
                        &mut self.ctx,
                        &mut air_constraints,
                        "op2_is_denorm_e_check_fsub",
                    );

                    let implicit_bit_val_op1 = fp_logical_not(
                        &op1_is_denormal,
                        &mut self.ctx,
                        &mut air_constraints,
                        "op1_implicit_bit_fsub",
                    );
                    let implicit_bit_val_op2 = fp_logical_not(
                        &op2_is_denormal,
                        &mut self.ctx,
                        &mut air_constraints,
                        "op2_implicit_bit_fsub",
                    );

                    let full_significand_op1 = fp_add(
                        &op1_m_val_expr,
                        &fp_mul(
                            &implicit_bit_val_op1,
                            &AirExpression::Constant(1u128 << implicit_mant_bit_pos),
                            &mut self.ctx,
                            &mut air_constraints,
                            "op1_impl_shifted_fsub",
                        ),
                        &mut self.ctx,
                        &mut air_constraints,
                        "full_sig_op1_fsub",
                    );
                    let full_significand_op2 = fp_add(
                        &op2_m_val_expr,
                        &fp_mul(
                            &implicit_bit_val_op2,
                            &AirExpression::Constant(1u128 << implicit_mant_bit_pos),
                            &mut self.ctx,
                            &mut air_constraints,
                            "op2_impl_shifted_fsub",
                        ),
                        &mut self.ctx,
                        &mut air_constraints,
                        "full_sig_op2_fsub",
                    );

                    let effective_exp_op1 = fp_select(
                        &op1_is_denormal,
                        &AirExpression::Constant(min_exp_biased_val),
                        &op1_e_val_expr,
                        &mut self.ctx,
                        &mut air_constraints,
                        "eff_exp_op1_fsub",
                    );
                    let effective_exp_op2 = fp_select(
                        &op2_is_denormal,
                        &AirExpression::Constant(min_exp_biased_val),
                        &op2_e_val_expr,
                        &mut self.ctx,
                        &mut air_constraints,
                        "eff_exp_op2_fsub",
                    );

                    let op1_exp_lt_op2_exp = fp_icmp_ult(
                        &effective_exp_op1,
                        &effective_exp_op2,
                        exp_bit_count + 1,
                        &mut self.ctx,
                        &mut air_constraints,
                        "op1e_lt_op2e_fsub",
                    );

                    let e1_eff = fp_select(
                        &op1_exp_lt_op2_exp,
                        &effective_exp_op2,
                        &effective_exp_op1,
                        &mut self.ctx,
                        &mut air_constraints,
                        "e1_eff_sel_fsub",
                    );
                    let e2_eff = fp_select(
                        &op1_exp_lt_op2_exp,
                        &effective_exp_op1,
                        &effective_exp_op2,
                        &mut self.ctx,
                        &mut air_constraints,
                        "e2_eff_sel_fsub",
                    );
                    let sig1_full = fp_select(
                        &op1_exp_lt_op2_exp,
                        &full_significand_op2,
                        &full_significand_op1,
                        &mut self.ctx,
                        &mut air_constraints,
                        "sig1_sel_fsub",
                    );
                    let sig2_full = fp_select(
                        &op1_exp_lt_op2_exp,
                        &full_significand_op1,
                        &full_significand_op2,
                        &mut self.ctx,
                        &mut air_constraints,
                        "sig2_sel_fsub",
                    );

                    let s1_orig = fp_select(
                        &op1_exp_lt_op2_exp,
                        &op2_s_expr,
                        &op1_s_expr,
                        &mut self.ctx,
                        &mut air_constraints,
                        "s1_orig_sel_fsub",
                    );
                    let s2_orig = fp_select(
                        &op1_exp_lt_op2_exp,
                        &op1_s_expr,
                        &op2_s_expr,
                        &mut self.ctx,
                        &mut air_constraints,
                        "s2_orig_sel_fsub",
                    );

                    let exp_diff = fp_sub(
                        &e1_eff,
                        &e2_eff,
                        &mut self.ctx,
                        &mut air_constraints,
                        "exp_diff_fsub",
                    );
                    let final_calc_exp_biased = e1_eff.clone();

                    let (sig2_aligned, _guard_bit, _round_bit, _sticky_bit) =
                        fp_variable_right_shift_with_grs(
                            &sig2_full,
                            &exp_diff,
                            mant_bit_count + 1,
                            mant_bit_count + 3,
                            &mut self.ctx,
                            &mut air_constraints,
                            "sig2_align_shift_fsub",
                        );

                    let effective_op_is_sub = fp_icmp_neq(
                        &s1_orig,
                        &s2_orig,
                        &mut self.ctx,
                        &mut air_constraints,
                        "eff_op_is_sub_fsub",
                    );

                    let sig1_lt_sig2_aligned = fp_icmp_ult(
                        &sig1_full,
                        &sig2_aligned,
                        mant_bit_count + 3,
                        &mut self.ctx,
                        &mut air_constraints,
                        "sig1_lt_sig2a_for_sub_fsub",
                    );

                    let diff_sig1_minus_sig2 = fp_sub(
                        &sig1_full,
                        &sig2_aligned,
                        &mut self.ctx,
                        &mut air_constraints,
                        "diff_s1_minus_s2_fsub",
                    );
                    let diff_sig2_minus_sig1 = fp_sub(
                        &sig2_aligned,
                        &sig1_full,
                        &mut self.ctx,
                        &mut air_constraints,
                        "diff_s2_minus_s1_fsub",
                    );

                    let sub_magnitude = fp_select(
                        &sig1_lt_sig2_aligned,
                        &diff_sig2_minus_sig1,
                        &diff_sig1_minus_sig2,
                        &mut self.ctx,
                        &mut air_constraints,
                        "sub_magnitude_fsub",
                    );
                    let sub_sign = fp_select(
                        &sig1_lt_sig2_aligned,
                        &s2_orig,
                        &s1_orig,
                        &mut self.ctx,
                        &mut air_constraints,
                        "sub_sign_fsub",
                    );

                    let add_magnitude = fp_add(
                        &sig1_full,
                        &sig2_aligned,
                        &mut self.ctx,
                        &mut air_constraints,
                        "add_magnitude_fsub",
                    );
                    let add_sign = s1_orig.clone();

                    let intermediate_significand_val = fp_select(
                        &effective_op_is_sub,
                        &sub_magnitude,
                        &add_magnitude,
                        &mut self.ctx,
                        &mut air_constraints,
                        "intermediate_significand_fsub",
                    );
                    let result_sign_intermediate_val = fp_select(
                        &effective_op_is_sub,
                        &sub_sign,
                        &add_sign,
                        &mut self.ctx,
                        &mut air_constraints,
                        "result_sign_intermediate_fsub",
                    );

                    let (
                        normalized_sign,
                        adjusted_biased_exp,
                        normalized_significand,
                        _is_true_zero_after_norm_round,
                    ) = fp_normalize_and_round_significand(
                        &intermediate_significand_val,
                        &result_sign_intermediate_val,
                        &final_calc_exp_biased,
                        &_guard_bit,
                        &_round_bit,
                        &_sticky_bit,
                        mant_bit_count,
                        exp_bit_count,
                        &mut self.ctx,
                        &mut air_constraints,
                        "fsub_norm_round",
                    );

                    let exp_overflows = fp_icmp_ule(
                        &AirExpression::Constant(all_ones_exp_biased),
                        &adjusted_biased_exp,
                        exp_bit_count + 1,
                        &mut self.ctx,
                        &mut air_constraints,
                        "exp_overflows_fsub",
                    );
                    let exp_underflows_to_zero = fp_icmp_ule(
                        &adjusted_biased_exp,
                        &AirExpression::Constant(zero_exp_biased_val),
                        exp_bit_count + 1,
                        &mut self.ctx,
                        &mut air_constraints,
                        "exp_underflows_fsub",
                    );

                    let gen_case_final_s = fp_select(
                        &exp_overflows,
                        &normalized_sign,
                        &normalized_sign,
                        &mut self.ctx,
                        &mut air_constraints,
                        "gen_s_ovf_fsub",
                    );
                    let gen_case_final_s = fp_select(
                        &exp_underflows_to_zero,
                        &normalized_sign,
                        &gen_case_final_s,
                        &mut self.ctx,
                        &mut air_constraints,
                        "gen_s_undf_fsub",
                    );

                    let gen_case_final_e = fp_select(
                        &exp_overflows,
                        &AirExpression::Constant(all_ones_exp_biased),
                        &adjusted_biased_exp,
                        &mut self.ctx,
                        &mut air_constraints,
                        "gen_e_ovf_fsub",
                    );
                    let gen_case_final_e = fp_select(
                        &exp_underflows_to_zero,
                        &AirExpression::Constant(zero_exp_biased_val),
                        &gen_case_final_e,
                        &mut self.ctx,
                        &mut air_constraints,
                        "gen_e_undf_fsub",
                    );

                    let gen_case_final_m = fp_select(
                        &exp_overflows,
                        &AirExpression::Constant(0),
                        &normalized_significand,
                        &mut self.ctx,
                        &mut air_constraints,
                        "gen_m_ovf_fsub",
                    );
                    let gen_case_final_m = fp_select(
                        &exp_underflows_to_zero,
                        &AirExpression::Constant(0),
                        &gen_case_final_m,
                        &mut self.ctx,
                        &mut air_constraints,
                        "gen_m_undf_fsub",
                    );

                    let gen_s_val_diff = fp_sub(
                        &general_case_res_s_expr,
                        &gen_case_final_s,
                        &mut self.ctx,
                        &mut air_constraints,
                        "gen_s_val_diff_fsub",
                    );
                    let gen_s_constraint = fp_mul(
                        &is_general_case_condition,
                        &gen_s_val_diff,
                        &mut self.ctx,
                        &mut air_constraints,
                        "gen_s_constr_mul_fsub",
                    );
                    air_constraints.push(gen_s_constraint);

                    let gen_e_val_diff = fp_sub(
                        &general_case_res_e_expr,
                        &gen_case_final_e,
                        &mut self.ctx,
                        &mut air_constraints,
                        "gen_e_val_diff_fsub",
                    );
                    let gen_e_constraint = fp_mul(
                        &is_general_case_condition,
                        &gen_e_val_diff,
                        &mut self.ctx,
                        &mut air_constraints,
                        "gen_e_constr_mul_fsub",
                    );
                    air_constraints.push(gen_e_constraint);

                    let gen_m_val_diff = fp_sub(
                        &general_case_res_m_expr,
                        &gen_case_final_m,
                        &mut self.ctx,
                        &mut air_constraints,
                        "gen_m_val_diff_fsub",
                    );
                    let gen_m_constraint = fp_mul(
                        &is_general_case_condition,
                        &gen_m_val_diff,
                        &mut self.ctx,
                        &mut air_constraints,
                        "gen_m_constr_mul_fsub",
                    );
                    air_constraints.push(gen_m_constraint);
                }

                StructuredAirConstraint::FMul {
                    operand1,
                    operand2,
                    result,
                    operand_bitwidth,
                    block_name: _,
                } => {
                    println!(
                        "  FMUL: op1={:?}, op2={:?}, res={:?} (bitwidth {}) - Setting up S/E/M aux vars.",
                        operand1, operand2, result, operand_bitwidth
                    );

                    let (s_bit_count, exp_bit_count, mant_bit_count) = match operand_bitwidth {
                        16 => (1u32, 5u32, 10u32),
                        32 => (1u32, 8u32, 23u32),
                        64 => (1u32, 11u32, 52u32),
                        80 => (1u32, 15u32, 63u32),
                        128 => (1u32, 15u32, 112u32),
                        _ => panic!(
                            "Unsupported operand_bitwidth {} for FMul S/E/M decomposition.",
                            operand_bitwidth
                        ),
                    };

                    let (op1_s_var, op1_e_var, op1_m_var) = setup_sem_aux_vars(
                        operand1,
                        "op1",
                        &mut self.ctx,
                        s_bit_count,
                        exp_bit_count,
                        mant_bit_count,
                        &mut air_constraints,
                    );
                    let (op2_s_var, op2_e_var, op2_m_var) = setup_sem_aux_vars(
                        operand2,
                        "op2_fmul",
                        &mut self.ctx,
                        s_bit_count,
                        exp_bit_count,
                        mant_bit_count,
                        &mut air_constraints,
                    );
                    let (res_s_var, res_e_var, res_m_var) = setup_sem_aux_vars(
                        lang::Operand::Var(result),
                        "res",
                        &mut self.ctx,
                        s_bit_count,
                        exp_bit_count,
                        mant_bit_count,
                        &mut air_constraints,
                    );

                    let op1_s_expr = AirExpression::Trace(op1_s_var, RowOffset::Current);
                    let op1_e_val_expr = AirExpression::Trace(op1_e_var, RowOffset::Current);
                    let op1_m_val_expr = AirExpression::Trace(op1_m_var, RowOffset::Current);

                    let op2_s_expr = AirExpression::Trace(op2_s_var, RowOffset::Current);
                    let op2_e_val_expr = AirExpression::Trace(op2_e_var, RowOffset::Current);
                    let op2_m_val_expr = AirExpression::Trace(op2_m_var, RowOffset::Current);

                    let res_s_expr = AirExpression::Trace(res_s_var, RowOffset::Current);
                    let res_e_val_expr = AirExpression::Trace(res_e_var, RowOffset::Current);
                    let res_m_val_expr = AirExpression::Trace(res_m_var, RowOffset::Current);

                    let op1_is_nan = fp_is_nan(
                        &op1_e_val_expr,
                        &op1_m_val_expr,
                        exp_bit_count,
                        mant_bit_count,
                        &mut self.ctx,
                        &mut air_constraints,
                        "op1_fmul",
                    );
                    let op2_is_nan = fp_is_nan(
                        &op2_e_val_expr,
                        &op2_m_val_expr,
                        exp_bit_count,
                        mant_bit_count,
                        &mut self.ctx,
                        &mut air_constraints,
                        "op2_fmul",
                    );

                    let op1_is_inf = fp_is_inf(
                        &op1_e_val_expr,
                        &op1_m_val_expr,
                        exp_bit_count,
                        mant_bit_count,
                        &mut self.ctx,
                        &mut air_constraints,
                        "op1_fmul",
                    );
                    let op2_is_inf = fp_is_inf(
                        &op2_e_val_expr,
                        &op2_m_val_expr,
                        exp_bit_count,
                        mant_bit_count,
                        &mut self.ctx,
                        &mut air_constraints,
                        "op2_fmul",
                    );

                    let op1_is_true_zero = fp_is_true_zero(
                        &op1_e_val_expr,
                        &op1_m_val_expr,
                        exp_bit_count,
                        mant_bit_count,
                        &mut self.ctx,
                        &mut air_constraints,
                        "op1_fmul",
                    );
                    let op2_is_true_zero = fp_is_true_zero(
                        &op2_e_val_expr,
                        &op2_m_val_expr,
                        exp_bit_count,
                        mant_bit_count,
                        &mut self.ctx,
                        &mut air_constraints,
                        "op2_fmul",
                    );

                    let qnan_sign = AirExpression::Constant(0);
                    let qnan_exp = AirExpression::Constant((1u128 << exp_bit_count) - 1);
                    let qnan_mant = AirExpression::Constant(1u128 << (mant_bit_count - 1));

                    let res_is_nan_due_to_op_nan = fp_logical_or(
                        &op1_is_nan,
                        &op2_is_nan,
                        &mut self.ctx,
                        &mut air_constraints,
                        "res_is_nan_from_op_fmul",
                    );

                    let op1_zero_op2_inf = fp_logical_and(
                        &op1_is_true_zero,
                        &op2_is_inf,
                        &mut self.ctx,
                        &mut air_constraints,
                        "op1z_op2inf_fmul",
                    );
                    let op1_inf_op2_zero = fp_logical_and(
                        &op1_is_inf,
                        &op2_is_true_zero,
                        &mut self.ctx,
                        &mut air_constraints,
                        "op1inf_op2z_fmul",
                    );
                    let res_is_nan_due_to_zero_inf = fp_logical_or(
                        &op1_zero_op2_inf,
                        &op1_inf_op2_zero,
                        &mut self.ctx,
                        &mut air_constraints,
                        "res_nan_zero_inf_fmul",
                    );

                    let final_res_is_nan = fp_logical_or(
                        &res_is_nan_due_to_op_nan,
                        &res_is_nan_due_to_zero_inf,
                        &mut self.ctx,
                        &mut air_constraints,
                        "final_res_is_nan_fmul",
                    );

                    let calculated_res_sign_if_not_nan = fp_icmp_neq(
                        &op1_s_expr,
                        &op2_s_expr,
                        &mut self.ctx,
                        &mut air_constraints,
                        "calc_res_sign_fmul",
                    );

                    let general_case_res_s_expr =
                        AirExpression::Trace(self.ctx.new_aux_variable(), RowOffset::Current);
                    let general_case_res_e_expr =
                        AirExpression::Trace(self.ctx.new_aux_variable(), RowOffset::Current);
                    let general_case_res_m_expr =
                        AirExpression::Trace(self.ctx.new_aux_variable(), RowOffset::Current);
                    air_constraints.push(AirExpression::Mul(
                        Box::new(general_case_res_s_expr.clone()),
                        Box::new(AirExpression::Sub(
                            Box::new(general_case_res_s_expr.clone()),
                            Box::new(AirExpression::Constant(1)),
                        )),
                    ));

                    let op1_is_inf_not_nan = fp_logical_and(
                        &op1_is_inf,
                        &fp_logical_not(
                            &op1_is_nan,
                            &mut self.ctx,
                            &mut air_constraints,
                            "op1_inf_nn_fmul",
                        ),
                        &mut self.ctx,
                        &mut air_constraints,
                        "op1_inf_not_nan_fmul",
                    );
                    let op2_is_inf_not_nan = fp_logical_and(
                        &op2_is_inf,
                        &fp_logical_not(
                            &op2_is_nan,
                            &mut self.ctx,
                            &mut air_constraints,
                            "op2_inf_nn_fmul",
                        ),
                        &mut self.ctx,
                        &mut air_constraints,
                        "op2_inf_not_nan_fmul",
                    );

                    let op1_is_finite_non_zero = fp_logical_and(
                        &fp_logical_not(
                            &op1_is_true_zero,
                            &mut self.ctx,
                            &mut air_constraints,
                            "op1_not_zero_for_fin_fmul",
                        ),
                        &fp_logical_not(
                            &op1_is_inf_not_nan,
                            &mut self.ctx,
                            &mut air_constraints,
                            "op1_not_inf_for_fin_fmul",
                        ),
                        &mut self.ctx,
                        &mut air_constraints,
                        "op1_is_fin_nz_fmul",
                    );
                    let op1_is_finite_non_zero = fp_logical_and(
                        &op1_is_finite_non_zero,
                        &fp_logical_not(
                            &op1_is_nan,
                            &mut self.ctx,
                            &mut air_constraints,
                            "op1_not_nan_for_fin_fmul",
                        ),
                        &mut self.ctx,
                        &mut air_constraints,
                        "op1_is_fin_nz_not_nan_fmul",
                    );

                    let op2_is_finite_non_zero = fp_logical_and(
                        &fp_logical_not(
                            &op2_is_true_zero,
                            &mut self.ctx,
                            &mut air_constraints,
                            "op2_not_zero_for_fin_fmul",
                        ),
                        &fp_logical_not(
                            &op2_is_inf_not_nan,
                            &mut self.ctx,
                            &mut air_constraints,
                            "op2_not_inf_for_fin_fmul",
                        ),
                        &mut self.ctx,
                        &mut air_constraints,
                        "op2_is_fin_nz_fmul",
                    );
                    let op2_is_finite_non_zero = fp_logical_and(
                        &op2_is_finite_non_zero,
                        &fp_logical_not(
                            &op2_is_nan,
                            &mut self.ctx,
                            &mut air_constraints,
                            "op2_not_nan_for_fin_fmul",
                        ),
                        &mut self.ctx,
                        &mut air_constraints,
                        "op2_is_fin_nz_not_nan_fmul",
                    );

                    let inf_x_inf = fp_logical_and(
                        &op1_is_inf_not_nan,
                        &op2_is_inf_not_nan,
                        &mut self.ctx,
                        &mut air_constraints,
                        "inf_x_inf_fmul",
                    );
                    let inf_x_finite = fp_logical_and(
                        &op1_is_inf_not_nan,
                        &op2_is_finite_non_zero,
                        &mut self.ctx,
                        &mut air_constraints,
                        "inf_x_finite_fmul",
                    );
                    let finite_x_inf = fp_logical_and(
                        &op1_is_finite_non_zero,
                        &op2_is_inf_not_nan,
                        &mut self.ctx,
                        &mut air_constraints,
                        "finite_x_inf_fmul",
                    );

                    let is_inf_result_scenario = fp_logical_or(
                        &inf_x_inf,
                        &inf_x_finite,
                        &mut self.ctx,
                        &mut air_constraints,
                        "is_inf_res_interim_fmul",
                    );
                    let is_inf_result_scenario = fp_logical_or(
                        &is_inf_result_scenario,
                        &finite_x_inf,
                        &mut self.ctx,
                        &mut air_constraints,
                        "is_inf_res_scenario_fmul",
                    );

                    let inter_res_s_if_inf = calculated_res_sign_if_not_nan.clone();
                    let inter_res_e_if_inf = qnan_exp.clone();
                    let inter_res_m_if_inf = AirExpression::Constant(0);

                    let op1_is_zero_not_special = fp_logical_and(
                        &op1_is_true_zero,
                        &fp_logical_not(
                            &op1_is_nan,
                            &mut self.ctx,
                            &mut air_constraints,
                            "op1_not_nan_z_fmul",
                        ),
                        &mut self.ctx,
                        &mut air_constraints,
                        "op1_zero_not_nan_fmul",
                    );
                    let op1_is_zero_not_special = fp_logical_and(
                        &op1_is_zero_not_special,
                        &fp_logical_not(
                            &op1_is_inf,
                            &mut self.ctx,
                            &mut air_constraints,
                            "op1_not_inf_z_fmul",
                        ),
                        &mut self.ctx,
                        &mut air_constraints,
                        "op1_zero_not_spec_fmul",
                    );

                    let op2_is_zero_not_special = fp_logical_and(
                        &op2_is_true_zero,
                        &fp_logical_not(
                            &op2_is_nan,
                            &mut self.ctx,
                            &mut air_constraints,
                            "op2_not_nan_z_fmul",
                        ),
                        &mut self.ctx,
                        &mut air_constraints,
                        "op2_zero_not_nan_fmul",
                    );
                    let op2_is_zero_not_special = fp_logical_and(
                        &op2_is_zero_not_special,
                        &fp_logical_not(
                            &op2_is_inf,
                            &mut self.ctx,
                            &mut air_constraints,
                            "op2_not_inf_z_fmul",
                        ),
                        &mut self.ctx,
                        &mut air_constraints,
                        "op2_zero_not_spec_fmul",
                    );

                    let op1_zero_op2_finite_not_inf_nan = fp_logical_and(
                        &op1_is_zero_not_special,
                        &fp_logical_not(
                            &op2_is_inf_not_nan,
                            &mut self.ctx,
                            &mut air_constraints,
                            "op2_nn_ni_for_z_fmul",
                        ),
                        &mut self.ctx,
                        &mut air_constraints,
                        "op1z_op2fin1_fmul",
                    );
                    let op1_zero_op2_finite_not_inf_nan = fp_logical_and(
                        &op1_zero_op2_finite_not_inf_nan,
                        &fp_logical_not(
                            &op2_is_nan,
                            &mut self.ctx,
                            &mut air_constraints,
                            "op1z_op2fin2_fmul",
                        ),
                        &mut self.ctx,
                        &mut air_constraints,
                        "op1z_op2fin_fmul",
                    );

                    let op2_zero_op1_finite_not_inf_nan = fp_logical_and(
                        &op2_is_zero_not_special,
                        &fp_logical_not(
                            &op1_is_inf_not_nan,
                            &mut self.ctx,
                            &mut air_constraints,
                            "op1_nn_ni_for_z_fmul",
                        ),
                        &mut self.ctx,
                        &mut air_constraints,
                        "op2z_op1fin1_fmul",
                    );
                    let op2_zero_op1_finite_not_inf_nan = fp_logical_and(
                        &op2_zero_op1_finite_not_inf_nan,
                        &fp_logical_not(
                            &op1_is_nan,
                            &mut self.ctx,
                            &mut air_constraints,
                            "op2z_op1fin2_fmul",
                        ),
                        &mut self.ctx,
                        &mut air_constraints,
                        "op2z_op1fin_fmul",
                    );
                    let is_zero_result_scenario = fp_logical_or(
                        &op1_zero_op2_finite_not_inf_nan,
                        &op2_zero_op1_finite_not_inf_nan,
                        &mut self.ctx,
                        &mut air_constraints,
                        "is_zero_res_scenario_fmul",
                    );

                    let inter_res_s_if_zero = calculated_res_sign_if_not_nan.clone();
                    let inter_res_e_if_zero = AirExpression::Constant(0);
                    let inter_res_m_if_zero = AirExpression::Constant(0);

                    let implicit_mant_bit_pos = mant_bit_count;
                    let all_ones_exp_biased = (1u128 << exp_bit_count) - 1;
                    let min_exp_biased_val = 1u128;
                    let zero_exp_biased_val = 0u128;
                    let bias_val = (1u128 << (exp_bit_count - 1)) - 1;

                    let op1_is_denormal = fp_is_value_equal(
                        &op1_e_val_expr,
                        &AirExpression::Constant(zero_exp_biased_val),
                        &mut self.ctx,
                        &mut air_constraints,
                        "op1_is_denorm_e_check_fmul",
                    );
                    let op2_is_denormal = fp_is_value_equal(
                        &op2_e_val_expr,
                        &AirExpression::Constant(zero_exp_biased_val),
                        &mut self.ctx,
                        &mut air_constraints,
                        "op2_is_denorm_e_check_fmul",
                    );

                    let implicit_bit_val_op1 = fp_logical_not(
                        &op1_is_denormal,
                        &mut self.ctx,
                        &mut air_constraints,
                        "op1_implicit_bit_fmul",
                    );
                    let implicit_bit_val_op2 = fp_logical_not(
                        &op2_is_denormal,
                        &mut self.ctx,
                        &mut air_constraints,
                        "op2_implicit_bit_fmul",
                    );

                    let full_significand_op1 = fp_add(
                        &op1_m_val_expr,
                        &fp_mul(
                            &implicit_bit_val_op1,
                            &AirExpression::Constant(1u128 << implicit_mant_bit_pos),
                            &mut self.ctx,
                            &mut air_constraints,
                            "op1_impl_shifted_fmul",
                        ),
                        &mut self.ctx,
                        &mut air_constraints,
                        "full_sig_op1_fmul",
                    );
                    let full_significand_op2 = fp_add(
                        &op2_m_val_expr,
                        &fp_mul(
                            &implicit_bit_val_op2,
                            &AirExpression::Constant(1u128 << implicit_mant_bit_pos),
                            &mut self.ctx,
                            &mut air_constraints,
                            "op2_impl_shifted_fmul",
                        ),
                        &mut self.ctx,
                        &mut air_constraints,
                        "full_sig_op2_fmul",
                    );

                    let effective_exp_op1 = fp_select(
                        &op1_is_denormal,
                        &AirExpression::Constant(min_exp_biased_val),
                        &op1_e_val_expr,
                        &mut self.ctx,
                        &mut air_constraints,
                        "eff_exp_op1_fmul",
                    );
                    let effective_exp_op2 = fp_select(
                        &op2_is_denormal,
                        &AirExpression::Constant(min_exp_biased_val),
                        &op2_e_val_expr,
                        &mut self.ctx,
                        &mut air_constraints,
                        "eff_exp_op2_fmul",
                    );

                    let unbiased_exp1 = fp_sub(
                        &effective_exp_op1,
                        &AirExpression::Constant(bias_val),
                        &mut self.ctx,
                        &mut air_constraints,
                        "unbiased_e1_fmul",
                    );
                    let unbiased_exp2 = fp_sub(
                        &effective_exp_op2,
                        &AirExpression::Constant(bias_val),
                        &mut self.ctx,
                        &mut air_constraints,
                        "unbiased_e2_fmul",
                    );
                    let sum_unbiased_exps = fp_add(
                        &unbiased_exp1,
                        &unbiased_exp2,
                        &mut self.ctx,
                        &mut air_constraints,
                        "sum_unbiased_exp_fmul",
                    );
                    let initial_biased_exp_for_norm = fp_add(
                        &sum_unbiased_exps,
                        &AirExpression::Constant(bias_val),
                        &mut self.ctx,
                        &mut air_constraints,
                        "init_biased_exp_fmul",
                    );

                    let significand_product = fp_mul(
                        &full_significand_op1,
                        &full_significand_op2,
                        &mut self.ctx,
                        &mut air_constraints,
                        "sig_prod_fmul",
                    );

                    let (
                        normalized_sign,
                        adjusted_biased_exp,
                        normalized_significand,
                        _is_true_zero_after_norm_round,
                    ) = fp_normalize_and_round_significand(
                        &significand_product,
                        &calculated_res_sign_if_not_nan,
                        &initial_biased_exp_for_norm,
                        &AirExpression::Constant(0),
                        &AirExpression::Constant(0),
                        &AirExpression::Constant(0),
                        mant_bit_count,
                        exp_bit_count,
                        &mut self.ctx,
                        &mut air_constraints,
                        "fmul_norm_round",
                    );

                    let exp_overflows = fp_icmp_ule(
                        &AirExpression::Constant(all_ones_exp_biased),
                        &adjusted_biased_exp,
                        exp_bit_count + 1,
                        &mut self.ctx,
                        &mut air_constraints,
                        "exp_overflows_fmul",
                    );
                    let exp_underflows_to_zero = fp_icmp_ule(
                        &adjusted_biased_exp,
                        &AirExpression::Constant(zero_exp_biased_val),
                        exp_bit_count + 1,
                        &mut self.ctx,
                        &mut air_constraints,
                        "exp_underflows_fmul",
                    );

                    let gen_case_s_val = normalized_sign.clone();
                    let gen_case_intermediate_e_val = fp_select(
                        &exp_underflows_to_zero,
                        &AirExpression::Constant(zero_exp_biased_val),
                        &adjusted_biased_exp,
                        &mut self.ctx,
                        &mut air_constraints,
                        "gen_e_undf_fmul",
                    );
                    let gen_case_e_val = fp_select(
                        &exp_overflows,
                        &AirExpression::Constant(all_ones_exp_biased),
                        &gen_case_intermediate_e_val,
                        &mut self.ctx,
                        &mut air_constraints,
                        "gen_e_ovf_fmul",
                    );

                    let gen_case_intermediate_m_val = fp_select(
                        &exp_underflows_to_zero,
                        &AirExpression::Constant(0),
                        &normalized_significand,
                        &mut self.ctx,
                        &mut air_constraints,
                        "gen_m_undf_fmul",
                    );
                    let gen_case_m_val = fp_select(
                        &exp_overflows,
                        &AirExpression::Constant(0),
                        &gen_case_intermediate_m_val,
                        &mut self.ctx,
                        &mut air_constraints,
                        "gen_m_ovf_fmul",
                    );

                    let res_s_if_not_inf = fp_select(
                        &is_zero_result_scenario,
                        &inter_res_s_if_zero,
                        &general_case_res_s_expr,
                        &mut self.ctx,
                        &mut air_constraints,
                        "s_not_inf_zero_vs_gen_fmul",
                    );
                    let res_e_if_not_inf = fp_select(
                        &is_zero_result_scenario,
                        &inter_res_e_if_zero,
                        &general_case_res_e_expr,
                        &mut self.ctx,
                        &mut air_constraints,
                        "e_not_inf_zero_vs_gen_fmul",
                    );
                    let res_m_if_not_inf = fp_select(
                        &is_zero_result_scenario,
                        &inter_res_m_if_zero,
                        &general_case_res_m_expr,
                        &mut self.ctx,
                        &mut air_constraints,
                        "m_not_inf_zero_vs_gen_fmul",
                    );

                    let res_s_if_not_nan = fp_select(
                        &is_inf_result_scenario,
                        &inter_res_s_if_inf,
                        &res_s_if_not_inf,
                        &mut self.ctx,
                        &mut air_constraints,
                        "s_not_nan_inf_vs_else_fmul",
                    );
                    let res_e_if_not_nan = fp_select(
                        &is_inf_result_scenario,
                        &inter_res_e_if_inf,
                        &res_e_if_not_inf,
                        &mut self.ctx,
                        &mut air_constraints,
                        "e_not_nan_inf_vs_else_fmul",
                    );
                    let res_m_if_not_nan = fp_select(
                        &is_inf_result_scenario,
                        &inter_res_m_if_inf,
                        &res_m_if_not_inf,
                        &mut self.ctx,
                        &mut air_constraints,
                        "m_not_nan_inf_vs_else_fmul",
                    );

                    let final_res_s_val = fp_select(
                        &final_res_is_nan,
                        &qnan_sign,
                        &res_s_if_not_nan,
                        &mut self.ctx,
                        &mut air_constraints,
                        "final_s_fmul",
                    );
                    let final_res_e_val = fp_select(
                        &final_res_is_nan,
                        &qnan_exp,
                        &res_e_if_not_nan,
                        &mut self.ctx,
                        &mut air_constraints,
                        "final_e_fmul",
                    );
                    let final_res_m_val = fp_select(
                        &final_res_is_nan,
                        &qnan_mant,
                        &res_m_if_not_nan,
                        &mut self.ctx,
                        &mut air_constraints,
                        "final_m_fmul",
                    );

                    air_constraints.push(AirExpression::Sub(
                        Box::new(res_s_expr),
                        Box::new(final_res_s_val),
                    ));
                    air_constraints.push(AirExpression::Sub(
                        Box::new(res_e_val_expr),
                        Box::new(final_res_e_val),
                    ));
                    air_constraints.push(AirExpression::Sub(
                        Box::new(res_m_val_expr),
                        Box::new(final_res_m_val),
                    ));

                    let not_final_nan_cond = fp_logical_not(
                        &final_res_is_nan,
                        &mut self.ctx,
                        &mut air_constraints,
                        "not_final_nan_for_gen_fmul",
                    );
                    let not_inf_res_cond = fp_logical_not(
                        &is_inf_result_scenario,
                        &mut self.ctx,
                        &mut air_constraints,
                        "not_inf_res_for_gen_fmul",
                    );
                    let not_zero_res_cond = fp_logical_not(
                        &is_zero_result_scenario,
                        &mut self.ctx,
                        &mut air_constraints,
                        "not_zero_res_for_gen_fmul",
                    );
                    let is_general_case_cond_pt1 = fp_logical_and(
                        &not_final_nan_cond,
                        &not_inf_res_cond,
                        &mut self.ctx,
                        &mut air_constraints,
                        "gen_case_pt1_fmul",
                    );
                    let is_general_case_condition = fp_logical_and(
                        &is_general_case_cond_pt1,
                        &not_zero_res_cond,
                        &mut self.ctx,
                        &mut air_constraints,
                        "is_general_case_fmul",
                    );

                    let gen_s_val_diff = fp_sub(
                        &general_case_res_s_expr,
                        &gen_case_s_val,
                        &mut self.ctx,
                        &mut air_constraints,
                        "gen_s_val_diff_fmul",
                    );
                    let gen_s_constraint = fp_mul(
                        &is_general_case_condition,
                        &gen_s_val_diff,
                        &mut self.ctx,
                        &mut air_constraints,
                        "gen_s_constr_mul_fmul",
                    );
                    air_constraints.push(gen_s_constraint);

                    let gen_e_val_diff = fp_sub(
                        &general_case_res_e_expr,
                        &gen_case_e_val,
                        &mut self.ctx,
                        &mut air_constraints,
                        "gen_e_val_diff_fmul",
                    );
                    let gen_e_constraint = fp_mul(
                        &is_general_case_condition,
                        &gen_e_val_diff,
                        &mut self.ctx,
                        &mut air_constraints,
                        "gen_e_constr_mul_fmul",
                    );
                    air_constraints.push(gen_e_constraint);

                    let gen_m_val_diff = fp_sub(
                        &general_case_res_m_expr,
                        &gen_case_m_val,
                        &mut self.ctx,
                        &mut air_constraints,
                        "gen_m_val_diff_fmul",
                    );
                    let gen_m_constraint = fp_mul(
                        &is_general_case_condition,
                        &gen_m_val_diff,
                        &mut self.ctx,
                        &mut air_constraints,
                        "gen_m_constr_mul_fmul",
                    );
                    air_constraints.push(gen_m_constraint);
                }
                StructuredAirConstraint::FDiv {
                    operand1,
                    operand2,
                    result,
                    operand_bitwidth,
                    block_name: _,
                } => {
                    println!(
                        "  FDIV: op1={:?}, op2={:?}, res={:?} (bitwidth {}) - Setting up S/E/M aux vars.",
                        operand1, operand2, result, operand_bitwidth
                    );

                    let (s_bit_count, exp_bit_count, mant_bit_count) = match operand_bitwidth {
                        16 => (1u32, 5u32, 10u32),
                        32 => (1u32, 8u32, 23u32),
                        64 => (1u32, 11u32, 52u32),
                        80 => (1u32, 15u32, 63u32),
                        128 => (1u32, 15u32, 112u32),
                        _ => panic!(
                            "Unsupported operand_bitwidth {} for FDiv S/E/M decomposition.",
                            operand_bitwidth
                        ),
                    };

                    let (op1_s_var, op1_e_var, op1_m_var) = setup_sem_aux_vars(
                        operand1,
                        "op1",
                        &mut self.ctx,
                        s_bit_count,
                        exp_bit_count,
                        mant_bit_count,
                        &mut air_constraints,
                    );
                    let (op2_s_var, op2_e_var, op2_m_var) = setup_sem_aux_vars(
                        operand2,
                        "op2_fdiv",
                        &mut self.ctx,
                        s_bit_count,
                        exp_bit_count,
                        mant_bit_count,
                        &mut air_constraints,
                    );
                    let (res_s_var, res_e_var, res_m_var) = setup_sem_aux_vars(
                        lang::Operand::Var(result),
                        "res",
                        &mut self.ctx,
                        s_bit_count,
                        exp_bit_count,
                        mant_bit_count,
                        &mut air_constraints,
                    );

                    let op1_s_expr = AirExpression::Trace(op1_s_var, RowOffset::Current);
                    let op1_e_val_expr = AirExpression::Trace(op1_e_var, RowOffset::Current);
                    let op1_m_val_expr = AirExpression::Trace(op1_m_var, RowOffset::Current);

                    let op2_s_expr = AirExpression::Trace(op2_s_var, RowOffset::Current);
                    let op2_e_val_expr = AirExpression::Trace(op2_e_var, RowOffset::Current);
                    let op2_m_val_expr = AirExpression::Trace(op2_m_var, RowOffset::Current);

                    let res_s_expr = AirExpression::Trace(res_s_var, RowOffset::Current);
                    let res_e_val_expr = AirExpression::Trace(res_e_var, RowOffset::Current);
                    let res_m_val_expr = AirExpression::Trace(res_m_var, RowOffset::Current);

                    let op1_is_nan = fp_is_nan(
                        &op1_e_val_expr,
                        &op1_m_val_expr,
                        exp_bit_count,
                        mant_bit_count,
                        &mut self.ctx,
                        &mut air_constraints,
                        "op1_fdiv",
                    );
                    let op2_is_nan = fp_is_nan(
                        &op2_e_val_expr,
                        &op2_m_val_expr,
                        exp_bit_count,
                        mant_bit_count,
                        &mut self.ctx,
                        &mut air_constraints,
                        "op2_fdiv",
                    );

                    let op1_is_inf = fp_is_inf(
                        &op1_e_val_expr,
                        &op1_m_val_expr,
                        exp_bit_count,
                        mant_bit_count,
                        &mut self.ctx,
                        &mut air_constraints,
                        "op1_fdiv",
                    );
                    let op2_is_inf = fp_is_inf(
                        &op2_e_val_expr,
                        &op2_m_val_expr,
                        exp_bit_count,
                        mant_bit_count,
                        &mut self.ctx,
                        &mut air_constraints,
                        "op2_fdiv",
                    );

                    let op1_is_true_zero = fp_is_true_zero(
                        &op1_e_val_expr,
                        &op1_m_val_expr,
                        exp_bit_count,
                        mant_bit_count,
                        &mut self.ctx,
                        &mut air_constraints,
                        "op1_fdiv",
                    );
                    let op2_is_true_zero = fp_is_true_zero(
                        &op2_e_val_expr,
                        &op2_m_val_expr,
                        exp_bit_count,
                        mant_bit_count,
                        &mut self.ctx,
                        &mut air_constraints,
                        "op2_fdiv",
                    );

                    let qnan_sign = AirExpression::Constant(0);
                    let qnan_exp = AirExpression::Constant((1u128 << exp_bit_count) - 1);
                    let qnan_mant = AirExpression::Constant(1u128 << (mant_bit_count - 1));

                    let res_is_nan_due_to_op_nan = fp_logical_or(
                        &op1_is_nan,
                        &op2_is_nan,
                        &mut self.ctx,
                        &mut air_constraints,
                        "res_is_nan_from_op_fdiv",
                    );

                    let op1_zero_op2_zero = fp_logical_and(
                        &op1_is_true_zero,
                        &op2_is_true_zero,
                        &mut self.ctx,
                        &mut air_constraints,
                        "op1z_op2z_fdiv",
                    );
                    let op1_inf_op2_inf = fp_logical_and(
                        &op1_is_inf,
                        &op2_is_inf,
                        &mut self.ctx,
                        &mut air_constraints,
                        "op1inf_op2inf_fdiv",
                    );
                    let res_is_nan_due_to_undef = fp_logical_or(
                        &op1_zero_op2_zero,
                        &op1_inf_op2_inf,
                        &mut self.ctx,
                        &mut air_constraints,
                        "res_nan_undef_fdiv",
                    );

                    let final_res_is_nan = fp_logical_or(
                        &res_is_nan_due_to_op_nan,
                        &res_is_nan_due_to_undef,
                        &mut self.ctx,
                        &mut air_constraints,
                        "final_res_is_nan_fdiv",
                    );

                    let calculated_res_sign_if_not_nan = fp_icmp_neq(
                        &op1_s_expr,
                        &op2_s_expr,
                        &mut self.ctx,
                        &mut air_constraints,
                        "calc_res_sign_fdiv",
                    );

                    let op1_is_finite_non_zero = fp_logical_and(
                        &fp_logical_not(
                            &op1_is_true_zero,
                            &mut self.ctx,
                            &mut air_constraints,
                            "op1_not_zero_for_fin_fdiv",
                        ),
                        &fp_logical_not(
                            &op1_is_inf,
                            &mut self.ctx,
                            &mut air_constraints,
                            "op1_not_inf_for_fin_fdiv",
                        ),
                        &mut self.ctx,
                        &mut air_constraints,
                        "op1_is_fin_nz_fdiv",
                    );
                    let op2_is_finite_non_zero = fp_logical_and(
                        &fp_logical_not(
                            &op2_is_true_zero,
                            &mut self.ctx,
                            &mut air_constraints,
                            "op2_not_zero_for_fin_fdiv",
                        ),
                        &fp_logical_not(
                            &op2_is_inf,
                            &mut self.ctx,
                            &mut air_constraints,
                            "op2_not_inf_for_fin_fdiv",
                        ),
                        &mut self.ctx,
                        &mut air_constraints,
                        "op2_is_fin_nz_fdiv",
                    );

                    let finite_div_zero = fp_logical_and(
                        &op1_is_finite_non_zero,
                        &op2_is_true_zero,
                        &mut self.ctx,
                        &mut air_constraints,
                        "fin_div_zero_fdiv",
                    );
                    let inf_div_finite = fp_logical_and(
                        &op1_is_inf,
                        &op2_is_finite_non_zero,
                        &mut self.ctx,
                        &mut air_constraints,
                        "inf_div_fin_fdiv",
                    );
                    let is_inf_result_scenario = fp_logical_or(
                        &finite_div_zero,
                        &inf_div_finite,
                        &mut self.ctx,
                        &mut air_constraints,
                        "is_inf_res_scenario_fdiv",
                    );

                    let inter_res_s_if_inf = calculated_res_sign_if_not_nan.clone();
                    let inter_res_e_if_inf = qnan_exp.clone();
                    let inter_res_m_if_inf = AirExpression::Constant(0);

                    let zero_div_finite = fp_logical_and(
                        &op1_is_true_zero,
                        &op2_is_finite_non_zero,
                        &mut self.ctx,
                        &mut air_constraints,
                        "zero_div_fin_fdiv",
                    );
                    let finite_div_inf = fp_logical_and(
                        &op1_is_finite_non_zero,
                        &op2_is_inf,
                        &mut self.ctx,
                        &mut air_constraints,
                        "fin_div_inf_fdiv",
                    );
                    let is_zero_result_scenario = fp_logical_or(
                        &zero_div_finite,
                        &finite_div_inf,
                        &mut self.ctx,
                        &mut air_constraints,
                        "is_zero_res_scenario_fdiv",
                    );

                    let inter_res_s_if_zero = calculated_res_sign_if_not_nan.clone();
                    let inter_res_e_if_zero = AirExpression::Constant(0);
                    let inter_res_m_if_zero = AirExpression::Constant(0);

                    let implicit_mant_bit_pos = mant_bit_count;
                    let all_ones_exp_biased = (1u128 << exp_bit_count) - 1;
                    let min_exp_biased_val = 1u128;
                    let zero_exp_biased_val = 0u128;
                    let bias_val = (1u128 << (exp_bit_count - 1)) - 1;

                    let res_is_denormal = fp_is_value_equal(
                        &res_e_val_expr,
                        &AirExpression::Constant(zero_exp_biased_val),
                        &mut self.ctx,
                        &mut air_constraints,
                        "res_is_denorm_e_check_fdiv",
                    );
                    let op2_is_denormal = fp_is_value_equal(
                        &op2_e_val_expr,
                        &AirExpression::Constant(zero_exp_biased_val),
                        &mut self.ctx,
                        &mut air_constraints,
                        "op2_is_denorm_e_check_fdiv",
                    );

                    let implicit_bit_val_res = fp_logical_not(
                        &res_is_denormal,
                        &mut self.ctx,
                        &mut air_constraints,
                        "res_implicit_bit_fdiv",
                    );
                    let implicit_bit_val_op2 = fp_logical_not(
                        &op2_is_denormal,
                        &mut self.ctx,
                        &mut air_constraints,
                        "op2_implicit_bit_fdiv",
                    );

                    let full_significand_res = fp_add(
                        &res_m_val_expr,
                        &fp_mul(
                            &implicit_bit_val_res,
                            &AirExpression::Constant(1u128 << implicit_mant_bit_pos),
                            &mut self.ctx,
                            &mut air_constraints,
                            "res_impl_shifted_fdiv",
                        ),
                        &mut self.ctx,
                        &mut air_constraints,
                        "full_sig_res_fdiv",
                    );
                    let full_significand_op2 = fp_add(
                        &op2_m_val_expr,
                        &fp_mul(
                            &implicit_bit_val_op2,
                            &AirExpression::Constant(1u128 << implicit_mant_bit_pos),
                            &mut self.ctx,
                            &mut air_constraints,
                            "op2_impl_shifted_fdiv",
                        ),
                        &mut self.ctx,
                        &mut air_constraints,
                        "full_sig_op2_fdiv",
                    );

                    let effective_exp_res = fp_select(
                        &res_is_denormal,
                        &AirExpression::Constant(min_exp_biased_val),
                        &res_e_val_expr,
                        &mut self.ctx,
                        &mut air_constraints,
                        "eff_exp_res_fdiv",
                    );
                    let effective_exp_op2 = fp_select(
                        &op2_is_denormal,
                        &AirExpression::Constant(min_exp_biased_val),
                        &op2_e_val_expr,
                        &mut self.ctx,
                        &mut air_constraints,
                        "eff_exp_op2_fdiv",
                    );

                    let unbiased_exp_res = fp_sub(
                        &effective_exp_res,
                        &AirExpression::Constant(bias_val),
                        &mut self.ctx,
                        &mut air_constraints,
                        "unbiased_eres_fdiv",
                    );
                    let unbiased_exp_op2 = fp_sub(
                        &effective_exp_op2,
                        &AirExpression::Constant(bias_val),
                        &mut self.ctx,
                        &mut air_constraints,
                        "unbiased_e2_fdiv",
                    );
                    let sum_unbiased_exps = fp_add(
                        &unbiased_exp_res,
                        &unbiased_exp_op2,
                        &mut self.ctx,
                        &mut air_constraints,
                        "sum_unbiased_exp_fdiv",
                    );
                    let initial_biased_exp_for_norm = fp_add(
                        &sum_unbiased_exps,
                        &AirExpression::Constant(bias_val),
                        &mut self.ctx,
                        &mut air_constraints,
                        "init_biased_exp_fdiv",
                    );

                    let significand_product = fp_mul(
                        &full_significand_res,
                        &full_significand_op2,
                        &mut self.ctx,
                        &mut air_constraints,
                        "sig_prod_fdiv",
                    );

                    let calculated_op1_sign = fp_icmp_neq(
                        &res_s_expr,
                        &op2_s_expr,
                        &mut self.ctx,
                        &mut air_constraints,
                        "calc_op1_sign_fdiv",
                    );

                    let (_normalized_sign, adjusted_biased_exp, normalized_significand, _) =
                        fp_normalize_and_round_significand(
                            &significand_product,
                            &calculated_op1_sign,
                            &initial_biased_exp_for_norm,
                            &AirExpression::Constant(0),
                            &AirExpression::Constant(0),
                            &AirExpression::Constant(0),
                            mant_bit_count,
                            exp_bit_count,
                            &mut self.ctx,
                            &mut air_constraints,
                            "fdiv_norm_round",
                        );

                    let exp_overflows = fp_icmp_ule(
                        &AirExpression::Constant(all_ones_exp_biased),
                        &adjusted_biased_exp,
                        exp_bit_count + 1,
                        &mut self.ctx,
                        &mut air_constraints,
                        "exp_overflows_fdiv",
                    );
                    let exp_underflows_to_zero = fp_icmp_ule(
                        &adjusted_biased_exp,
                        &AirExpression::Constant(zero_exp_biased_val),
                        exp_bit_count + 1,
                        &mut self.ctx,
                        &mut air_constraints,
                        "exp_underflows_fdiv",
                    );

                    let gen_case_op1_intermediate_e = fp_select(
                        &exp_underflows_to_zero,
                        &AirExpression::Constant(zero_exp_biased_val),
                        &adjusted_biased_exp,
                        &mut self.ctx,
                        &mut air_constraints,
                        "gen_op1_e_undf_fdiv",
                    );
                    let gen_case_op1_e = fp_select(
                        &exp_overflows,
                        &AirExpression::Constant(all_ones_exp_biased),
                        &gen_case_op1_intermediate_e,
                        &mut self.ctx,
                        &mut air_constraints,
                        "gen_op1_e_ovf_fdiv",
                    );

                    let gen_case_op1_intermediate_m = fp_select(
                        &exp_underflows_to_zero,
                        &AirExpression::Constant(0),
                        &normalized_significand,
                        &mut self.ctx,
                        &mut air_constraints,
                        "gen_op1_m_undf_fdiv",
                    );
                    let gen_case_op1_m = fp_select(
                        &exp_overflows,
                        &AirExpression::Constant(0),
                        &gen_case_op1_intermediate_m,
                        &mut self.ctx,
                        &mut air_constraints,
                        "gen_op1_m_ovf_fdiv",
                    );

                    let res_s_if_not_inf = fp_select(
                        &is_zero_result_scenario,
                        &inter_res_s_if_zero,
                        &res_s_expr,
                        &mut self.ctx,
                        &mut air_constraints,
                        "s_not_inf_zero_vs_gen_fdiv",
                    );
                    let res_e_if_not_inf = fp_select(
                        &is_zero_result_scenario,
                        &inter_res_e_if_zero,
                        &res_e_val_expr,
                        &mut self.ctx,
                        &mut air_constraints,
                        "e_not_inf_zero_vs_gen_fdiv",
                    );
                    let res_m_if_not_inf = fp_select(
                        &is_zero_result_scenario,
                        &inter_res_m_if_zero,
                        &res_m_val_expr,
                        &mut self.ctx,
                        &mut air_constraints,
                        "m_not_inf_zero_vs_gen_fdiv",
                    );

                    let res_s_if_not_nan = fp_select(
                        &is_inf_result_scenario,
                        &inter_res_s_if_inf,
                        &res_s_if_not_inf,
                        &mut self.ctx,
                        &mut air_constraints,
                        "s_not_nan_inf_vs_else_fdiv",
                    );
                    let res_e_if_not_nan = fp_select(
                        &is_inf_result_scenario,
                        &inter_res_e_if_inf,
                        &res_e_if_not_inf,
                        &mut self.ctx,
                        &mut air_constraints,
                        "e_not_nan_inf_vs_else_fdiv",
                    );
                    let res_m_if_not_nan = fp_select(
                        &is_inf_result_scenario,
                        &inter_res_m_if_inf,
                        &res_m_if_not_inf,
                        &mut self.ctx,
                        &mut air_constraints,
                        "m_not_nan_inf_vs_else_fdiv",
                    );

                    let final_res_s_val = fp_select(
                        &final_res_is_nan,
                        &qnan_sign,
                        &res_s_if_not_nan,
                        &mut self.ctx,
                        &mut air_constraints,
                        "final_s_fdiv",
                    );
                    let final_res_e_val = fp_select(
                        &final_res_is_nan,
                        &qnan_exp,
                        &res_e_if_not_nan,
                        &mut self.ctx,
                        &mut air_constraints,
                        "final_e_fdiv",
                    );
                    let final_res_m_val = fp_select(
                        &final_res_is_nan,
                        &qnan_mant,
                        &res_m_if_not_nan,
                        &mut self.ctx,
                        &mut air_constraints,
                        "final_m_fdiv",
                    );

                    air_constraints.push(AirExpression::Sub(
                        Box::new(res_s_expr.clone()),
                        Box::new(final_res_s_val),
                    ));
                    air_constraints.push(AirExpression::Sub(
                        Box::new(res_e_val_expr.clone()),
                        Box::new(final_res_e_val),
                    ));
                    air_constraints.push(AirExpression::Sub(
                        Box::new(res_m_val_expr.clone()),
                        Box::new(final_res_m_val),
                    ));

                    let not_final_nan_cond = fp_logical_not(
                        &final_res_is_nan,
                        &mut self.ctx,
                        &mut air_constraints,
                        "not_final_nan_for_gen_fdiv",
                    );
                    let not_inf_res_cond = fp_logical_not(
                        &is_inf_result_scenario,
                        &mut self.ctx,
                        &mut air_constraints,
                        "not_inf_res_for_gen_fdiv",
                    );
                    let not_zero_res_cond = fp_logical_not(
                        &is_zero_result_scenario,
                        &mut self.ctx,
                        &mut air_constraints,
                        "not_zero_res_for_gen_fdiv",
                    );
                    let is_general_case_cond_pt1 = fp_logical_and(
                        &not_final_nan_cond,
                        &not_inf_res_cond,
                        &mut self.ctx,
                        &mut air_constraints,
                        "gen_case_pt1_fdiv",
                    );
                    let is_general_case_condition = fp_logical_and(
                        &is_general_case_cond_pt1,
                        &not_zero_res_cond,
                        &mut self.ctx,
                        &mut air_constraints,
                        "is_general_case_fdiv",
                    );

                    let op1_s_diff = fp_sub(
                        &op1_s_expr,
                        &calculated_op1_sign,
                        &mut self.ctx,
                        &mut air_constraints,
                        "op1_s_diff_fdiv",
                    );
                    let op1_s_constraint = fp_mul(
                        &is_general_case_condition,
                        &op1_s_diff,
                        &mut self.ctx,
                        &mut air_constraints,
                        "op1_s_constr_fdiv",
                    );
                    air_constraints.push(op1_s_constraint);

                    let op1_e_diff = fp_sub(
                        &op1_e_val_expr,
                        &gen_case_op1_e,
                        &mut self.ctx,
                        &mut air_constraints,
                        "op1_e_diff_fdiv",
                    );
                    let op1_e_constraint = fp_mul(
                        &is_general_case_condition,
                        &op1_e_diff,
                        &mut self.ctx,
                        &mut air_constraints,
                        "op1_e_constr_fdiv",
                    );
                    air_constraints.push(op1_e_constraint);

                    let op1_m_diff = fp_sub(
                        &op1_m_val_expr,
                        &gen_case_op1_m,
                        &mut self.ctx,
                        &mut air_constraints,
                        "op1_m_diff_fdiv",
                    );
                    let op1_m_constraint = fp_mul(
                        &is_general_case_condition,
                        &op1_m_diff,
                        &mut self.ctx,
                        &mut air_constraints,
                        "op1_m_constr_fdiv",
                    );
                    air_constraints.push(op1_m_constraint);
                }
                StructuredAirConstraint::FRem {
                    operand1,
                    operand2,
                    result,
                    operand_bitwidth,
                    block_name: _,
                } => {
                    println!(
                        "  FREM: op1={:?}, op2={:?}, res={:?} (bitwidth {}) - Setting up S/E/M aux vars.",
                        operand1, operand2, result, operand_bitwidth
                    );

                    let (s_bit_count, exp_bit_count, mant_bit_count) = match operand_bitwidth {
                        16 => (1u32, 5u32, 10u32),
                        32 => (1u32, 8u32, 23u32),
                        64 => (1u32, 11u32, 52u32),
                        80 => (1u32, 15u32, 63u32),
                        128 => (1u32, 15u32, 112u32),
                        _ => panic!(
                            "Unsupported operand_bitwidth {} for FRem S/E/M decomposition.",
                            operand_bitwidth
                        ),
                    };

                    let (op1_s_var, op1_e_var, op1_m_var) = setup_sem_aux_vars(
                        operand1,
                        "op1_frem",
                        &mut self.ctx,
                        s_bit_count,
                        exp_bit_count,
                        mant_bit_count,
                        &mut air_constraints,
                    );
                    let (_op2_s_var, op2_e_var, op2_m_var) = setup_sem_aux_vars(
                        operand2,
                        "op2_frem",
                        &mut self.ctx,
                        s_bit_count,
                        exp_bit_count,
                        mant_bit_count,
                        &mut air_constraints,
                    );
                    let (res_s_var, res_e_var, res_m_var) = setup_sem_aux_vars(
                        lang::Operand::Var(result),
                        "res_frem",
                        &mut self.ctx,
                        s_bit_count,
                        exp_bit_count,
                        mant_bit_count,
                        &mut air_constraints,
                    );

                    let op1_s_expr = AirExpression::Trace(op1_s_var, RowOffset::Current);
                    let op1_e_val_expr = AirExpression::Trace(op1_e_var, RowOffset::Current);
                    let op1_m_val_expr = AirExpression::Trace(op1_m_var, RowOffset::Current);

                    let op2_e_val_expr = AirExpression::Trace(op2_e_var, RowOffset::Current);
                    let op2_m_val_expr = AirExpression::Trace(op2_m_var, RowOffset::Current);

                    let res_s_expr = AirExpression::Trace(res_s_var, RowOffset::Current);
                    let res_e_val_expr = AirExpression::Trace(res_e_var, RowOffset::Current);
                    let res_m_val_expr = AirExpression::Trace(res_m_var, RowOffset::Current);

                    let op1_is_nan = fp_is_nan(
                        &op1_e_val_expr,
                        &op1_m_val_expr,
                        exp_bit_count,
                        mant_bit_count,
                        &mut self.ctx,
                        &mut air_constraints,
                        "op1_frem",
                    );
                    let op2_is_nan = fp_is_nan(
                        &op2_e_val_expr,
                        &op2_m_val_expr,
                        exp_bit_count,
                        mant_bit_count,
                        &mut self.ctx,
                        &mut air_constraints,
                        "op2_frem",
                    );

                    let op1_is_inf = fp_is_inf(
                        &op1_e_val_expr,
                        &op1_m_val_expr,
                        exp_bit_count,
                        mant_bit_count,
                        &mut self.ctx,
                        &mut air_constraints,
                        "op1_frem",
                    );
                    let op2_is_inf = fp_is_inf(
                        &op2_e_val_expr,
                        &op2_m_val_expr,
                        exp_bit_count,
                        mant_bit_count,
                        &mut self.ctx,
                        &mut air_constraints,
                        "op2_frem",
                    );

                    let op1_is_true_zero = fp_is_true_zero(
                        &op1_e_val_expr,
                        &op1_m_val_expr,
                        exp_bit_count,
                        mant_bit_count,
                        &mut self.ctx,
                        &mut air_constraints,
                        "op1_frem",
                    );
                    let op2_is_true_zero = fp_is_true_zero(
                        &op2_e_val_expr,
                        &op2_m_val_expr,
                        exp_bit_count,
                        mant_bit_count,
                        &mut self.ctx,
                        &mut air_constraints,
                        "op2_frem",
                    );

                    let qnan_sign = AirExpression::Constant(0);
                    let qnan_exp = AirExpression::Constant((1u128 << exp_bit_count) - 1);
                    let qnan_mant = AirExpression::Constant(1u128 << (mant_bit_count - 1));

                    let res_is_nan_from_op = fp_logical_or(
                        &op1_is_nan,
                        &op2_is_nan,
                        &mut self.ctx,
                        &mut air_constraints,
                        "res_nan_from_op_frem",
                    );

                    let res_is_nan_undef = fp_logical_or(
                        &op1_is_inf,
                        &op2_is_true_zero,
                        &mut self.ctx,
                        &mut air_constraints,
                        "res_nan_undef_frem",
                    );
                    let final_res_is_nan = fp_logical_or(
                        &res_is_nan_from_op,
                        &res_is_nan_undef,
                        &mut self.ctx,
                        &mut air_constraints,
                        "final_res_is_nan_frem",
                    );

                    let op1_is_finite = fp_logical_not(
                        &fp_logical_or(
                            &op1_is_nan,
                            &op1_is_inf,
                            &mut self.ctx,
                            &mut air_constraints,
                            "op1_nan_or_inf_frem",
                        ),
                        &mut self.ctx,
                        &mut air_constraints,
                        "op1_is_finite_frem",
                    );
                    let is_op1_result_scenario = fp_logical_and(
                        &op1_is_finite,
                        &op2_is_inf,
                        &mut self.ctx,
                        &mut air_constraints,
                        "is_op1_res_scenario_frem",
                    );

                    let is_zero_result_scenario = op1_is_true_zero.clone();

                    let inter_res_s_if_op1 = op1_s_expr.clone();
                    let inter_res_e_if_op1 = op1_e_val_expr.clone();
                    let inter_res_m_if_op1 = op1_m_val_expr.clone();

                    let inter_res_s_if_zero = op1_s_expr.clone();
                    let inter_res_e_if_zero = AirExpression::Constant(0);
                    let inter_res_m_if_zero = AirExpression::Constant(0);

                    let res_s_if_not_nan = fp_select(
                        &is_op1_result_scenario,
                        &inter_res_s_if_op1,
                        &res_s_expr,
                        &mut self.ctx,
                        &mut air_constraints,
                        "s_not_nan_op1_vs_else_frem",
                    );
                    let res_e_if_not_nan = fp_select(
                        &is_op1_result_scenario,
                        &inter_res_e_if_op1,
                        &res_e_val_expr,
                        &mut self.ctx,
                        &mut air_constraints,
                        "e_not_nan_op1_vs_else_frem",
                    );
                    let res_m_if_not_nan = fp_select(
                        &is_op1_result_scenario,
                        &inter_res_m_if_op1,
                        &res_m_val_expr,
                        &mut self.ctx,
                        &mut air_constraints,
                        "m_not_nan_op1_vs_else_frem",
                    );

                    let res_s_if_not_nan_zero = fp_select(
                        &is_zero_result_scenario,
                        &inter_res_s_if_zero,
                        &res_s_if_not_nan,
                        &mut self.ctx,
                        &mut air_constraints,
                        "s_not_nan_zero_vs_else_frem",
                    );
                    let res_e_if_not_nan_zero = fp_select(
                        &is_zero_result_scenario,
                        &inter_res_e_if_zero,
                        &res_e_if_not_nan,
                        &mut self.ctx,
                        &mut air_constraints,
                        "e_not_nan_zero_vs_else_frem",
                    );
                    let res_m_if_not_nan_zero = fp_select(
                        &is_zero_result_scenario,
                        &inter_res_m_if_zero,
                        &res_m_if_not_nan,
                        &mut self.ctx,
                        &mut air_constraints,
                        "m_not_nan_zero_vs_else_frem",
                    );

                    let final_res_s_val = fp_select(
                        &final_res_is_nan,
                        &qnan_sign,
                        &res_s_if_not_nan_zero,
                        &mut self.ctx,
                        &mut air_constraints,
                        "final_s_frem",
                    );
                    let final_res_e_val = fp_select(
                        &final_res_is_nan,
                        &qnan_exp,
                        &res_e_if_not_nan_zero,
                        &mut self.ctx,
                        &mut air_constraints,
                        "final_e_frem",
                    );
                    let final_res_m_val = fp_select(
                        &final_res_is_nan,
                        &qnan_mant,
                        &res_m_if_not_nan_zero,
                        &mut self.ctx,
                        &mut air_constraints,
                        "final_m_frem",
                    );

                    air_constraints.push(AirExpression::Sub(
                        Box::new(res_s_expr.clone()),
                        Box::new(final_res_s_val),
                    ));
                    air_constraints.push(AirExpression::Sub(
                        Box::new(res_e_val_expr.clone()),
                        Box::new(final_res_e_val),
                    ));
                    air_constraints.push(AirExpression::Sub(
                        Box::new(res_m_val_expr.clone()),
                        Box::new(final_res_m_val),
                    ));

                    let not_final_nan_cond = fp_logical_not(
                        &final_res_is_nan,
                        &mut self.ctx,
                        &mut air_constraints,
                        "not_final_nan_for_gen_frem",
                    );
                    let not_op1_res_cond = fp_logical_not(
                        &is_op1_result_scenario,
                        &mut self.ctx,
                        &mut air_constraints,
                        "not_op1_res_for_gen_frem",
                    );
                    let not_zero_res_cond = fp_logical_not(
                        &is_zero_result_scenario,
                        &mut self.ctx,
                        &mut air_constraints,
                        "not_zero_res_for_gen_frem",
                    );
                    let is_general_case_cond_pt1 = fp_logical_and(
                        &not_final_nan_cond,
                        &not_op1_res_cond,
                        &mut self.ctx,
                        &mut air_constraints,
                        "gen_case_pt1_frem",
                    );
                    let is_general_case_condition = fp_logical_and(
                        &is_general_case_cond_pt1,
                        &not_zero_res_cond,
                        &mut self.ctx,
                        &mut air_constraints,
                        "is_general_case_frem",
                    );

                    let sign_diff = fp_sub(
                        &res_s_expr,
                        &op1_s_expr,
                        &mut self.ctx,
                        &mut air_constraints,
                        "sign_diff_frem",
                    );
                    let sign_constraint = fp_mul(
                        &is_general_case_condition,
                        &sign_diff,
                        &mut self.ctx,
                        &mut air_constraints,
                        "sign_constr_frem",
                    );
                    air_constraints.push(sign_constraint);

                    let rem_abs_val = fp_add(
                        &fp_mul(
                            &res_e_val_expr,
                            &AirExpression::Constant(1u128 << mant_bit_count),
                            &mut self.ctx,
                            &mut air_constraints,
                            "rem_e_shifted_frem",
                        ),
                        &res_m_val_expr,
                        &mut self.ctx,
                        &mut air_constraints,
                        "rem_abs_val_frem",
                    );
                    let op2_abs_val = fp_add(
                        &fp_mul(
                            &op2_e_val_expr,
                            &AirExpression::Constant(1u128 << mant_bit_count),
                            &mut self.ctx,
                            &mut air_constraints,
                            "op2_e_shifted_frem",
                        ),
                        &op2_m_val_expr,
                        &mut self.ctx,
                        &mut air_constraints,
                        "op2_abs_val_frem",
                    );

                    let abs_rem_lt_abs_op2 = fp_icmp_ult(
                        &rem_abs_val,
                        &op2_abs_val,
                        mant_bit_count + exp_bit_count,
                        &mut self.ctx,
                        &mut air_constraints,
                        "abs_rem_lt_abs_op2_frem",
                    );
                    let lt_check_diff = fp_sub(
                        &abs_rem_lt_abs_op2,
                        &AirExpression::Constant(1),
                        &mut self.ctx,
                        &mut air_constraints,
                        "lt_check_diff_frem",
                    );
                    let lt_constraint = fp_mul(
                        &is_general_case_condition,
                        &lt_check_diff,
                        &mut self.ctx,
                        &mut air_constraints,
                        "lt_constr_frem",
                    );
                    air_constraints.push(lt_constraint);
                }
                StructuredAirConstraint::FNeg {
                    operand,
                    result,
                    operand_bitwidth,
                    block_name: _,
                } => {
                    println!(
                        "  FNEG: op={:?}, res={:?} (bitwidth {}) - Setting up S/E/M aux vars.",
                        operand, result, operand_bitwidth
                    );

                    let (s_bit_count, exp_bit_count, mant_bit_count) = match operand_bitwidth {
                        16 => (1u32, 5u32, 10u32),
                        32 => (1u32, 8u32, 23u32),
                        64 => (1u32, 11u32, 52u32),
                        80 => (1u32, 15u32, 63u32),
                        128 => (1u32, 15u32, 112u32),
                        _ => panic!(
                            "Unsupported operand_bitwidth {} for FNeg S/E/M decomposition.",
                            operand_bitwidth
                        ),
                    };

                    let (op_s_var, op_e_var, op_m_var) = setup_sem_aux_vars(
                        operand,
                        "op_fneg",
                        &mut self.ctx,
                        s_bit_count,
                        exp_bit_count,
                        mant_bit_count,
                        &mut air_constraints,
                    );
                    let (res_s_var, res_e_var, res_m_var) = setup_sem_aux_vars(
                        lang::Operand::Var(result),
                        "res_fneg",
                        &mut self.ctx,
                        s_bit_count,
                        exp_bit_count,
                        mant_bit_count,
                        &mut air_constraints,
                    );

                    let op_s_expr = AirExpression::Trace(op_s_var, RowOffset::Current);
                    let op_e_expr = AirExpression::Trace(op_e_var, RowOffset::Current);
                    let op_m_expr = AirExpression::Trace(op_m_var, RowOffset::Current);

                    let res_s_expr = AirExpression::Trace(res_s_var, RowOffset::Current);
                    let res_e_expr = AirExpression::Trace(res_e_var, RowOffset::Current);
                    let res_m_expr = AirExpression::Trace(res_m_var, RowOffset::Current);

                    let flipped_sign = AirExpression::Sub(
                        Box::new(AirExpression::Constant(1)),
                        Box::new(op_s_expr),
                    );
                    air_constraints.push(AirExpression::Sub(
                        Box::new(res_s_expr),
                        Box::new(flipped_sign),
                    ));

                    air_constraints.push(AirExpression::Sub(
                        Box::new(res_e_expr),
                        Box::new(op_e_expr),
                    ));

                    air_constraints.push(AirExpression::Sub(
                        Box::new(res_m_expr),
                        Box::new(op_m_expr),
                    ));
                }
                StructuredAirConstraint::FCmp {
                    cond,
                    operand1,
                    operand2,
                    result,
                    operand_bitwidth,
                    block_name: _,
                } => {
                    let (s_bit_count, exp_bit_count, mant_bit_count) = match operand_bitwidth {
                        16 => (1, 5, 10),
                        32 => (1, 8, 23),
                        64 => (1, 11, 52),
                        _ => panic!("Unsupported operand_bitwidth {} for FCmp", operand_bitwidth),
                    };

                    let (op1_s_var, op1_e_var, op1_m_var) = setup_sem_aux_vars(
                        operand1,
                        "op1_fcmp",
                        &mut self.ctx,
                        s_bit_count,
                        exp_bit_count,
                        mant_bit_count,
                        &mut air_constraints,
                    );
                    let (op2_s_var, op2_e_var, op2_m_var) = setup_sem_aux_vars(
                        operand2,
                        "op2_fcmp",
                        &mut self.ctx,
                        s_bit_count,
                        exp_bit_count,
                        mant_bit_count,
                        &mut air_constraints,
                    );

                    let op1_s_expr = AirExpression::Trace(op1_s_var, RowOffset::Current);
                    let op1_e_expr = AirExpression::Trace(op1_e_var, RowOffset::Current);
                    let op1_m_expr = AirExpression::Trace(op1_m_var, RowOffset::Current);

                    let op2_s_expr = AirExpression::Trace(op2_s_var, RowOffset::Current);
                    let op2_e_expr = AirExpression::Trace(op2_e_var, RowOffset::Current);
                    let op2_m_expr = AirExpression::Trace(op2_m_var, RowOffset::Current);

                    let res_air_var = AirTraceVariable(result.0);
                    let res_expr = AirExpression::Trace(res_air_var, RowOffset::Current);

                    air_constraints.push(AirExpression::Mul(
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
                        &mut self.ctx,
                        &mut air_constraints,
                        "op1_fcmp_nan",
                    );
                    let op2_is_nan = fp_is_nan(
                        &op2_e_expr,
                        &op2_m_expr,
                        exp_bit_count,
                        mant_bit_count,
                        &mut self.ctx,
                        &mut air_constraints,
                        "op2_fcmp_nan",
                    );

                    let op1_is_inf = fp_is_inf(
                        &op1_e_expr,
                        &op1_m_expr,
                        exp_bit_count,
                        mant_bit_count,
                        &mut self.ctx,
                        &mut air_constraints,
                        "op1_fcmp_inf",
                    );
                    let op2_is_inf = fp_is_inf(
                        &op2_e_expr,
                        &op2_m_expr,
                        exp_bit_count,
                        mant_bit_count,
                        &mut self.ctx,
                        &mut air_constraints,
                        "op2_fcmp_inf",
                    );

                    let op1_is_true_zero = fp_is_true_zero(
                        &op1_e_expr,
                        &op1_m_expr,
                        exp_bit_count,
                        mant_bit_count,
                        &mut self.ctx,
                        &mut air_constraints,
                        "op1_fcmp_zero",
                    );
                    let op2_is_true_zero = fp_is_true_zero(
                        &op2_e_expr,
                        &op2_m_expr,
                        exp_bit_count,
                        mant_bit_count,
                        &mut self.ctx,
                        &mut air_constraints,
                        "op2_fcmp_zero",
                    );

                    let is_uno = fp_logical_or(
                        &op1_is_nan,
                        &op2_is_nan,
                        &mut self.ctx,
                        &mut air_constraints,
                        "is_uno_fcmp",
                    );
                    let is_ord =
                        fp_logical_not(&is_uno, &mut self.ctx, &mut air_constraints, "is_ord_fcmp");

                    let signs_eq = fp_icmp_eq(
                        &op1_s_expr,
                        &op2_s_expr,
                        &mut self.ctx,
                        &mut air_constraints,
                        "signs_eq_fcmp",
                    );
                    let exps_eq = fp_icmp_eq(
                        &op1_e_expr,
                        &op2_e_expr,
                        &mut self.ctx,
                        &mut air_constraints,
                        "exps_eq_fcmp",
                    );
                    let mants_eq = fp_icmp_eq(
                        &op1_m_expr,
                        &op2_m_expr,
                        &mut self.ctx,
                        &mut air_constraints,
                        "mants_eq_fcmp",
                    );

                    let same_sem = fp_logical_and(
                        &signs_eq,
                        &fp_logical_and(
                            &exps_eq,
                            &mants_eq,
                            &mut self.ctx,
                            &mut air_constraints,
                            "em_eq_fcmp",
                        ),
                        &mut self.ctx,
                        &mut air_constraints,
                        "sem_eq_fcmp",
                    );
                    let both_zero = fp_logical_and(
                        &op1_is_true_zero,
                        &op2_is_true_zero,
                        &mut self.ctx,
                        &mut air_constraints,
                        "both_zero_fcmp",
                    );
                    let are_equal_if_not_inf = fp_logical_or(
                        &same_sem,
                        &both_zero,
                        &mut self.ctx,
                        &mut air_constraints,
                        "are_equal_not_inf_fcmp",
                    );

                    let both_inf = fp_logical_and(
                        &op1_is_inf,
                        &op2_is_inf,
                        &mut self.ctx,
                        &mut air_constraints,
                        "both_inf_fcmp",
                    );
                    let both_inf_and_signs_eq = fp_logical_and(
                        &both_inf,
                        &signs_eq,
                        &mut self.ctx,
                        &mut air_constraints,
                        "both_inf_eq_fcmp",
                    );

                    let are_equal_ord = fp_select(
                        &op1_is_inf,
                        &both_inf_and_signs_eq,
                        &are_equal_if_not_inf,
                        &mut self.ctx,
                        &mut air_constraints,
                        "are_equal_ord_fcmp",
                    );

                    let op1_is_neg = fp_icmp_eq(
                        &op1_s_expr,
                        &AirExpression::Constant(1),
                        &mut self.ctx,
                        &mut air_constraints,
                        "op1_neg_fcmp",
                    );
                    let op2_is_neg = fp_icmp_eq(
                        &op2_s_expr,
                        &AirExpression::Constant(1),
                        &mut self.ctx,
                        &mut air_constraints,
                        "op2_neg_fcmp",
                    );
                    let op1_is_pos = fp_logical_not(
                        &op1_is_neg,
                        &mut self.ctx,
                        &mut air_constraints,
                        "op1_pos_fcmp",
                    );
                    let op2_is_pos = fp_logical_not(
                        &op2_is_neg,
                        &mut self.ctx,
                        &mut air_constraints,
                        "op2_pos_fcmp",
                    );

                    let op1_neg_op2_pos = fp_logical_and(
                        &op1_is_neg,
                        &op2_is_pos,
                        &mut self.ctx,
                        &mut air_constraints,
                        "op1_neg_op2_pos_fcmp",
                    );

                    let op1_exp_lt_op2_exp = fp_icmp_ult(
                        &op1_e_expr,
                        &op2_e_expr,
                        exp_bit_count,
                        &mut self.ctx,
                        &mut air_constraints,
                        "op1_exp_lt_fcmp",
                    );
                    let op1_mant_lt_op2_mant = fp_icmp_ult(
                        &op1_m_expr,
                        &op2_m_expr,
                        mant_bit_count,
                        &mut self.ctx,
                        &mut air_constraints,
                        "op1_mant_lt_fcmp",
                    );
                    let exp_eq_mant_lt = fp_logical_and(
                        &exps_eq,
                        &op1_mant_lt_op2_mant,
                        &mut self.ctx,
                        &mut air_constraints,
                        "exp_eq_mant_lt_fcmp",
                    );
                    let lt_if_pos_signed = fp_logical_or(
                        &op1_exp_lt_op2_exp,
                        &exp_eq_mant_lt,
                        &mut self.ctx,
                        &mut air_constraints,
                        "lt_if_pos_signed_fcmp",
                    );

                    let op2_exp_lt_op1_exp = fp_icmp_ult(
                        &op2_e_expr,
                        &op1_e_expr,
                        exp_bit_count,
                        &mut self.ctx,
                        &mut air_constraints,
                        "op2_exp_lt_fcmp",
                    );
                    let op2_mant_lt_op1_mant = fp_icmp_ult(
                        &op2_m_expr,
                        &op1_m_expr,
                        mant_bit_count,
                        &mut self.ctx,
                        &mut air_constraints,
                        "op2_mant_lt_fcmp",
                    );
                    let exp_eq_mant_gt = fp_logical_and(
                        &exps_eq,
                        &op2_mant_lt_op1_mant,
                        &mut self.ctx,
                        &mut air_constraints,
                        "exp_eq_mant_gt_fcmp",
                    );
                    let lt_if_neg_signed = fp_logical_or(
                        &op2_exp_lt_op1_exp,
                        &exp_eq_mant_gt,
                        &mut self.ctx,
                        &mut air_constraints,
                        "lt_if_neg_signed_fcmp",
                    );

                    let same_sign_pos = fp_logical_and(
                        &signs_eq,
                        &op1_is_pos,
                        &mut self.ctx,
                        &mut air_constraints,
                        "ss_pos_fcmp",
                    );
                    let same_sign_neg = fp_logical_and(
                        &signs_eq,
                        &op1_is_neg,
                        &mut self.ctx,
                        &mut air_constraints,
                        "ss_neg_fcmp",
                    );

                    let same_sign_lt = fp_logical_or(
                        &fp_logical_and(
                            &same_sign_pos,
                            &lt_if_pos_signed,
                            &mut self.ctx,
                            &mut air_constraints,
                            "ss_pos_lt_fcmp",
                        ),
                        &fp_logical_and(
                            &same_sign_neg,
                            &lt_if_neg_signed,
                            &mut self.ctx,
                            &mut air_constraints,
                            "ss_neg_lt_fcmp",
                        ),
                        &mut self.ctx,
                        &mut air_constraints,
                        "same_sign_lt_fcmp",
                    );

                    let lt_if_normal_numbers = fp_logical_or(
                        &op1_neg_op2_pos,
                        &same_sign_lt,
                        &mut self.ctx,
                        &mut air_constraints,
                        "lt_if_normal_fcmp",
                    );

                    let op1_is_neg_inf = fp_logical_and(
                        &op1_is_inf,
                        &op1_is_neg,
                        &mut self.ctx,
                        &mut air_constraints,
                        "op1_neg_inf_fcmp",
                    );
                    let op2_is_neg_inf = fp_logical_and(
                        &op2_is_inf,
                        &op2_is_neg,
                        &mut self.ctx,
                        &mut air_constraints,
                        "op2_neg_inf_fcmp",
                    );
                    let op1_is_pos_inf = fp_logical_and(
                        &op1_is_inf,
                        &op1_is_pos,
                        &mut self.ctx,
                        &mut air_constraints,
                        "op1_pos_inf_fcmp",
                    );
                    let op2_is_pos_inf = fp_logical_and(
                        &op2_is_inf,
                        &op2_is_pos,
                        &mut self.ctx,
                        &mut air_constraints,
                        "op2_pos_inf_fcmp",
                    );

                    let case1_lt_inf = fp_logical_and(
                        &op1_is_neg_inf,
                        &fp_logical_not(
                            &op2_is_neg_inf,
                            &mut self.ctx,
                            &mut air_constraints,
                            "not_op2_neg_inf",
                        ),
                        &mut self.ctx,
                        &mut air_constraints,
                        "lt_op1_neg_inf",
                    );
                    let case2_lt_inf = fp_logical_and(
                        &op2_is_pos_inf,
                        &fp_logical_not(
                            &op1_is_pos_inf,
                            &mut self.ctx,
                            &mut air_constraints,
                            "not_op1_pos_inf",
                        ),
                        &mut self.ctx,
                        &mut air_constraints,
                        "lt_op2_pos_inf",
                    );
                    let is_lt_due_to_inf = fp_logical_or(
                        &case1_lt_inf,
                        &case2_lt_inf,
                        &mut self.ctx,
                        &mut air_constraints,
                        "is_lt_due_to_inf",
                    );

                    let is_lt_ord = fp_select(
                        &fp_logical_or(
                            &op1_is_inf,
                            &op2_is_inf,
                            &mut self.ctx,
                            &mut air_constraints,
                            "any_inf",
                        ),
                        &is_lt_due_to_inf,
                        &lt_if_normal_numbers,
                        &mut self.ctx,
                        &mut air_constraints,
                        "is_lt_ord_fcmp",
                    );

                    let is_gt_ord = fp_logical_and(
                        &is_ord,
                        &fp_logical_not(
                            &fp_logical_or(
                                &is_lt_ord,
                                &are_equal_ord,
                                &mut self.ctx,
                                &mut air_constraints,
                                "lt_or_eq_ord",
                            ),
                            &mut self.ctx,
                            &mut air_constraints,
                            "not_lt_or_eq_ord",
                        ),
                        &mut self.ctx,
                        &mut air_constraints,
                        "is_gt_ord_fcmp",
                    );

                    let final_res = match cond {
                        FloatPredicate::OEQ => fp_logical_and(
                            &is_ord,
                            &are_equal_ord,
                            &mut self.ctx,
                            &mut air_constraints,
                            "res_oeq",
                        ),
                        FloatPredicate::ONE => fp_logical_and(
                            &is_ord,
                            &fp_logical_not(
                                &are_equal_ord,
                                &mut self.ctx,
                                &mut air_constraints,
                                "not_are_equal_ord",
                            ),
                            &mut self.ctx,
                            &mut air_constraints,
                            "res_one",
                        ),
                        FloatPredicate::OGT => fp_logical_and(
                            &is_ord,
                            &is_gt_ord,
                            &mut self.ctx,
                            &mut air_constraints,
                            "res_ogt",
                        ),
                        FloatPredicate::OGE => fp_logical_and(
                            &is_ord,
                            &fp_logical_or(
                                &is_gt_ord,
                                &are_equal_ord,
                                &mut self.ctx,
                                &mut air_constraints,
                                "oge_cond",
                            ),
                            &mut self.ctx,
                            &mut air_constraints,
                            "res_oge",
                        ),
                        FloatPredicate::OLT => fp_logical_and(
                            &is_ord,
                            &is_lt_ord,
                            &mut self.ctx,
                            &mut air_constraints,
                            "res_olt",
                        ),
                        FloatPredicate::OLE => fp_logical_and(
                            &is_ord,
                            &fp_logical_or(
                                &is_lt_ord,
                                &are_equal_ord,
                                &mut self.ctx,
                                &mut air_constraints,
                                "ole_cond",
                            ),
                            &mut self.ctx,
                            &mut air_constraints,
                            "res_ole",
                        ),
                        FloatPredicate::ORD => is_ord.clone(),

                        FloatPredicate::UEQ => fp_logical_or(
                            &is_uno,
                            &are_equal_ord,
                            &mut self.ctx,
                            &mut air_constraints,
                            "res_ueq",
                        ),
                        FloatPredicate::UNE => fp_logical_or(
                            &is_uno,
                            &fp_logical_not(
                                &are_equal_ord,
                                &mut self.ctx,
                                &mut air_constraints,
                                "not_are_equal_ord_u",
                            ),
                            &mut self.ctx,
                            &mut air_constraints,
                            "res_une",
                        ),
                        FloatPredicate::UGT => fp_logical_or(
                            &is_uno,
                            &is_gt_ord,
                            &mut self.ctx,
                            &mut air_constraints,
                            "res_ugt",
                        ),
                        FloatPredicate::UGE => fp_logical_or(
                            &is_uno,
                            &fp_logical_or(
                                &is_gt_ord,
                                &are_equal_ord,
                                &mut self.ctx,
                                &mut air_constraints,
                                "uge_cond",
                            ),
                            &mut self.ctx,
                            &mut air_constraints,
                            "res_uge",
                        ),
                        FloatPredicate::ULT => fp_logical_or(
                            &is_uno,
                            &is_lt_ord,
                            &mut self.ctx,
                            &mut air_constraints,
                            "res_ult",
                        ),
                        FloatPredicate::ULE => fp_logical_or(
                            &is_uno,
                            &fp_logical_or(
                                &is_lt_ord,
                                &are_equal_ord,
                                &mut self.ctx,
                                &mut air_constraints,
                                "ule_cond",
                            ),
                            &mut self.ctx,
                            &mut air_constraints,
                            "res_ule",
                        ),
                        FloatPredicate::UNO => is_uno.clone(),

                        FloatPredicate::PredicateTrue => AirExpression::Constant(1),
                        FloatPredicate::PredicateFalse => AirExpression::Constant(0),
                    };

                    air_constraints
                        .push(AirExpression::Sub(Box::new(res_expr), Box::new(final_res)));
                }
            }
        }

        air_constraints
    }
}

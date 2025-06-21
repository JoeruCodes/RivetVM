use std::collections::HashMap;

use crate::{
    constraints::{
        lang_operand_to_air_expression, AirExpression, AirTraceVariable, ResolveConstraint,
        RowOffset,
    },
    ConstraintSystemVariable, Operand, StructuredAirConstraint,
};

#[derive(Debug, Clone)]
pub struct Phi {
    pub result: ConstraintSystemVariable,
    pub incoming_values: Vec<(Operand, String)>,
    pub block_name: String,
}

impl ResolveConstraint for Phi {
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

        let phi_res_air_var = AirTraceVariable(dest_col.0);
        let phi_res_expr_current = AirExpression::Trace(phi_res_air_var, RowOffset::Current);

        if self.incoming_values.len() == 2 {
            let val1_op = self.incoming_values[0].0;
            let pred1_name = &self.incoming_values[0].1;
            let val2_op = self.incoming_values[1].0;
            let pred2_name = &self.incoming_values[1].1;

            if let Some(cond_var_lang) = phi_condition_map
                .get(&(pred1_name.clone(), pred2_name.clone()))
                .or_else(|| phi_condition_map.get(&(pred2_name.clone(), pred1_name.clone())))
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

                let cond_expr =
                    AirExpression::Trace(AirTraceVariable(cond_var.0), RowOffset::Current);
                let val_true_expr = ctx.expr_for_operand(val_true_op);
                let val_false_expr = ctx.expr_for_operand(val_false_op);

                let vt_minus_vf =
                    AirExpression::Sub(Box::new(val_true_expr), Box::new(val_false_expr.clone()));
                let c_mult_vt_minus_vf =
                    AirExpression::Mul(Box::new(cond_expr), Box::new(vt_minus_vf));
                let pr_minus_vf = AirExpression::Sub(
                    Box::new(phi_res_expr_current.clone()),
                    Box::new(val_false_expr),
                );
                let final_phi_constraint =
                    AirExpression::Sub(Box::new(pr_minus_vf), Box::new(c_mult_vt_minus_vf));

                constraints.push(final_phi_constraint.clone());
                println!(
                    "    PHI (2-input from CondBr): Generated constraint: {:?}",
                    final_phi_constraint
                );
            } else {
                let mut handled_by_other_phi_logic = false;
                for (val_op, pred_name) in &self.incoming_values {
                    if pred_name.as_str() == "entry" {
                        if let Operand::Const(_) = val_op {
                            let init_val_expr = ctx.expr_for_operand(*val_op);
                            let init_constraint = AirExpression::Sub(
                                Box::new(phi_res_expr_current.clone()),
                                Box::new(init_val_expr),
                            );
                            constraints.push(init_constraint.clone());
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
                        self.result,
                        self.block_name,
                        pred1_name,
                        val1_op,
                        pred2_name,
                        val2_op,
                        phi_condition_map
                    );
                }
            }
        } else if !self.incoming_values.is_empty() {
            let mut found_controlling_switch = false;
            for sw_instr_variant in switch_instructions {
                if let StructuredAirConstraint::Switch(switch_instr) = sw_instr_variant {
                    let mut relevant_to_phi = true;
                    for (_phi_op, phi_pred_name) in &self.incoming_values {
                        if !(phi_pred_name.as_str()
                            == switch_instr.default_target_block_name.as_str()
                            || switch_instr.cases.iter().any(|(_, case_target)| {
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
                        switch_instr.condition_operand, switch_instr.default_target_block_name, switch_instr.cases
                    );

                    let switch_cond_expr = ctx.expr_for_operand(switch_instr.condition_operand);

                    let mut case_selector_exprs = Vec::new();
                    let mut sum_of_is_case_k_terms_for_default_check: Option<Box<AirExpression>> =
                        None;

                    for (case_val_lang_op, case_target_name) in &switch_instr.cases {
                        let case_val_expr = ctx.expr_for_operand(*case_val_lang_op);

                        let is_this_case_aux_var = ctx.new_aux_variable();
                        let is_this_case_expr =
                            AirExpression::Trace(is_this_case_aux_var, RowOffset::Current);

                        constraints.push(AirExpression::Mul(
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
                        constraints.push(AirExpression::Mul(
                            Box::new(diff_cond_case),
                            Box::new(is_this_case_expr.clone()),
                        ));

                        let phi_op_for_this_case = self.incoming_values.iter().find(|(_, pred_name)| pred_name.as_str() == case_target_name.as_str())
                            .map(|(op, _)| ctx.expr_for_operand(*op))
                            .expect(&format!("PHI from Switch: Could not find PHI incoming value for case target {}", case_target_name));

                        case_selector_exprs.push((is_this_case_expr.clone(), phi_op_for_this_case));

                        sum_of_is_case_k_terms_for_default_check =
                            Some(match sum_of_is_case_k_terms_for_default_check {
                                Some(current_sum) => Box::new(AirExpression::Add(
                                    current_sum,
                                    Box::new(is_this_case_expr.clone()),
                                )),
                                None => Box::new(is_this_case_expr.clone()),
                            });
                    }

                    let is_default_aux_var = ctx.new_aux_variable();
                    let is_default_expr =
                        AirExpression::Trace(is_default_aux_var, RowOffset::Current);
                    constraints.push(AirExpression::Mul(
                        Box::new(is_default_expr.clone()),
                        Box::new(AirExpression::Sub(
                            Box::new(is_default_expr.clone()),
                            Box::new(AirExpression::Constant(1)),
                        )),
                    ));

                    let sum_is_cases = sum_of_is_case_k_terms_for_default_check
                        .unwrap_or_else(|| Box::new(AirExpression::Constant(0)));
                    constraints.push(AirExpression::Sub(
                        Box::new(AirExpression::Add(
                            Box::new(is_default_expr.clone()),
                            sum_is_cases,
                        )),
                        Box::new(AirExpression::Constant(1)),
                    ));

                    let phi_op_for_default = self.incoming_values.iter().find(|(_, pred_name)| pred_name.as_str() == switch_instr.default_target_block_name.as_str())
                        .map(|(op, _)| ctx.expr_for_operand(*op))
                        .expect(&format!("PHI from Switch: Could not find PHI incoming value for default target {}", switch_instr.default_target_block_name));

                    let mut selected_value_sum: Option<Box<AirExpression>> = None;
                    for (is_case_expr, phi_val_expr) in case_selector_exprs {
                        let term =
                            AirExpression::Mul(Box::new(is_case_expr), Box::new(phi_val_expr));
                        selected_value_sum = Some(match selected_value_sum {
                            Some(current_sum) => {
                                Box::new(AirExpression::Add(current_sum, Box::new(term)))
                            }
                            None => Box::new(term),
                        });
                    }
                    let default_term =
                        AirExpression::Mul(Box::new(is_default_expr), Box::new(phi_op_for_default));
                    selected_value_sum = Some(match selected_value_sum {
                        Some(current_sum) => {
                            Box::new(AirExpression::Add(current_sum, Box::new(default_term)))
                        }
                        None => Box::new(default_term),
                    });

                    let final_sum_expr = selected_value_sum
                        .expect("Should have at least a default term for PHI from switch");
                    let phi_switch_constraint =
                        AirExpression::Sub(Box::new(phi_res_expr_current.clone()), final_sum_expr);
                    constraints.push(phi_switch_constraint.clone());
                    println!(
                        "    PHI (from Switch): Generated constraint: {:?}",
                        phi_switch_constraint
                    );

                    break;
                }
            }
            if !found_controlling_switch {
                println!(
                    "WARN: PHI ({} inputs): Could not find controlling Switch instruction. PHI result {:?}, self.incoming_values: {:?}. Skipping.",
                    self.incoming_values.len(),
                    self.result,
                    self.incoming_values
                );
            }
        } else {
            println!(
                "WARN: PHI: Node with 0 incoming values found for result {:?}. Skipping.",
                self.result
            );
        }

        println!("    PHI processing complete.");

        if let Some(reg_col) = reg_col_opt {
            let sel = ctx.new_row_selector();
            let dest_expr = AirExpression::Trace(AirTraceVariable(dest_col.0), RowOffset::Current);
            let reg_expr = AirExpression::Trace(AirTraceVariable(reg_col), RowOffset::Current);
            let diff = AirExpression::Sub(Box::new(dest_expr), Box::new(reg_expr));
            ctx.add_row_gated_constraint(sel, diff);
        }
    }
}

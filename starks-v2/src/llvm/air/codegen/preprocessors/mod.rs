use std::collections::HashMap;

use lang::Operand;
use lang::StructuredAirConstraint;

use super::PreprocessedPhiTransitions;
use super::PreprocessedStructuredConstraints;
use crate::llvm::air::codegen::AirCodegen;
use crate::llvm::air::codegen::LangVariable;

impl AirCodegen {
    pub fn preprocess_structured_constraints(
        structured_constraints_from_lang: &[StructuredAirConstraint],
    ) -> PreprocessedStructuredConstraints {
        let mut phi_condition_map: HashMap<(String, String), LangVariable> = HashMap::new();
        let mut switch_instructions = Vec::new();

        for constraint in structured_constraints_from_lang {
            if let StructuredAirConstraint::ConditionalBranch {
                condition,
                true_block_name,
                false_block_name,
                block_name: _,
            } = constraint
            {
                phi_condition_map.insert(
                    (true_block_name.clone(), false_block_name.clone()),
                    *condition,
                );
            } else if let StructuredAirConstraint::Switch { block_name: _, .. } = constraint {
                switch_instructions.push(constraint.clone());
            }
        }

        PreprocessedStructuredConstraints {
            phi_condition_map,
            switch_instructions,
        }
    }

    pub fn preprocess_phi_transitions(
        structured_constraints_from_lang: &[StructuredAirConstraint],
    ) -> PreprocessedPhiTransitions {
        let mut loop_phi_transitions: HashMap<(String, String), Vec<(LangVariable, Operand)>> =
            HashMap::new();
        let mut block_terminators: HashMap<String, (String, Option<String>, Option<LangVariable>)> =
            HashMap::new();

        for constraint in structured_constraints_from_lang {
            match constraint {
                StructuredAirConstraint::Branch {
                    target_block_name,
                    block_name,
                } => {
                    block_terminators
                        .insert(block_name.clone(), (target_block_name.clone(), None, None));
                }
                StructuredAirConstraint::ConditionalBranch {
                    condition,
                    true_block_name,
                    false_block_name,
                    block_name,
                } => {
                    block_terminators.insert(
                        block_name.clone(),
                        (
                            true_block_name.clone(),
                            Some(false_block_name.clone()),
                            Some(*condition),
                        ),
                    );
                }

                _ => {}
            }
        }

        for constraint in structured_constraints_from_lang {
            if let StructuredAirConstraint::Phi {
                result,
                incoming_values,
                block_name: header_block_name,
            } = constraint
            {
                if header_block_name == "loop_header" {
                    for (current_value_operand_ref, current_predecessor_block_name_ref) in
                        incoming_values
                    {
                        if current_predecessor_block_name_ref == "loop_latch" {
                            if let Operand::Var(_) = *current_value_operand_ref {
                                if let Some((true_target, maybe_false_target, _)) =
                                    block_terminators.get(current_predecessor_block_name_ref)
                                {
                                    let is_confirmed_back_edge = true_target == header_block_name
                                        || (maybe_false_target.is_some()
                                            && maybe_false_target.as_ref().unwrap()
                                                == header_block_name);

                                    if is_confirmed_back_edge {
                                        println!(
                                            "  Targeted Loop edge identified for PHI Var {:?} in block '{}': from pred '{}' with val_op {:?}",
                                            result,
                                            header_block_name,
                                            current_predecessor_block_name_ref,
                                            current_value_operand_ref
                                        );
                                        loop_phi_transitions
                                            .entry((
                                                header_block_name.clone(),
                                                current_predecessor_block_name_ref.clone(),
                                            ))
                                            .or_default()
                                            .push((*result, *current_value_operand_ref));
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }

        PreprocessedPhiTransitions {
            loop_phi_transitions,
        }
    }
}

use std::collections::HashMap;

use lang::constraints::phi::Phi;
use lang::ConstraintSystemVariable as LangVariable;
use lang::Operand;
use lang::StructuredAirConstraint;

use super::PreprocessedPhiTransitions;
use super::PreprocessedStructuredConstraints;
use crate::llvm::air::codegen::AirCodegen;

impl AirCodegen {
    pub fn preprocess_structured_constraints(
        structured_constraints_from_lang: &[StructuredAirConstraint],
    ) -> PreprocessedStructuredConstraints {
        let mut phi_condition_map: HashMap<(String, String), LangVariable> = HashMap::new();
        let mut switch_instructions = Vec::new();

        for constraint in structured_constraints_from_lang {
            if let StructuredAirConstraint::ConditionalBranch(cond_branch) = constraint {
                phi_condition_map.insert(
                    (
                        cond_branch.true_block_name.clone(),
                        cond_branch.false_block_name.clone(),
                    ),
                    cond_branch.condition,
                );
            } else if let StructuredAirConstraint::Switch(_) = constraint {
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
                StructuredAirConstraint::Branch(branch) => {
                    block_terminators.insert(
                        branch.block_name.clone(),
                        (branch.target_block_name.clone(), None, None),
                    );
                }
                StructuredAirConstraint::ConditionalBranch(cond_branch) => {
                    block_terminators.insert(
                        cond_branch.block_name.clone(),
                        (
                            cond_branch.true_block_name.clone(),
                            Some(cond_branch.false_block_name.clone()),
                            Some(cond_branch.condition),
                        ),
                    );
                }

                _ => {}
            }
        }

        for constraint in structured_constraints_from_lang {
            if let StructuredAirConstraint::Phi(Phi {
                result,
                incoming_values,
                block_name: header_block_name,
            }) = constraint
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

#[cfg(test)]
mod tests {
    use super::*;
    use lang::{
        constraints::{
            branch::Branch, conditional_branch::ConditionalBranch, phi::Phi, switch::Switch,
        },
        Operand,
    };

    #[test]
    fn test_preprocess_structured_constraints() {
        let cond_var = LangVariable(0);
        let constraints = vec![
            StructuredAirConstraint::ConditionalBranch(ConditionalBranch {
                condition: cond_var,
                true_block_name: "if.then".to_string(),
                false_block_name: "if.else".to_string(),
                block_name: "entry".to_string(),
            }),
            StructuredAirConstraint::Switch(Switch {
                condition_operand: Operand::Var(LangVariable(1)),
                default_target_block_name: "sw.default".to_string(),
                cases: vec![(Operand::Const(10), "sw.case1".to_string())],
                block_name: "sw.entry".to_string(),
            }),
        ];

        let preprocessed = AirCodegen::preprocess_structured_constraints(&constraints);

        assert_eq!(preprocessed.phi_condition_map.len(), 1);
        assert_eq!(
            preprocessed
                .phi_condition_map
                .get(&("if.then".to_string(), "if.else".to_string())),
            Some(&cond_var)
        );

        assert_eq!(preprocessed.switch_instructions.len(), 1);
        matches!(
            preprocessed.switch_instructions[0],
            StructuredAirConstraint::Switch(_)
        );
    }

    #[test]
    fn test_preprocess_phi_transitions() {
        let phi_result_var = LangVariable(0);
        let loop_var = LangVariable(1);
        let cond_var = LangVariable(2);

        let constraints = vec![
            StructuredAirConstraint::Phi(Phi {
                result: phi_result_var,
                incoming_values: vec![
                    (Operand::Const(0), "entry".to_string()),
                    (Operand::Var(loop_var), "loop_latch".to_string()),
                ],
                block_name: "loop_header".to_string(),
            }),
            StructuredAirConstraint::ConditionalBranch(ConditionalBranch {
                condition: cond_var,
                true_block_name: "loop_header".to_string(),
                false_block_name: "loop_exit".to_string(),
                block_name: "loop_latch".to_string(),
            }),
            StructuredAirConstraint::Branch(Branch {
                target_block_name: "end".to_string(),
                block_name: "loop_exit".to_string(),
            }),
        ];

        let preprocessed = AirCodegen::preprocess_phi_transitions(&constraints);

        assert_eq!(preprocessed.loop_phi_transitions.len(), 1);

        let transition_key = ("loop_header".to_string(), "loop_latch".to_string());
        let expected_transitions = vec![(phi_result_var, Operand::Var(loop_var))];

        assert_eq!(
            preprocessed.loop_phi_transitions.get(&transition_key),
            Some(&expected_transitions)
        );
    }
}

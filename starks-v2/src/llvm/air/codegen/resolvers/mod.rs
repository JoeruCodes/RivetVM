use lang::StructuredAirConstraint;
use lang::constraints::{AirExpression, ResolveConstraint};
use std::collections::HashMap;

use super::AirCodegen;
use crate::llvm::air::codegen::LangVariable;

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
                StructuredAirConstraint::GetElementPtr(v) => {
                    v.resolve(
                        &mut air_constraints,
                        &mut self.ctx,
                        phi_condition_map,
                        switch_instructions,
                    );
                }
                StructuredAirConstraint::ZExt(v) => {
                    v.resolve(
                        &mut air_constraints,
                        &mut self.ctx,
                        phi_condition_map,
                        switch_instructions,
                    );
                }
                StructuredAirConstraint::SExt(v) => {
                    v.resolve(
                        &mut air_constraints,
                        &mut self.ctx,
                        phi_condition_map,
                        switch_instructions,
                    );
                }
                StructuredAirConstraint::FPExt(v) => {
                    v.resolve(
                        &mut air_constraints,
                        &mut self.ctx,
                        phi_condition_map,
                        switch_instructions,
                    );
                }
                StructuredAirConstraint::Select(v) => {
                    v.resolve(
                        &mut air_constraints,
                        &mut self.ctx,
                        phi_condition_map,
                        switch_instructions,
                    );
                }
                StructuredAirConstraint::Add(v) => {
                    v.resolve(
                        &mut air_constraints,
                        &mut self.ctx,
                        phi_condition_map,
                        switch_instructions,
                    );
                }
                StructuredAirConstraint::Sub(v) => {
                    v.resolve(
                        &mut air_constraints,
                        &mut self.ctx,
                        phi_condition_map,
                        switch_instructions,
                    );
                }
                StructuredAirConstraint::Multiply(v) => {
                    v.resolve(
                        &mut air_constraints,
                        &mut self.ctx,
                        phi_condition_map,
                        switch_instructions,
                    );
                }
                StructuredAirConstraint::And(v) => {
                    v.resolve(
                        &mut air_constraints,
                        &mut self.ctx,
                        phi_condition_map,
                        switch_instructions,
                    );
                }
                StructuredAirConstraint::Or(v) => {
                    v.resolve(
                        &mut air_constraints,
                        &mut self.ctx,
                        phi_condition_map,
                        switch_instructions,
                    );
                }
                StructuredAirConstraint::Xor(v) => {
                    v.resolve(
                        &mut air_constraints,
                        &mut self.ctx,
                        phi_condition_map,
                        switch_instructions,
                    );
                }
                StructuredAirConstraint::Shl(v) => {
                    v.resolve(
                        &mut air_constraints,
                        &mut self.ctx,
                        phi_condition_map,
                        switch_instructions,
                    );
                }

                StructuredAirConstraint::FPToSI(v) => {
                    v.resolve(
                        &mut air_constraints,
                        &mut self.ctx,
                        phi_condition_map,
                        switch_instructions,
                    );
                }
                StructuredAirConstraint::SIToFP(v) => {
                    v.resolve(
                        &mut air_constraints,
                        &mut self.ctx,
                        phi_condition_map,
                        switch_instructions,
                    );
                }
                StructuredAirConstraint::UIToFP(v) => {
                    v.resolve(
                        &mut air_constraints,
                        &mut self.ctx,
                        phi_condition_map,
                        switch_instructions,
                    );
                }
                StructuredAirConstraint::FPToUI(v) => {
                    v.resolve(
                        &mut air_constraints,
                        &mut self.ctx,
                        phi_condition_map,
                        switch_instructions,
                    );
                }
                StructuredAirConstraint::Shr(v) => {
                    v.resolve(
                        &mut air_constraints,
                        &mut self.ctx,
                        phi_condition_map,
                        switch_instructions,
                    );
                }
                StructuredAirConstraint::AShr(v) => {
                    v.resolve(
                        &mut air_constraints,
                        &mut self.ctx,
                        phi_condition_map,
                        switch_instructions,
                    );
                }
                StructuredAirConstraint::UDiv(v) => {
                    v.resolve(
                        &mut air_constraints,
                        &mut self.ctx,
                        phi_condition_map,
                        switch_instructions,
                    );
                }
                StructuredAirConstraint::SDiv(v) => {
                    v.resolve(
                        &mut air_constraints,
                        &mut self.ctx,
                        phi_condition_map,
                        switch_instructions,
                    );
                }
                StructuredAirConstraint::Icmp(v) => {
                    v.resolve(
                        &mut air_constraints,
                        &mut self.ctx,
                        phi_condition_map,
                        switch_instructions,
                    );
                }
                StructuredAirConstraint::Phi(v) => {
                    v.resolve(
                        &mut air_constraints,
                        &mut self.ctx,
                        phi_condition_map,
                        switch_instructions,
                    );
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
                StructuredAirConstraint::URem(v) => {
                    v.resolve(
                        &mut air_constraints,
                        &mut self.ctx,
                        phi_condition_map,
                        switch_instructions,
                    );
                }
                StructuredAirConstraint::SRem(v) => {
                    v.resolve(
                        &mut air_constraints,
                        &mut self.ctx,
                        phi_condition_map,
                        switch_instructions,
                    );
                }
                StructuredAirConstraint::Trunc(v) => {
                    v.resolve(
                        &mut air_constraints,
                        &mut self.ctx,
                        phi_condition_map,
                        switch_instructions,
                    );
                }
                StructuredAirConstraint::FPTrunc(v) => {
                    v.resolve(
                        &mut air_constraints,
                        &mut self.ctx,
                        phi_condition_map,
                        switch_instructions,
                    );
                }
                StructuredAirConstraint::FAdd(v) => {
                    v.resolve(
                        &mut air_constraints,
                        &mut self.ctx,
                        phi_condition_map,
                        switch_instructions,
                    );
                }
                StructuredAirConstraint::FSub(v) => {
                    v.resolve(
                        &mut air_constraints,
                        &mut self.ctx,
                        phi_condition_map,
                        switch_instructions,
                    );
                }

                StructuredAirConstraint::FMul(v) => {
                    v.resolve(
                        &mut air_constraints,
                        &mut self.ctx,
                        phi_condition_map,
                        switch_instructions,
                    );
                }
                StructuredAirConstraint::FDiv(v) => {
                    v.resolve(
                        &mut air_constraints,
                        &mut self.ctx,
                        phi_condition_map,
                        switch_instructions,
                    );
                }
                StructuredAirConstraint::FRem(v) => {
                    v.resolve(
                        &mut air_constraints,
                        &mut self.ctx,
                        phi_condition_map,
                        switch_instructions,
                    );
                }
                StructuredAirConstraint::FNeg(v) => {
                    v.resolve(
                        &mut air_constraints,
                        &mut self.ctx,
                        phi_condition_map,
                        switch_instructions,
                    );
                }
                StructuredAirConstraint::FCmp(v) => {
                    v.resolve(
                        &mut air_constraints,
                        &mut self.ctx,
                        phi_condition_map,
                        switch_instructions,
                    );
                }
            }
        }

        air_constraints
    }
}

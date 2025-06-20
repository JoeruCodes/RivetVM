use lang::constraints::{AirExpression, ResolveConstraint};
use lang::ConstraintSystemVariable as LangVariable;
use lang::StructuredAirConstraint;
use std::collections::HashMap;

use super::AirCodegen;

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
                StructuredAirConstraint::CatchPad(_) => {}
                StructuredAirConstraint::CatchRet(_) => {}
                StructuredAirConstraint::CatchSwitch(_) => {}
                StructuredAirConstraint::CleanupPad(_) => {}
                StructuredAirConstraint::CleanupRet(_) => {}
                StructuredAirConstraint::IndirectBr(_) => {}
                StructuredAirConstraint::LandingPad(_) => {}
                StructuredAirConstraint::Resume(_) => {}
                StructuredAirConstraint::ReturnAddress(v) => {
                    v.resolve(
                        &mut air_constraints,
                        &mut self.ctx,
                        phi_condition_map,
                        switch_instructions,
                    );
                }
                StructuredAirConstraint::Assign(v) => {
                    v.resolve(
                        &mut air_constraints,
                        &mut self.ctx,
                        phi_condition_map,
                        switch_instructions,
                    );
                }
                StructuredAirConstraint::AtomicCmpXchg(v) => {
                    v.resolve(
                        &mut air_constraints,
                        &mut self.ctx,
                        phi_condition_map,
                        switch_instructions,
                    );
                }
                StructuredAirConstraint::AtomicRMW(v) => {
                    v.resolve(
                        &mut air_constraints,
                        &mut self.ctx,
                        phi_condition_map,
                        switch_instructions,
                    );
                }
                StructuredAirConstraint::Call(_) => {}
                StructuredAirConstraint::CallBr(v) => {
                    v.resolve(
                        &mut air_constraints,
                        &mut self.ctx,
                        phi_condition_map,
                        switch_instructions,
                    );
                }
                StructuredAirConstraint::Invoke(_) => {}
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
                StructuredAirConstraint::FNeg(v) => {
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
                StructuredAirConstraint::FAdd(v) => {
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
                StructuredAirConstraint::FRem(v) => {
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
                StructuredAirConstraint::SDiv(v) => {
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
                StructuredAirConstraint::Shl(v) => {
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
                StructuredAirConstraint::SRem(v) => {
                    v.resolve(
                        &mut air_constraints,
                        &mut self.ctx,
                        phi_condition_map,
                        switch_instructions,
                    );
                }
                StructuredAirConstraint::URem(v) => {
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
                StructuredAirConstraint::Branch(r) => {
                    r.resolve(
                        &mut air_constraints,
                        &mut self.ctx,
                        phi_condition_map,
                        switch_instructions,
                    );
                }
                StructuredAirConstraint::ConditionalBranch(r) => {
                    r.resolve(
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
                StructuredAirConstraint::Return(ret) => {
                    ret.resolve(
                        &mut air_constraints,
                        &mut self.ctx,
                        phi_condition_map,
                        switch_instructions,
                    );
                }
                StructuredAirConstraint::Alloca { .. } => {}
                StructuredAirConstraint::Switch(r) => {
                    r.resolve(
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
                StructuredAirConstraint::SIToFP(v) => {
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
                StructuredAirConstraint::Select(v) => {
                    v.resolve(
                        &mut air_constraints,
                        &mut self.ctx,
                        phi_condition_map,
                        switch_instructions,
                    );
                }
                StructuredAirConstraint::GetElementPtr(v) => {
                    v.resolve(
                        &mut air_constraints,
                        &mut self.ctx,
                        phi_condition_map,
                        switch_instructions,
                    );
                }
                StructuredAirConstraint::ExtractValue { .. } => {}
            }
        }

        air_constraints
    }
}

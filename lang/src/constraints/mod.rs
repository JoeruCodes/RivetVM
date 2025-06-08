use std::collections::HashMap;

use crate::{ctx::AirGenContext, ConstraintSystemVariable, Operand, StructuredAirConstraint};

pub mod add;
pub mod and;
pub mod ashr;
pub mod fadd;
pub mod fcmp;
pub mod fdiv;
pub mod fmul;
pub mod fneg;
pub mod fpext;
pub mod fptosi;
pub mod fptoui;
pub mod fptrunc;
pub mod frem;
pub mod fsub;
pub mod get_elem_ptr;
pub mod icmp;
pub mod mul;
pub mod or;
pub mod phi;
pub mod sdiv;
pub mod select;
pub mod sext;
pub mod shl;
pub mod shr;
pub mod sitofp;
pub mod srem;
pub mod sub;
pub mod trunc;
pub mod udiv;
pub mod uitofp;
pub mod urem;
pub mod xor;
pub mod zext;

pub trait ResolveConstraint {
    fn resolve(
        &self,
        constraints: &mut Vec<AirExpression>,
        ctx: &mut AirGenContext,
        phi_condition_map: &HashMap<(String, String), ConstraintSystemVariable>,
        switch_instructions: &Vec<StructuredAirConstraint>,
    );
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct AirTraceVariable(pub usize);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum RowOffset {
    Current,
    Next,
}

#[derive(Debug, Clone, PartialEq)]
pub enum AirExpression {
    Trace(AirTraceVariable, RowOffset),
    Constant(u128),
    Add(Box<AirExpression>, Box<AirExpression>),
    Sub(Box<AirExpression>, Box<AirExpression>),
    Mul(Box<AirExpression>, Box<AirExpression>),
}

impl std::ops::Add for AirExpression {
    type Output = Self;

    fn add(self, other: Self) -> Self::Output {
        AirExpression::Add(Box::new(self), Box::new(other))
    }
}

impl std::ops::Mul for AirExpression {
    type Output = Self;

    fn mul(self, other: Self) -> Self::Output {
        AirExpression::Mul(Box::new(self), Box::new(other))
    }
}

impl std::ops::Sub for AirExpression {
    type Output = Self;

    fn sub(self, other: Self) -> Self::Output {
        AirExpression::Sub(Box::new(self), Box::new(other))
    }
}

pub fn lang_operand_to_air_expression(lang_op: Operand) -> AirExpression {
    match lang_op {
        Operand::Var(v) => AirExpression::Trace(AirTraceVariable(v.0), RowOffset::Current),
        Operand::Const(c) => AirExpression::Constant(c),
    }
}

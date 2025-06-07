use std::marker::PhantomData;

use crate::Field;

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

pub struct GeneratedAir<F: Field + Clone> {
    pub num_trace_columns: usize,

    pub constraints: Vec<AirExpression>,
    pub _phantom_field: PhantomData<F>,
}

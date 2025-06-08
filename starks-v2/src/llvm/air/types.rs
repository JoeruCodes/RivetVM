use std::{
    marker::PhantomData,
    ops::{Add, Mul, Sub},
};

use lang::constraints::AirExpression;

use crate::Field;

pub struct GeneratedAir<F: Field + Clone> {
    pub num_trace_columns: usize,

    pub constraints: Vec<AirExpression>,
    pub _phantom_field: PhantomData<F>,
}

use std::{
    marker::PhantomData,
    ops::{Add, Mul, Sub},
};

use lang::constraints::{AirExpression, AirTraceVariable};

use crate::{llvm::air::codegen::memory::MemoryTraceColumns, Field};

pub struct GeneratedAir<F: Field + Clone> {
    pub num_trace_columns: usize,

    pub constraints: Vec<AirExpression>,
    pub memory_trace_columns: MemoryTraceColumns,
    pub _phantom_field: PhantomData<F>,
}

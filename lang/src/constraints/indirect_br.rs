use crate::{ConstraintSystemVariable, Operand};

#[derive(Debug, Clone)]
pub struct IndirectBr {
    pub address: Operand,
    pub destinations: Vec<String>,
    pub block_name: String,
}

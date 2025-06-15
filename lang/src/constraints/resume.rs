use crate::{ConstraintSystemVariable, Operand};

#[derive(Debug, Clone)]
pub struct Resume {
    pub ptr_operand: Operand,
    pub selector_operand: Operand,
    pub block_name: String,
}

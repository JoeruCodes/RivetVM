use crate::ConstraintSystemVariable;

#[derive(Debug, Clone)]
pub struct CleanupPad {
    pub result: ConstraintSystemVariable,
    pub block_name: String,
}

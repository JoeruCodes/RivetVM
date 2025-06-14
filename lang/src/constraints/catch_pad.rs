use crate::ConstraintSystemVariable;

#[derive(Debug, Clone)]
pub struct CatchPad {
    pub result: ConstraintSystemVariable,
    pub block_name: String,
}

use crate::ConstraintSystemVariable;

#[derive(Debug, Clone)]
pub struct LandingPad {
    pub result: ConstraintSystemVariable,
    pub block_name: String,
}

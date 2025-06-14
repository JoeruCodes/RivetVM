use crate::ConstraintSystemVariable;

#[derive(Debug, Clone)]

pub struct CatchSwitch {
    pub unwind_dest_block_name: Option<String>,
    pub block_name: String,
    pub handler_block_names: Vec<String>,
    pub result: ConstraintSystemVariable,
}

use std::collections::HashMap;

use crate::{ConstraintSystemVariable, Operand};

#[derive(Debug, Clone)]
pub struct CallFrame {
    pub function_name: String,
    pub return_to_block: String,
    
    pub param_to_arg_map: HashMap<ConstraintSystemVariable, Operand>,
    
    pub return_value_dest: Option<ConstraintSystemVariable>,
}

#[derive(Debug, Clone, Default)]
pub struct CallStack {
    frames: Vec<CallFrame>,
}

impl CallStack {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn push(&mut self, frame: CallFrame) {
        self.frames.push(frame);
    }

    pub fn pop(&mut self) -> Option<CallFrame> {
        self.frames.pop()
    }

    pub fn is_empty(&self) -> bool {
        self.frames.is_empty()
    }

    pub fn last_mut(&mut self) -> Option<&mut CallFrame> {
        self.frames.last_mut()
    }
}

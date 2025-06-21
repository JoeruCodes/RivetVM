use std::collections::HashMap;

use inkwell::AtomicRMWBinOp;

use crate::{
    constraints::{
        lang_operand_to_air_expression, AirExpression, AirTraceVariable, ResolveConstraint,
        RowOffset,
    },
    ctx::AirGenContext,
    ConstraintSystemVariable, MemoryAccessLogEntry, MemoryAccessType, Operand,
    StructuredAirConstraint,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RmwBinOp {
    Xchg,
    Add,
    Sub,
    And,
    Nand,
    Or,
    Xor,
    Max,
    Min,
    UMax,
    UMin,
    FAdd,
    FSub,
}

impl From<AtomicRMWBinOp> for RmwBinOp {
    fn from(op: AtomicRMWBinOp) -> Self {
        match op {
            AtomicRMWBinOp::Xchg => Self::Xchg,
            AtomicRMWBinOp::Add => Self::Add,
            AtomicRMWBinOp::Sub => Self::Sub,
            AtomicRMWBinOp::And => Self::And,
            AtomicRMWBinOp::Nand => Self::Nand,
            AtomicRMWBinOp::Or => Self::Or,
            AtomicRMWBinOp::Xor => Self::Xor,
            AtomicRMWBinOp::Max => Self::Max,
            AtomicRMWBinOp::Min => Self::Min,
            AtomicRMWBinOp::UMax => Self::UMax,
            AtomicRMWBinOp::UMin => Self::UMin,
            AtomicRMWBinOp::FAdd => Self::FAdd,
            AtomicRMWBinOp::FSub => Self::FSub,
        }
    }
}

#[derive(Debug, Clone)]
pub struct AtomicRMW {
    pub ptr: Operand,
    pub value: Operand,
    pub operation: RmwBinOp,
    pub result: ConstraintSystemVariable,
    pub block_name: String,
    pub time_step: ConstraintSystemVariable,
}

impl ResolveConstraint for AtomicRMW {
    fn resolve(
        &self,
        constraints: &mut Vec<AirExpression>,
        ctx: &mut AirGenContext,
        _phi_condition_map: &HashMap<(String, String), ConstraintSystemVariable>,
        _switch_instructions: &Vec<StructuredAirConstraint>,
    ) {
        let reg_col_opt = ctx.col_for_ssa(self.result);

        let dest_col = ctx.new_aux_variable();
        ctx.bind_ssa_var(self.result, dest_col.0);

        let old_val_expr = AirExpression::Trace(dest_col, RowOffset::Current);
        let arg_val_expr = ctx.expr_for_operand(self.value);

        let new_val_expr = match self.operation {
            RmwBinOp::Add => old_val_expr + arg_val_expr,
            RmwBinOp::Sub => old_val_expr - arg_val_expr,

            _ => ctx.expr_for_operand(self.value),
        };

        let written_val_var = ctx.new_aux_variable();
        let written_val_expr = AirExpression::Trace(written_val_var, RowOffset::Current);
        constraints.push(written_val_expr - new_val_expr.clone());

        if let Some(reg_col) = reg_col_opt {
            let sel = ctx.new_row_selector();
            let reg_expr = AirExpression::Trace(AirTraceVariable(reg_col), RowOffset::Current);
            let dest_expr = AirExpression::Trace(dest_col.clone(), RowOffset::Current);
            let diff = AirExpression::Sub(Box::new(dest_expr), Box::new(reg_expr));
            ctx.add_row_gated_constraint(sel, diff);
        }
    }
}

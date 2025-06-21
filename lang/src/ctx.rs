use std::collections::HashMap;

use crate::{
    constraints::{call_stack::CallStack, AirExpression, AirTraceVariable, RowOffset},
    ConstraintSystemVariable, Operand,
};

use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RangeProofGroup {
    pub value_col: Option<usize>,
    pub base_col: usize,
    pub bitwidth: u32,
    pub signed: bool,
    pub overflow_col: usize,
}

#[derive(Debug, Clone)]
pub enum NextBlock {
    Direct(String),
    Conditional {
        condition: ConstraintSystemVariable,
        true_block: String,
        false_block: String,
    },
    Switch {
        condition: Operand,
        default_block: String,
        cases: Vec<(Operand, String)>,
    },
}

#[derive(Debug, Clone)]
pub struct FunctionContext {
    pub parameters: Vec<ConstraintSystemVariable>,
    pub entry_block: Option<String>,
}

#[derive(Debug, Clone)]
pub struct AirGenContext {
    pub next_available_trace_col: usize,
    pub(crate) internal_constraints: Vec<AirExpression>,
    pub functions: HashMap<String, FunctionContext>,
    pub call_stack: CallStack,
    pub next_block: Option<NextBlock>,

    pub ssa_column_map: HashMap<String, usize>,

    pub range_proof_groups: Vec<RangeProofGroup>,

    pub ssa_var_to_col: HashMap<usize, usize>,
}

impl AirGenContext {
    pub fn new(initial_max_var_id: usize) -> Self {
        AirGenContext {
            next_available_trace_col: initial_max_var_id + 1,
            internal_constraints: Vec::new(),
            functions: HashMap::new(),
            call_stack: CallStack::new(),
            next_block: None,
            ssa_column_map: HashMap::new(),
            range_proof_groups: Vec::new(),
            ssa_var_to_col: HashMap::new(),
        }
    }

    pub fn set_next_block(&mut self, block_name: Option<String>) {
        self.next_block = block_name.map(NextBlock::Direct);
    }

    pub fn set_conditional_next_block(
        &mut self,
        condition: ConstraintSystemVariable,
        true_block: String,
        false_block: String,
    ) {
        self.next_block = Some(NextBlock::Conditional {
            condition,
            true_block,
            false_block,
        });
    }

    pub fn set_switch_next_block(
        &mut self,
        condition: Operand,
        default_block: String,
        cases: Vec<(Operand, String)>,
    ) {
        self.next_block = Some(NextBlock::Switch {
            condition,
            default_block,
            cases,
        });
    }

    pub fn new_aux_variable(&mut self) -> AirTraceVariable {
        let var = AirTraceVariable(self.next_available_trace_col);
        self.next_available_trace_col += 1;

        let ssa_name = format!("tmp_{}", var.0);
        self.ssa_column_map.insert(ssa_name, var.0);
        var
    }

    pub fn add_unsigned_range_proof_constraints(
        &mut self,
        var_expr: AirExpression,
        bitwidth: u32,
    ) -> Vec<AirTraceVariable> {
        let bitwidth = bitwidth;
        let mut bit_vars = Vec::with_capacity(bitwidth as usize);
        let mut sum_of_bit_terms = AirExpression::Constant(0);

        for i in 0..bitwidth {
            let bit_var = self.new_aux_variable();
            bit_vars.push(bit_var);
            let bit_var_expr = AirExpression::Trace(bit_var, RowOffset::Current);

            self.internal_constraints.push(AirExpression::Mul(
                Box::new(bit_var_expr.clone()),
                Box::new(AirExpression::Sub(
                    Box::new(bit_var_expr.clone()),
                    Box::new(AirExpression::Constant(1)),
                )),
            ));

            sum_of_bit_terms = AirExpression::Add(
                Box::new(sum_of_bit_terms),
                Box::new(AirExpression::Mul(
                    Box::new(bit_var_expr.clone()),
                    Box::new(AirExpression::Constant(1u128 << i)),
                )),
            );
        }

        let overflow_var = self.new_aux_variable();
        let overflow_expr = AirExpression::Trace(overflow_var, RowOffset::Current);
        let overflow_term = AirExpression::Mul(
            Box::new(overflow_expr.clone()),
            Box::new(AirExpression::Constant(1u128 << bitwidth)),
        );
        let rhs_expr =
            AirExpression::Add(Box::new(sum_of_bit_terms.clone()), Box::new(overflow_term));

        self.internal_constraints.push(AirExpression::Sub(
            Box::new(var_expr.clone()),
            Box::new(rhs_expr),
        ));

        if let Some(first_bit_var) = bit_vars.first() {
            let value_col_opt =
                if let AirExpression::Trace(AirTraceVariable(val_col), RowOffset::Current) =
                    var_expr
                {
                    Some(val_col)
                } else {
                    None
                };

            self.range_proof_groups.push(RangeProofGroup {
                value_col: value_col_opt,
                base_col: first_bit_var.0,
                bitwidth,
                signed: false,
                overflow_col: overflow_var.0,
            });
        }

        bit_vars
    }

    pub fn add_signed_range_proof_constraints(
        &mut self,
        var_expr: AirExpression,
        bitwidth: u32,
    ) -> (Vec<AirExpression>, Option<AirExpression>) {
        let bitwidth = bitwidth;
        let (bit_exprs, msb_opt, overflow_var) =
            self.generate_signed_range_proof_constraints(&var_expr, bitwidth, "signed_range_proof");

        if let AirExpression::Trace(AirTraceVariable(val_col), RowOffset::Current) = var_expr {
            if let Some(AirExpression::Trace(AirTraceVariable(first_bit_col), RowOffset::Current)) =
                bit_exprs.first()
            {
                self.range_proof_groups.push(RangeProofGroup {
                    value_col: Some(val_col),
                    base_col: *first_bit_col,
                    bitwidth,
                    signed: true,
                    overflow_col: overflow_var.0,
                });
            }
        }

        (bit_exprs, msb_opt)
    }

    fn generate_signed_range_proof_constraints(
        &mut self,
        x_signed_expr: &AirExpression,
        bitwidth: u32,
        var_name: &str,
    ) -> (Vec<AirExpression>, Option<AirExpression>, AirTraceVariable) {
        if bitwidth == 0 {
            println!(
                "    SDIV Range Proof for {}: bitwidth is 0, skipping.",
                var_name
            );
            return (Vec::new(), None, AirTraceVariable(0));
        }
        println!(
            "    SDIV: Generating signed {}-bit range proof for {}",
            bitwidth, var_name
        );

        let pow_2_k_minus_1 = 1u128 << (bitwidth - 1);
        let x_unsigned_offset_val = AirExpression::Constant(pow_2_k_minus_1);

        let x_unsigned_expr = AirExpression::Add(
            Box::new(x_signed_expr.clone()),
            Box::new(x_unsigned_offset_val),
        );
        println!(
            "      {}_unsigned = {} + 2^({}-1) = {:?}",
            var_name, var_name, bitwidth, x_unsigned_expr
        );

        let mut bit_vars_exprs = Vec::new();
        let mut sum_terms = Vec::new();

        for i in 0..bitwidth {
            let bit_aux_var = self.new_aux_variable();
            let bit_expr = AirExpression::Trace(bit_aux_var, RowOffset::Current);

            let bit_minus_one = AirExpression::Sub(
                Box::new(bit_expr.clone()),
                Box::new(AirExpression::Constant(1)),
            );
            self.internal_constraints.push(AirExpression::Mul(
                Box::new(bit_expr.clone()),
                Box::new(bit_minus_one),
            ));
            bit_vars_exprs.push(bit_expr.clone());

            let power_of_2 = 1u128 << i;
            sum_terms.push(AirExpression::Mul(
                Box::new(bit_expr.clone()),
                Box::new(AirExpression::Constant(power_of_2)),
            ));
            println!(
                "        {}_bit_{} (trace col {}) created for {}. Booleanity added.",
                var_name, i, bit_aux_var.0, var_name
            );
        }

        let sum_from_bits = sum_terms
            .into_iter()
            .reduce(|acc, term| AirExpression::Add(Box::new(acc), Box::new(term)))
            .unwrap_or_else(|| AirExpression::Constant(0));

        let overflow_var = self.new_aux_variable();
        let overflow_expr = AirExpression::Trace(overflow_var, RowOffset::Current);
        let overflow_term = AirExpression::Mul(
            Box::new(overflow_expr.clone()),
            Box::new(AirExpression::Constant(1u128 << bitwidth)),
        );
        let rhs_expr = AirExpression::Add(Box::new(sum_from_bits.clone()), Box::new(overflow_term));

        self.internal_constraints.push(AirExpression::Sub(
            Box::new(x_unsigned_expr),
            Box::new(rhs_expr),
        ));
        println!(
            "      {}_unsigned decomposition constraint added for {}.
    ",
            var_name, var_name
        );

        let msb_expr_opt = bit_vars_exprs.last().cloned();
        (bit_vars_exprs, msb_expr_opt, overflow_var)
    }

    pub fn drain_internal_constraints(&mut self) -> Vec<AirExpression> {
        std::mem::take(&mut self.internal_constraints)
    }

    pub fn ssa_column_map(&self) -> &HashMap<String, usize> {
        &self.ssa_column_map
    }

    pub fn range_proof_groups(&self) -> &Vec<RangeProofGroup> {
        &self.range_proof_groups
    }

    pub fn bind_ssa_var(&mut self, var: crate::ConstraintSystemVariable, col: usize) {
        self.ssa_var_to_col.insert(var.0, col);
    }

    pub fn col_for_ssa(&self, var: crate::ConstraintSystemVariable) -> Option<usize> {
        self.ssa_var_to_col.get(&var.0).cloned()
    }

    pub fn expr_for_operand(&self, op: crate::Operand) -> crate::constraints::AirExpression {
        use crate::constraints::{AirExpression, AirTraceVariable, RowOffset};
        match op {
            crate::Operand::Const(c) => AirExpression::Constant(c),
            crate::Operand::Var(v) => {
                if let Some(col) = self.col_for_ssa(v) {
                    AirExpression::Trace(AirTraceVariable(col), RowOffset::Current)
                } else {
                    AirExpression::Trace(AirTraceVariable(v.0), RowOffset::Current)
                }
            }
        }
    }

    pub fn add_row_gated_constraint(
        &mut self,
        selector_expr: AirExpression,
        constraint_expr: AirExpression,
    ) {
        let _ = (selector_expr, constraint_expr);
    }

    pub fn new_row_selector(&mut self) -> AirExpression {
        use crate::constraints::{AirExpression, RowOffset};
        let sel_var = self.new_aux_variable();
        let sel_expr = AirExpression::Trace(sel_var, RowOffset::Current);

        self.internal_constraints.push(AirExpression::Mul(
            Box::new(sel_expr.clone()),
            Box::new(AirExpression::Sub(
                Box::new(sel_expr.clone()),
                Box::new(AirExpression::Constant(1)),
            )),
        ));

        sel_expr
    }

    pub fn current_selector_expr(&self) -> AirExpression {
        use crate::constraints::{AirExpression, AirTraceVariable, RowOffset};
        AirExpression::Trace(AirTraceVariable(44), RowOffset::Current)
    }
}

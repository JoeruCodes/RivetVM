use lang::constraints::{
    lang_operand_to_air_expression, AirExpression as AirConstraint, AirTraceVariable, RowOffset,
};
use lang::ctx::AirGenContext;
use lang::{MemoryAccessLogEntry, MemoryAccessType};

const CLK_DIFFERENCE_BITWIDTH: u32 = 32;

#[derive(Debug, Clone)]
pub struct MemoryTraceColumns {
    pub clk: AirTraceVariable,

    pub addr: AirTraceVariable,

    pub val: AirTraceVariable,

    pub is_write: AirTraceVariable,

    pub selector: AirTraceVariable,
}

pub fn generate_memory_air_constraints(
    memory_log: &[MemoryAccessLogEntry],
    air_gen_ctx: &mut AirGenContext,
    mut next_trace_col_idx: usize,
) -> (Vec<AirConstraint>, MemoryTraceColumns, usize) {
    let mut constraints = Vec::new();

    let clk_col = AirTraceVariable(next_trace_col_idx);
    next_trace_col_idx += 1;
    let addr_col = AirTraceVariable(next_trace_col_idx);
    next_trace_col_idx += 1;
    let val_col = AirTraceVariable(next_trace_col_idx);
    next_trace_col_idx += 1;
    let is_write_col = AirTraceVariable(next_trace_col_idx);
    next_trace_col_idx += 1;

    // selector column
    let sel_col = AirTraceVariable(next_trace_col_idx);
    next_trace_col_idx += 1;

    let memory_cols = MemoryTraceColumns {
        clk: clk_col,
        addr: addr_col,
        val: val_col,
        is_write: is_write_col,
        selector: sel_col,
    };

    if memory_log.is_empty() {
        return (constraints, memory_cols, next_trace_col_idx);
    }

    println!(
        "    Memory AIR Codegen: Defined {} memory trace columns. Processing {} memory access entries.",
        4,
        memory_log.len()
    );

    for i in 0..memory_log.len() {
        let entry = &memory_log[i];
        let m_clk_c = AirConstraint::Trace(memory_cols.clk, RowOffset::Current);
        let m_addr_c = AirConstraint::Trace(memory_cols.addr, RowOffset::Current);
        let m_val_c = AirConstraint::Trace(memory_cols.val, RowOffset::Current);
        let m_is_write_c = AirConstraint::Trace(memory_cols.is_write, RowOffset::Current);
        let sel_c = AirConstraint::Trace(memory_cols.selector, RowOffset::Current);

        // selector booleanity
        constraints.push(AirConstraint::Mul(
            Box::new(sel_c.clone()),
            Box::new(AirConstraint::Sub(
                Box::new(sel_c.clone()),
                Box::new(AirConstraint::Constant(1)),
            )),
        ));

        constraints.push(AirConstraint::Mul(
            Box::new(sel_c.clone()),
            Box::new(AirConstraint::Sub(
                Box::new(m_clk_c.clone()),
                Box::new(AirConstraint::Constant(entry.time_step.0 as u128)),
            )),
        ));

        constraints.push(AirConstraint::Mul(
            Box::new(sel_c.clone()),
            Box::new(AirConstraint::Sub(
                Box::new(m_addr_c.clone()),
                Box::new(lang_operand_to_air_expression(entry.address)),
            )),
        ));

        let is_write_val_const =
            AirConstraint::Constant(if entry.access_type == MemoryAccessType::Write {
                1
            } else {
                0
            });
        constraints.push(AirConstraint::Mul(
            Box::new(sel_c.clone()),
            Box::new(AirConstraint::Sub(
                Box::new(m_is_write_c.clone()),
                Box::new(is_write_val_const.clone()),
            )),
        ));

        constraints.push(AirConstraint::Mul(
            Box::new(sel_c.clone()),
            Box::new(AirConstraint::Mul(
                Box::new(m_is_write_c.clone()),
                Box::new(AirConstraint::Sub(
                    Box::new(m_is_write_c.clone()),
                    Box::new(AirConstraint::Constant(1)),
                )),
            )),
        ));

        constraints.push(AirConstraint::Mul(
            Box::new(sel_c.clone()),
            Box::new(AirConstraint::Mul(
                Box::new(is_write_val_const.clone()),
                Box::new(AirConstraint::Sub(
                    Box::new(m_val_c.clone()),
                    Box::new(lang_operand_to_air_expression(entry.value)),
                )),
            )),
        ));
    }

    for i in 0..(memory_log.len().saturating_sub(1)) {
        let m_clk_c = AirConstraint::Trace(memory_cols.clk, RowOffset::Current);
        let m_addr_c = AirConstraint::Trace(memory_cols.addr, RowOffset::Current);
        let m_val_c = AirConstraint::Trace(memory_cols.val, RowOffset::Current);
        let m_is_write_c = AirConstraint::Trace(memory_cols.is_write, RowOffset::Current);
        let sel_c = AirConstraint::Trace(memory_cols.selector, RowOffset::Current);

        let m_clk_n = AirConstraint::Trace(memory_cols.clk, RowOffset::Next);
        let m_addr_n = AirConstraint::Trace(memory_cols.addr, RowOffset::Next);
        let m_val_n = AirConstraint::Trace(memory_cols.val, RowOffset::Next);
        let m_is_write_n = AirConstraint::Trace(memory_cols.is_write, RowOffset::Next);
        let sel_n = AirConstraint::Trace(memory_cols.selector, RowOffset::Next);

        let next_entry_val_expr = lang_operand_to_air_expression(memory_log[i + 1].value);

        let addr_diff = AirConstraint::Sub(Box::new(m_addr_n.clone()), Box::new(m_addr_c.clone()));

        let is_addr_same_aux =
            AirConstraint::Trace(air_gen_ctx.new_aux_variable(), RowOffset::Current);
        let inv_addr_diff_aux =
            AirConstraint::Trace(air_gen_ctx.new_aux_variable(), RowOffset::Current);

        constraints.push(AirConstraint::Mul(
            Box::new(is_addr_same_aux.clone()),
            Box::new(AirConstraint::Sub(
                Box::new(is_addr_same_aux.clone()),
                Box::new(AirConstraint::Constant(1)),
            )),
        ));

        constraints.push(AirConstraint::Mul(
            Box::new(addr_diff.clone()),
            Box::new(is_addr_same_aux.clone()),
        ));

        constraints.push(AirConstraint::Sub(
            Box::new(AirConstraint::Mul(
                Box::new(addr_diff.clone()),
                Box::new(inv_addr_diff_aux.clone()),
            )),
            Box::new(AirConstraint::Sub(
                Box::new(AirConstraint::Constant(1)),
                Box::new(is_addr_same_aux.clone()),
            )),
        ));

        let clk_diff_val_expr = AirConstraint::Sub(
            Box::new(AirConstraint::Sub(
                Box::new(m_clk_n.clone()),
                Box::new(m_clk_c.clone()),
            )),
            Box::new(AirConstraint::Constant(1)),
        );
        let clk_diff_non_negative_aux =
            AirConstraint::Trace(air_gen_ctx.new_aux_variable(), RowOffset::Current);
        constraints.push(AirConstraint::Mul(
            Box::new(sel_c.clone()),
            Box::new(AirConstraint::Mul(
                Box::new(is_addr_same_aux.clone()),
                Box::new(AirConstraint::Sub(
                    Box::new(clk_diff_val_expr.clone()),
                    Box::new(clk_diff_non_negative_aux.clone()),
                )),
            )),
        ));

        let _clk_diff_bits = air_gen_ctx.add_unsigned_range_proof_constraints(
            clk_diff_non_negative_aux.clone(),
            CLK_DIFFERENCE_BITWIDTH,
        );

        let read_selector_next = AirConstraint::Sub(
            Box::new(AirConstraint::Constant(1)),
            Box::new(m_is_write_n.clone()),
        );
        let val_prop_if_read_next =
            AirConstraint::Mul(Box::new(read_selector_next), Box::new(m_val_c.clone()));
        let val_prop_if_write_next = AirConstraint::Mul(
            Box::new(m_is_write_n.clone()),
            Box::new(next_entry_val_expr.clone()),
        );
        let expected_val_n_if_addr_same = AirConstraint::Add(
            Box::new(val_prop_if_write_next),
            Box::new(val_prop_if_read_next),
        );

        let val_consistency_if_addr_same = AirConstraint::Sub(
            Box::new(m_val_n.clone()),
            Box::new(expected_val_n_if_addr_same),
        );
        constraints.push(AirConstraint::Mul(
            Box::new(sel_c.clone()),
            Box::new(AirConstraint::Mul(
                Box::new(is_addr_same_aux.clone()),
                Box::new(val_consistency_if_addr_same),
            )),
        ));

        let not_is_addr_same_selector = AirConstraint::Sub(
            Box::new(AirConstraint::Constant(1)),
            Box::new(is_addr_same_aux.clone()),
        );
        let read_selector_next_for_new_addr = AirConstraint::Sub(
            Box::new(AirConstraint::Constant(1)),
            Box::new(m_is_write_n.clone()),
        );
        let term1 = AirConstraint::Mul(
            Box::new(not_is_addr_same_selector),
            Box::new(read_selector_next_for_new_addr),
        );
        constraints.push(AirConstraint::Mul(
            Box::new(sel_c.clone()),
            Box::new(AirConstraint::Mul(
                Box::new(term1),
                Box::new(AirConstraint::Sub(
                    Box::new(AirConstraint::Sub(
                        Box::new(m_clk_n.clone()),
                        Box::new(m_clk_c.clone()),
                    )),
                    Box::new(AirConstraint::Constant(1)),
                )),
            )),
        ));
    }

    constraints.extend(air_gen_ctx.drain_internal_constraints());

    println!(
        "    Memory AIR Codegen: Defined {} memory trace columns. Added {} constraints. Next aux var from ctx: {}. Final trace col idx: {}",
        4,
        constraints.len(),
        air_gen_ctx.next_available_trace_col,
        next_trace_col_idx
    );

    (constraints, memory_cols, next_trace_col_idx)
}

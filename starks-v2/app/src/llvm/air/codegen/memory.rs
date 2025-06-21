use lang::constraints::AirExpression as AirConstraint;
use lang::constraints::{AirExpression, AirTraceVariable, RowOffset};
use lang::ctx::AirGenContext;
use lang::MemoryAccessLogEntry;

#[derive(Debug, Clone)]
pub struct MemoryTraceColumns {
    pub clk: AirTraceVariable,

    pub addr: AirTraceVariable,

    pub val: AirTraceVariable,

    pub is_write: AirTraceVariable,

    pub last_write_val: AirTraceVariable,

    pub is_first_read: AirTraceVariable,
}

pub fn generate_memory_air_constraints(
    memory_log: &[MemoryAccessLogEntry],
    air_gen_ctx: &mut AirGenContext,
    mut next_trace_col_idx: usize,
) -> (Vec<AirExpression>, MemoryTraceColumns, usize) {
    let mut constraints = Vec::new();

    let clk_col = AirTraceVariable(next_trace_col_idx);
    next_trace_col_idx += 1;
    let addr_col = AirTraceVariable(next_trace_col_idx);
    next_trace_col_idx += 1;
    let val_col = AirTraceVariable(next_trace_col_idx);
    next_trace_col_idx += 1;
    let is_write_col = AirTraceVariable(next_trace_col_idx);
    next_trace_col_idx += 1;

    let last_write_val_col = AirTraceVariable(next_trace_col_idx);
    next_trace_col_idx += 1;

    let is_first_read_col = AirTraceVariable(next_trace_col_idx);
    next_trace_col_idx += 1;

    let memory_cols = MemoryTraceColumns {
        clk: clk_col,
        addr: addr_col,
        val: val_col,
        is_write: is_write_col,
        last_write_val: last_write_val_col,
        is_first_read: is_first_read_col,
    };

    if air_gen_ctx.next_available_trace_col < next_trace_col_idx {
        air_gen_ctx.next_available_trace_col = next_trace_col_idx;
    }

    for _entry in memory_log {
        constraints.push(AirExpression::Mul(
            Box::new(AirExpression::Trace(
                memory_cols.is_write,
                RowOffset::Current,
            )),
            Box::new(AirExpression::Sub(
                Box::new(AirExpression::Trace(
                    memory_cols.is_write,
                    RowOffset::Current,
                )),
                Box::new(AirExpression::Constant(1)),
            )),
        ));
    }

    for i in 0..memory_log.len().saturating_sub(1) {
        let m_clk_c = AirExpression::Trace(memory_cols.clk, RowOffset::Current);
        let m_addr_c = AirExpression::Trace(memory_cols.addr, RowOffset::Current);
        let m_val_c = AirExpression::Trace(memory_cols.val, RowOffset::Current);
        let m_is_write_c = AirExpression::Trace(memory_cols.is_write, RowOffset::Current);

        let m_last_write_val_c =
            AirExpression::Trace(memory_cols.last_write_val, RowOffset::Current);
        let m_is_first_read_c = AirExpression::Trace(memory_cols.is_first_read, RowOffset::Current);

        let m_clk_n = AirExpression::Trace(memory_cols.clk, RowOffset::Next);
        let m_addr_n = AirExpression::Trace(memory_cols.addr, RowOffset::Next);
        let m_val_n = AirExpression::Trace(memory_cols.val, RowOffset::Next);
        let m_is_write_n = AirExpression::Trace(memory_cols.is_write, RowOffset::Next);

        let next_entry_val_expr = air_gen_ctx.expr_for_operand(memory_log[i + 1].value);
        let addr_diff = AirConstraint::Sub(Box::new(m_addr_n.clone()), Box::new(m_addr_c.clone()));

        let is_addr_same_aux =
            AirConstraint::Trace(air_gen_ctx.new_aux_variable(), RowOffset::Current);
        let inv_addr_diff_aux =
            AirConstraint::Trace(air_gen_ctx.new_aux_variable(), RowOffset::Current);

        let clk_diff_lo_aux =
            AirConstraint::Trace(air_gen_ctx.new_aux_variable(), RowOffset::Current);
        let clk_diff_hi_aux =
            AirConstraint::Trace(air_gen_ctx.new_aux_variable(), RowOffset::Current);

        let _bit_vars =
            air_gen_ctx.add_unsigned_range_proof_constraints(clk_diff_lo_aux.clone(), 32);

        constraints.push(AirConstraint::Sub(
            Box::new(AirConstraint::Add(
                Box::new(clk_diff_lo_aux.clone()),
                Box::new(AirConstraint::Mul(
                    Box::new(clk_diff_hi_aux.clone()),
                    Box::new(AirConstraint::Constant(1u128 << 32)),
                )),
            )),
            Box::new(AirConstraint::Sub(
                Box::new(m_clk_n.clone()),
                Box::new(m_clk_c.clone()),
            )),
        ));

        constraints.push(AirConstraint::Mul(
            Box::new(clk_diff_hi_aux.clone()),
            Box::new(AirConstraint::Sub(
                Box::new(clk_diff_hi_aux.clone()),
                Box::new(AirConstraint::Constant(1)),
            )),
        ));

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

        constraints.push(AirConstraint::Sub(
            Box::new(AirConstraint::Sub(
                Box::new(m_clk_n.clone()),
                Box::new(m_clk_c.clone()),
            )),
            Box::new(AirConstraint::Constant(1)),
        ));

        constraints.push(AirConstraint::Mul(
            Box::new(m_is_first_read_c.clone()),
            Box::new(AirConstraint::Sub(
                Box::new(m_val_c.clone()),
                Box::new(m_last_write_val_c.clone()),
            )),
        ));
    }

    constraints.extend(air_gen_ctx.drain_internal_constraints());
    (constraints, memory_cols, next_trace_col_idx)
}

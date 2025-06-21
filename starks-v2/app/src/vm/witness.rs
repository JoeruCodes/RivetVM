use lang::constraints::{AirExpression, AirTraceVariable, RowOffset};
use lang::ctx::RangeProofGroup;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

use super::{GoldilocksField, MemoryAccessType, MemoryTraceEntry, TraceEntry};
use crate::{
    llvm::air::codegen::{constraint_provider::AirConstraintProvider, AirCodegen},
    mod_pow, ConstraintProvider, Field,
};

use std::collections::HashSet;
use std::iter::FromIterator;

const AUX_PER_ROW: usize = 37;

fn mod_inv(val: u128, prime: u128) -> u128 {
    if val == 0 {
        0
    } else {
        mod_pow(val, prime - 2, prime)
    }
}

fn expr_contains_column(expr: &AirExpression, col: usize) -> bool {
    match expr {
        AirExpression::Trace(AirTraceVariable(c), _) => *c == col,
        AirExpression::Add(a, b) | AirExpression::Sub(a, b) | AirExpression::Mul(a, b) => {
            expr_contains_column(a, col) || expr_contains_column(b, col)
        }
        _ => false,
    }
}

fn eval_air_expr(
    expr: &AirExpression,
    row: usize,
    trace_len: usize,
    trace_cols: &Vec<Vec<u128>>,
    prime: u128,
) -> u128 {
    match expr {
        AirExpression::Constant(c) => *c % prime,
        AirExpression::Add(a, b) => {
            (eval_air_expr(a, row, trace_len, trace_cols, prime)
                + eval_air_expr(b, row, trace_len, trace_cols, prime))
                % prime
        }
        AirExpression::Sub(a, b) => {
            let l = eval_air_expr(a, row, trace_len, trace_cols, prime);
            let r = eval_air_expr(b, row, trace_len, trace_cols, prime);
            (l + prime - r) % prime
        }
        AirExpression::Mul(a, b) => {
            (eval_air_expr(a, row, trace_len, trace_cols, prime)
                * eval_air_expr(b, row, trace_len, trace_cols, prime))
                % prime
        }
        AirExpression::Trace(AirTraceVariable(c), offset) => {
            let idx = match offset {
                RowOffset::Current => row,
                RowOffset::Next => (row + 1) % trace_len,
            };
            trace_cols[*c][idx]
        }
    }
}

fn try_solve_side(
    lhs: &AirExpression,
    rhs: &AirExpression,
    row: usize,
    trace_len: usize,
    trace_cols: &mut Vec<Vec<u128>>,
    prime: u128,
    protected: &HashSet<usize>,
) -> bool {
    if let AirExpression::Trace(AirTraceVariable(col), RowOffset::Current) = lhs {
        if *col < 32 || protected.contains(col) {
            return false;
        }

        if expr_contains_column(rhs, *col) {
            return false;
        }

        if matches!(rhs, AirExpression::Trace(AirTraceVariable(rcol), RowOffset::Current) if *rcol < 32)
            || protected.iter().any(|p| expr_contains_column(rhs, *p))
        {
            return false;
        }

        let val = eval_air_expr(rhs, row, trace_len, trace_cols, prime);
        if trace_cols[*col][row] != val {
            trace_cols[*col][row] = val;
            return true;
        }
        return false;
    } else {
        match lhs {
            AirExpression::Add(a, b) | AirExpression::Sub(a, b) => {
                let (trace_side, other_side, trace_on_left) = match (&**a, &**b) {
                    (AirExpression::Trace(AirTraceVariable(c), RowOffset::Current), other) => {
                        (Some(*c), other, true)
                    }
                    (other, AirExpression::Trace(AirTraceVariable(c), RowOffset::Current)) => {
                        (Some(*c), other, false)
                    }
                    _ => (None, lhs, false),
                };

                if let Some(col) = trace_side {
                    if col < 32 || protected.contains(&col) {
                        return false;
                    }

                    if !matches!(rhs, AirExpression::Constant(_)) {
                        return false;
                    }

                    if expr_contains_column(other_side, col) {
                        return false;
                    }

                    if protected
                        .iter()
                        .any(|p| expr_contains_column(other_side, *p))
                    {
                        return false;
                    }

                    let other_val = eval_air_expr(other_side, row, trace_len, trace_cols, prime);
                    let rhs_val = eval_air_expr(rhs, row, trace_len, trace_cols, prime);

                    let new_val = match lhs {
                        AirExpression::Add(_, _) => (rhs_val + prime - other_val) % prime,
                        AirExpression::Sub(_, _) => {
                            if trace_on_left {
                                (rhs_val + other_val) % prime
                            } else {
                                (other_val + prime - rhs_val) % prime
                            }
                        }
                        _ => return false,
                    };
                    if trace_cols[col][row] != new_val {
                        trace_cols[col][row] = new_val;
                        return true;
                    }
                }
            }
            _ => {}
        }
    }
    false
}

fn collect_max_col(expr: &AirExpression, max: &mut usize) {
    match expr {
        AirExpression::Trace(AirTraceVariable(c), _) => {
            if *c > *max {
                *max = *c;
            }
        }
        AirExpression::Add(a, b) | AirExpression::Sub(a, b) | AirExpression::Mul(a, b) => {
            collect_max_col(a, max);
            collect_max_col(b, max);
        }
        _ => {}
    }
}

pub fn generate_vm_witness(
    llvm_ir: &str,
    trace_data: &str,
    memory_trace_data: &str,
    other_cols_raw: &[u8],
) -> Result<Vec<Vec<u128>>, String> {
    let field = GoldilocksField;

    let trace: Vec<TraceEntry> = serde_json::from_str(trace_data)
        .map_err(|e| format!("Failed to parse trace_data: {}", e))?;
    let mut memory_trace: Vec<MemoryTraceEntry> = serde_json::from_str(memory_trace_data)
        .map_err(|e| format!("Failed to parse memory_trace_data: {}", e))?;

    memory_trace.sort_by(|a, b| {
        let key_a = (
            a.address,
            a.time_step,
            match a.access_type {
                MemoryAccessType::Write => 1u8,
                MemoryAccessType::Read => 0u8,
            },
        );
        let key_b = (
            b.address,
            b.time_step,
            match b.access_type {
                MemoryAccessType::Write => 1u8,
                MemoryAccessType::Read => 0u8,
            },
        );
        key_a.cmp(&key_b)
    });
    let mut other_cols: Vec<Vec<u128>> = serde_json::from_slice(other_cols_raw)
        .map_err(|e| format!("Failed to parse other_cols_raw: {}", e))?;

    let air = AirCodegen::generate_air(llvm_ir, &field)
        .map_err(|e| format!("Failed to generate AIR: {}", e))?;
    let range_groups: Vec<RangeProofGroup> = air.range_proof_groups.clone();

    #[cfg(test)]
    {
        for (cidx, expr) in air.constraints.iter().enumerate() {
            if expr_contains_column(expr, 37) {
                println!("DEBUG constraint {} uses col 37: {:?}", cidx, expr);
            }
        }
    }

    let aux_start_col: usize = air.memory_trace_columns.iter().max().copied().unwrap_or(0) + 1;

    let expected_pairs = 0usize;

    let trace_len = trace.len();

    let expected_other_cols = air.num_trace_columns.saturating_sub(32);
    if other_cols.len() < expected_other_cols {
        other_cols.resize_with(expected_other_cols, || vec![0u128; trace_len]);
    }

    for col in &mut other_cols {
        if col.len() == trace_len - 1 {
            col.insert(0, *col.first().unwrap_or(&0u128));
        }
        if col.len() < trace_len {
            let pad_val = *col.last().unwrap_or(&0u128);
            col.resize(trace_len, pad_val);
        } else if col.len() > trace_len {
            col.truncate(trace_len);
        }
    }

    let mut trace_columns = other_cols;
    trace_columns.splice(0..0, vec![vec![0u128; trace_len]; 32]);

    let clk_col = air.memory_trace_columns[0];
    let addr_col = air.memory_trace_columns[1];
    let val_col = air.memory_trace_columns[2];
    let is_write_col = air.memory_trace_columns[3];

    let last_write_val_col = *air.ssa_column_map.get("mem_last_write_val").unwrap();
    let is_first_read_col = *air.ssa_column_map.get("mem_is_first_read").unwrap();

    for row in 0..trace_len {
        trace_columns[clk_col][row] = row as u128;
    }

    for (row, m) in memory_trace.iter().enumerate() {
        if row >= trace_columns[0].len() {
            continue;
        }
        trace_columns[addr_col][row] = m.address as u128;
        trace_columns[val_col][row] = m.value as u128;
        trace_columns[is_write_col][row] = match m.access_type {
            MemoryAccessType::Write => 1,
            MemoryAccessType::Read => 0,
        };
    }

    for col in &mut trace_columns {
        col.push(0u128);
    }
    let new_row_idx = trace_len;
    trace_columns[addr_col][new_row_idx] = trace_columns[addr_col][0];

    trace_columns[is_write_col][new_row_idx] = 0;

    trace_columns[clk_col][new_row_idx] =
        (trace_columns[clk_col][trace_len - 1] + 1) % GoldilocksField::PRIME;

    let goldilocks_prime: u128 = GoldilocksField::PRIME;

    #[cfg(test)]
    println!(
        "DEBUG: memory rows = {}, expected_pairs = {}",
        memory_trace.len(),
        expected_pairs
    );
    #[cfg(test)]
    println!(
        "DEBUG is_write rows 24/25 before aux copy: {} {}",
        trace_columns[is_write_col][24], trace_columns[is_write_col][25]
    );

    let total_rows = trace_len;

    let highest_helper_col = aux_start_col + total_rows * AUX_PER_ROW - 1;
    if highest_helper_col >= trace_columns.len() {
        let col_len = trace_columns[0].len();
        trace_columns
            .extend((0..=highest_helper_col - trace_columns.len()).map(|_| vec![0u128; col_len]));
    }

    for row in 0..total_rows {
        let base_col = aux_start_col + row * AUX_PER_ROW;

        let curr_addr = trace_columns[addr_col][row] as u128;
        let next_addr = trace_columns[addr_col][row + 1] as u128;

        let addr_diff =
            ((next_addr as i128 - curr_addr as i128).rem_euclid(goldilocks_prime as i128)) as u128;

        let is_addr_same = if addr_diff == 0 { 1u128 } else { 0u128 };
        let inv_addr_diff = mod_inv(addr_diff, goldilocks_prime);

        let clk_diff_lo = 1u128;
        let clk_diff_hi = 0u128;

        for blk_start in (aux_start_col..=highest_helper_col).step_by(AUX_PER_ROW) {
            trace_columns[blk_start + 0][row] = is_addr_same;
            trace_columns[blk_start + 1][row] = inv_addr_diff;
            trace_columns[blk_start + 2][row] = clk_diff_lo;
            trace_columns[blk_start + 3][row] = clk_diff_hi;

            trace_columns[blk_start + 4][row] = 1u128;
            for b in 1..32 {
                trace_columns[blk_start + 4 + b][row] = 0u128;
            }

            trace_columns[blk_start + 36][row] = 0u128;
        }
    }

    #[cfg(test)]
    {
        println!(
            "DEBUG helper row0 col{}={} col{}={}, row1 col{}={} col{}={}",
            aux_start_col,
            trace_columns[aux_start_col][0],
            aux_start_col + 1,
            trace_columns[aux_start_col + 1][0],
            aux_start_col + 2,
            trace_columns[aux_start_col + 2][1],
            aux_start_col + 3,
            trace_columns[aux_start_col + 3][1]
        );
    }

    for grp in &range_groups {
        let base = grp.base_col;
        let bits = grp.bitwidth as usize;

        let Some(vcol) = grp.value_col else { continue };

        if base + bits - 1 >= trace_columns.len() {
            let missing = base + bits - trace_columns.len();
            trace_columns.extend((0..=missing).map(|_| vec![0u128; trace_len]));
        }
        if vcol >= trace_columns.len() {
            continue;
        }

        for row in 0..trace_len {
            let val_raw = trace_columns[vcol][row];
            let (range_mod, half_mod) = if bits < 128 {
                let rm = 1u128 << bits;
                let hm = rm >> 1;
                (Some(rm), Some(hm))
            } else {
                (None, None)
            };

            let mut x_k = if grp.signed && bits > 0 {
                match half_mod {
                    Some(hm) => (val_raw + hm) % GoldilocksField::PRIME,
                    None => val_raw % GoldilocksField::PRIME,
                }
            } else {
                val_raw % GoldilocksField::PRIME
            };

            if let Some(rm) = range_mod {
                x_k %= rm;
            }

            for b in 0..bits {
                trace_columns[base + b][row] = (x_k >> b) & 1u128;
            }
            if grp.overflow_col >= trace_columns.len() {
                trace_columns.extend(
                    (0..=(grp.overflow_col - trace_columns.len())).map(|_| vec![0u128; trace_len]),
                );
            }
            let overflow_val = (val_raw - x_k) >> bits;
            trace_columns[grp.overflow_col][row] = overflow_val;
        }
    }

    let mut value_expr_cache: HashMap<usize, AirExpression> = HashMap::new();

    for grp in &range_groups {
        if grp.value_col.is_some() {
            continue;
        }

        let base = grp.base_col;
        let bits = grp.bitwidth as usize;

        let val_expr = value_expr_cache
            .entry(base)
            .or_insert_with(|| {
                air.constraints
                    .iter()
                    .find_map(|c| {
                        if let AirExpression::Sub(lhs, rhs) = c {
                            let lhs_has = expr_contains_column(lhs, base);
                            let rhs_has = expr_contains_column(rhs, base);
                            match (lhs_has, rhs_has) {
                                (true, false) => Some((**rhs).clone()),
                                (false, true) => Some((**lhs).clone()),
                                _ => None,
                            }
                        } else {
                            None
                        }
                    })
                    .expect("value expression for orphan range-proof not found")
            })
            .clone();

        if base + bits > trace_columns.len() {
            trace_columns
                .extend((0..(base + bits - trace_columns.len())).map(|_| vec![0u128; trace_len]));
        }

        for row in 0..trace_len {
            let val_raw = eval_air_expr(
                &val_expr,
                row,
                trace_len,
                &trace_columns,
                GoldilocksField::PRIME,
            );
            let (range_mod, half_mod) = if bits < 128 {
                let rm = 1u128 << bits;
                let hm = rm >> 1;
                (Some(rm), Some(hm))
            } else {
                (None, None)
            };

            let mut x_k = if grp.signed && bits > 0 {
                match half_mod {
                    Some(hm) => (val_raw + hm) % GoldilocksField::PRIME,
                    None => val_raw % GoldilocksField::PRIME,
                }
            } else {
                val_raw % GoldilocksField::PRIME
            };

            if let Some(rm) = range_mod {
                x_k %= rm;
            }

            for b in 0..bits {
                trace_columns[base + b][row] = (x_k >> b) & 1u128;
            }
            if grp.overflow_col >= trace_columns.len() {
                trace_columns.extend(
                    (0..=(grp.overflow_col - trace_columns.len())).map(|_| vec![0u128; trace_len]),
                );
            }
            let overflow_val = (val_raw - x_k) >> bits;
            trace_columns[grp.overflow_col][row] = overflow_val;
        }
    }

    let mut max_col = trace_columns.len() - 1;
    for expr in &air.constraints {
        collect_max_col(expr, &mut max_col);
    }
    if max_col + 1 > trace_columns.len() {
        trace_columns
            .extend((0..(max_col + 1 - trace_columns.len())).map(|_| vec![0u128; trace_len]));
    }

    #[cfg(test)]
    {
        println!(
            "DEBUG before solver (pre-clamp): is_write_row0={}, is_write_row1={}, addr_row0={}, addr_row1={}, reg4_row0={}, reg4_row1={} ",
            trace_columns[is_write_col][0],
            trace_columns[is_write_col][1],
            trace_columns[addr_col][0],
            trace_columns[addr_col][1],
            trace_columns[4][0],
            trace_columns[4][1]
        );
    }

    for row in 0..trace_len {
        let v = trace_columns[is_write_col][row];
        trace_columns[is_write_col][row] = if v == 0 { 0 } else { 1 };
    }

    #[cfg(test)]
    {
        println!(
            "DEBUG witness: addr_col={} row0 addr={} | row1 addr={} | col37 row0={}, row1={}",
            addr_col,
            trace_columns[addr_col][0],
            trace_columns[addr_col][1],
            trace_columns[37][0],
            trace_columns[37][1]
        );

        let row = memory_trace.len().saturating_sub(1);
        println!(
            "DEBUG final row{} helper block col{}={} col{}={}",
            row,
            aux_start_col + row * 2,
            trace_columns[aux_start_col + row * 2][row],
            aux_start_col + row * 2 + 1,
            trace_columns[aux_start_col + row * 2 + 1][row]
        );
    }

    for row in 0..trace_len {
        let v = trace_columns[is_write_col][row];
        trace_columns[is_write_col][row] = if v == 0 { 0 } else { 1 };
    }

    #[cfg(test)]
    {
        println!(
            "DEBUG after final clamp: is_write row0={} row1={} row2={} row3={}",
            trace_columns[is_write_col][0],
            trace_columns[is_write_col][1],
            trace_columns[is_write_col][2],
            trace_columns[is_write_col][3]
        );
    }

    let protected_cols: HashSet<usize> = (0..32)
        .chain([
            clk_col,
            addr_col,
            val_col,
            is_write_col,
            last_write_val_col,
            is_first_read_col,
        ])
        .collect();

    for row in 0..trace_len {
        for expr in &air.constraints {
            if let AirExpression::Sub(lhs, rhs) = expr {
                if let (
                    AirExpression::Add(a, b),
                    AirExpression::Trace(AirTraceVariable(dest), RowOffset::Current),
                ) = (&**lhs, &**rhs)
                {
                    if let (Some(src), Some(k)) = match (&**a, &**b) {
                        (
                            AirExpression::Trace(AirTraceVariable(s), RowOffset::Current),
                            AirExpression::Constant(c),
                        ) => (Some(*s), Some(*c)),
                        (
                            AirExpression::Constant(c),
                            AirExpression::Trace(AirTraceVariable(s), RowOffset::Current),
                        ) => (Some(*s), Some(*c)),
                        _ => (None, None),
                    } {
                        if !protected_cols.contains(dest) {
                            let val = (trace_columns[src][row] + k) % GoldilocksField::PRIME;
                            trace_columns[*dest][row] = val;
                        }
                        continue;
                    }
                }

                if let (
                    AirExpression::Trace(AirTraceVariable(dest), RowOffset::Current),
                    AirExpression::Add(a, b),
                ) = (&**lhs, &**rhs)
                {
                    if let (Some(src), Some(k)) = match (&**a, &**b) {
                        (
                            AirExpression::Trace(AirTraceVariable(s), RowOffset::Current),
                            AirExpression::Constant(c),
                        ) => (Some(*s), Some(*c)),
                        (
                            AirExpression::Constant(c),
                            AirExpression::Trace(AirTraceVariable(s), RowOffset::Current),
                        ) => (Some(*s), Some(*c)),
                        _ => (None, None),
                    } {
                        if !protected_cols.contains(dest) {
                            let val = (trace_columns[src][row] + k) % GoldilocksField::PRIME;
                            trace_columns[*dest][row] = val;
                        }
                        continue;
                    }
                }

                if let (
                    AirExpression::Add(a, b),
                    AirExpression::Trace(AirTraceVariable(dest), RowOffset::Current),
                ) = (&**lhs, &**rhs)
                {
                    if let (
                        AirExpression::Trace(AirTraceVariable(s1), RowOffset::Current),
                        AirExpression::Trace(AirTraceVariable(s2), RowOffset::Current),
                    ) = (&**a, &**b)
                    {
                        if !protected_cols.contains(dest) {
                            let val = (trace_columns[*s1][row] + trace_columns[*s2][row])
                                % GoldilocksField::PRIME;
                            trace_columns[*dest][row] = val;
                        }
                        continue;
                    }
                }

                if let (
                    AirExpression::Trace(AirTraceVariable(dest), RowOffset::Current),
                    AirExpression::Add(a, b),
                ) = (&**lhs, &**rhs)
                {
                    if let (
                        AirExpression::Trace(AirTraceVariable(s1), RowOffset::Current),
                        AirExpression::Trace(AirTraceVariable(s2), RowOffset::Current),
                    ) = (&**a, &**b)
                    {
                        if !protected_cols.contains(dest) {
                            let val = (trace_columns[*s1][row] + trace_columns[*s2][row])
                                % GoldilocksField::PRIME;
                            trace_columns[*dest][row] = val;
                        }
                        continue;
                    }
                }

                if let (
                    AirExpression::Sub(a, b),
                    AirExpression::Trace(AirTraceVariable(dest), RowOffset::Current),
                ) = (&**lhs, &**rhs)
                {
                    if let (
                        AirExpression::Trace(AirTraceVariable(src), RowOffset::Current),
                        AirExpression::Constant(k),
                    ) = (&**a, &**b)
                    {
                        if !protected_cols.contains(dest) {
                            let val = (trace_columns[*src][row] + GoldilocksField::PRIME
                                - (k % GoldilocksField::PRIME))
                                % GoldilocksField::PRIME;
                            trace_columns[*dest][row] = val;
                        }
                        continue;
                    }
                }

                if let (
                    AirExpression::Trace(AirTraceVariable(dest), RowOffset::Current),
                    AirExpression::Sub(a, b),
                ) = (&**lhs, &**rhs)
                {
                    if let (
                        AirExpression::Trace(AirTraceVariable(src), RowOffset::Current),
                        AirExpression::Constant(k),
                    ) = (&**a, &**b)
                    {
                        if !protected_cols.contains(dest) {
                            let val = (trace_columns[*src][row] + GoldilocksField::PRIME
                                - (k % GoldilocksField::PRIME))
                                % GoldilocksField::PRIME;
                            trace_columns[*dest][row] = val;
                        }
                        continue;
                    }
                }

                if let (
                    AirExpression::Trace(AirTraceVariable(a), RowOffset::Current),
                    AirExpression::Trace(AirTraceVariable(b), RowOffset::Current),
                ) = (&**lhs, &**rhs)
                {
                    let a_idx = *a;
                    let b_idx = *b;

                    let val_a = trace_columns[a_idx][row];
                    let val_b = trace_columns[b_idx][row];

                    if val_a == 0 && val_b != 0 && !protected_cols.contains(&a_idx) {
                        trace_columns[a_idx][row] = val_b;
                    } else if val_b == 0 && val_a != 0 && !protected_cols.contains(&b_idx) {
                        trace_columns[b_idx][row] = val_a;
                    }
                    continue;
                }
            }
        }
    }

    Ok(trace_columns)
}

pub fn evaluate_constraints(
    trace_columns: Vec<Vec<u128>>,
    llvm_ir: &str,
    _trace_len: usize,
) -> Result<(), String> {
    let field = GoldilocksField;
    let air = AirCodegen::generate_air(llvm_ir, &field)
        .map_err(|e| format!("Failed to generate AIR for constraint evaluation: {}", e))?;

    let constraint_provider = AirConstraintProvider {
        generated_air: air.clone(),
    };

    let rows = trace_columns.first().ok_or("trace_columns is empty")?.len();

    let evaluations = constraint_provider.get_constraints_evaluations(
        &field,
        &trace_columns,
        rows.next_power_of_two(),
        field.get_nth_root_of_unity(rows.next_power_of_two()),
        rows.next_power_of_two(),
        field.get_nth_root_of_unity(rows.next_power_of_two()),
        rows.next_power_of_two(),
    );

    for (c_idx, evals) in evaluations.iter().enumerate() {
        for idx in 1..rows - 1 {
            if evals[idx] != 0 {
                return Err(format!(
                    "Constraint #{} failed at row {} (value = {}), expr = {:?}",
                    c_idx, idx, evals[idx], air.constraints[c_idx]
                ));
            }
        }
    }
    Ok(())
}

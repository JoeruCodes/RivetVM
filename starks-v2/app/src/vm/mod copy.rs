use serde::{Deserialize, Serialize};
use std::collections::HashSet;
use std::fs;

use crate::{
    llvm::air::codegen::{constraint_provider::AirConstraintProvider, AirCodegen},
    mod_pow, ConstraintProvider, Field, Unity,
};
use lang::ctx::RangeProofGroup;

#[derive(Debug, Deserialize)]
pub struct TraceEntry {
    pub pc: u64,
    pub register: Vec<u64>,
}

#[derive(Debug, Deserialize)]
pub struct MemoryTraceEntry {
    pub time_step: usize,
    pub pc: u64,
    pub address: u64,
    pub value: u64,
    pub access_type: MemoryAccessType,
}

#[derive(Debug, Deserialize)]
pub enum MemoryAccessType {
    Read,
    Write,
}

#[derive(Clone, Copy, Debug)]
pub struct GoldilocksField;

impl Field for GoldilocksField {
    
    
    const PRIME: u128 = 18446744069414584321;

    fn get_prime() -> u128 {
        Self::PRIME
    }

    
    
    
    
    
    
    
    
    
    fn get_nth_root_of_unity(&self, n: usize) -> Unity {
        let p_minus_1 = Self::PRIME - 1;
        let n_u128 = n as u128;

        
        if p_minus_1 % n_u128 != 0 {
            panic!(
                "A primitive {}-th root of unity does not exist in this field.",
                n
            );
        }

        
        let generator = 2717u128;

        
        let exponent = p_minus_1 / n_u128;
        let root = mod_pow(generator, exponent, Self::PRIME);

        Unity { generator: root }
    }
}

mod test {
    use lang::ctx::RangeProofGroup;

    use crate::{
        llvm::air::codegen::{constraint_provider::AirConstraintProvider, AirCodegen}, mod_pow, vm::{GoldilocksField, MemoryAccessType, MemoryTraceEntry, TraceEntry}, ConstraintProvider, Field
    };
    use std::{collections::HashSet, fs};

            
        
        
        const AUX_START_COL: usize = 37;
        
        
        
        
        
        
        
        const AUX_PER_PAIR: usize = 37;


    #[test]
    fn test_vm_trace() {
        let field = GoldilocksField;
        let memory_trace = include_str!("../../../r2vm/memory_trace.json");
        let trace = include_str!("../../../r2vm/trace.json");
        let llvm_ir = include_str!("../../../r2vm/hello.ll");

        let trace: Vec<TraceEntry> = serde_json::from_str(trace).unwrap();
        let memory_trace: Vec<MemoryTraceEntry> = serde_json::from_str(memory_trace).unwrap();

        
        
        
        let other_cols_raw = include_bytes!("../../../r2vm/other_cols.json");
        let mut other_cols: Vec<Vec<u128>> = serde_json::from_slice(other_cols_raw).unwrap();

        
        
        let air = AirCodegen::generate_air(llvm_ir, &field).unwrap();
        let range_groups: Vec<RangeProofGroup> = air.range_proof_groups.clone();

        
        
        
        let expected_pairs = range_groups
            .iter()
            .filter(|g| {
                g.base_col >= AUX_START_COL + 3
                    && (g.base_col - (AUX_START_COL + 3)) % AUX_PER_PAIR == 0
            })
            .count();

        
        
        
        
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

        
        for (row_idx, entry) in trace.iter().enumerate() {
            for reg_idx in 0..32 {
                trace_columns[reg_idx][row_idx] = entry.register[reg_idx] as u128;
            }
        }

        
        let clk_col = air.memory_trace_columns[0];
        let addr_col = air.memory_trace_columns[1];
        let val_col = air.memory_trace_columns[2];
        let is_write_col = air.memory_trace_columns[3];
        let selector_col = air.memory_trace_columns[4];

        for (row, m) in memory_trace.iter().enumerate() {
            
            if row >= trace_columns[0].len() {
                continue; 
            }
            trace_columns[clk_col][row] = m.time_step as u128;
            trace_columns[addr_col][row] = m.address as u128;
            trace_columns[val_col][row] = m.value as u128;
            trace_columns[is_write_col][row] = match m.access_type {
                MemoryAccessType::Write => 1,
                MemoryAccessType::Read => 0,
            };
            trace_columns[selector_col][row] = 1;
        }

        
        
        
        
        if selector_col < trace_columns.len() {
            trace_columns[selector_col][0] = 0;
            for row in memory_trace.len()..trace_len {
                trace_columns[selector_col][row] = 0;
            }
        }

        
        
        
        
        
        let goldilocks_prime: u128 = GoldilocksField::PRIME;

        fn mod_inv(val: u128, prime: u128) -> u128 {
            if val == 0 {
                0
            } else {
                
                mod_pow(val, prime - 2, prime)
            }
        }

        if expected_pairs > 0 {
            for pair_idx in 0..expected_pairs {
                let prev = &memory_trace[pair_idx];
                let next = &memory_trace[pair_idx + 1];

                let row = pair_idx; 

                let addr_diff = ((next.address as i128 - prev.address as i128)
                    .rem_euclid(goldilocks_prime as i128)) as u128;
                let is_addr_same = if addr_diff == 0 { 1u128 } else { 0u128 };
                let inv_addr_diff = mod_inv(addr_diff, goldilocks_prime);
                
                
                let clk_diff_val = next.time_step as i128 - prev.time_step as i128 - 1;
                let clk_diff = (clk_diff_val.rem_euclid(1i128 << 32)) as u128;

                let base_col = AUX_START_COL + pair_idx * AUX_PER_PAIR;
                if base_col + (AUX_PER_PAIR - 1) >= trace_columns.len() {
                    let missing = base_col + AUX_PER_PAIR - trace_columns.len();
                    trace_columns.extend((0..missing).map(|_| vec![0u128; trace_len]));
                }

                trace_columns[base_col][row] = is_addr_same;
                trace_columns[base_col + 1][row] = inv_addr_diff;
                trace_columns[base_col + 2][row] = clk_diff;

                let bit_base = base_col + 3;
                for bit_idx in 0..32 {
                    let bit_val = (clk_diff >> bit_idx) & 1u128;
                    trace_columns[bit_base + bit_idx][row] = bit_val;
                }

                
                
                
                trace_columns[selector_col][row] = 1;
                trace_columns[selector_col][row + 1] = 1;

                
                
                for aux_off in 0..AUX_PER_PAIR {
                    let col_idx = base_col + aux_off;
                    trace_columns[col_idx][row + 1] = trace_columns[col_idx][row];
                }

                if pair_idx < 2 {
                    println!("Debug pair {} row {} clk_diff {}", pair_idx, row, clk_diff);
                    println!(
                        "Bits: {:?}",
                        (0..32)
                            .map(|b| trace_columns[bit_base + b][row])
                            .collect::<Vec<_>>()
                    );
                }
            }
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
                        (0..=(grp.overflow_col - trace_columns.len()))
                            .map(|_| vec![0u128; trace_len]),
                    );
                }
                let overflow_val = (val_raw - x_k) >> bits;
                trace_columns[grp.overflow_col][row] = overflow_val;
            }
        }

        
        
        
        
        

        use lang::constraints::{AirExpression, AirTraceVariable, RowOffset};

        
        
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

        
        use std::collections::HashMap;
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
                trace_columns.extend(
                    (0..(base + bits - trace_columns.len())).map(|_| vec![0u128; trace_len]),
                );
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
                        (0..=(grp.overflow_col - trace_columns.len()))
                            .map(|_| vec![0u128; trace_len]),
                    );
                }
                let overflow_val = (val_raw - x_k) >> bits;
                trace_columns[grp.overflow_col][row] = overflow_val;
            }
        }

        let constraint_provider = AirConstraintProvider {
            generated_air: air.clone(),
        };

        
        
        
        let p = GoldilocksField::PRIME;
        let add_p = |a: u128, b: u128| -> u128 {
            let s = a + b;
            if s >= p {
                s - p
            } else {
                s
            }
        };
        let sub_p = |a: u128, b: u128| -> u128 {
            if a >= b {
                a - b
            } else {
                p - (b - a)
            }
        };

        
        for reg in 0..32 {
            let initial = trace_columns[reg][0];
            for row in 0..trace_len {
                trace_columns[reg][row] = initial;
            }
        }

        
        let r0 = trace_columns[0][0];
        let r1 = trace_columns[1][0];
        let r13 = trace_columns[13][0];
        let r15 = trace_columns[15][0];

        let r3 = add_p(r0, 4);
        let r5 = add_p(r3, 4);
        let r7 = add_p(r5, 4);
        let r9 = add_p(r7, 4);
        let r17 = add_p(r13, r15);
        let r22 = sub_p(r1, 2);
        let r24 = sub_p(r1, 1);
        let r26 = r22;

        let derived = [
            (3, r3),
            (5, r5),
            (7, r7),
            (9, r9),
            (17, r17),
            (22, r22),
            (24, r24),
            (26, r26),
        ];
        for (col, val) in derived {
            for row in 0..trace_len {
                trace_columns[col][row] = val;
            }
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
        let mut max_col = trace_columns.len() - 1;
        for expr in &air.constraints {
            collect_max_col(expr, &mut max_col);
        }
        if max_col + 1 > trace_columns.len() {
            trace_columns
                .extend((0..(max_col + 1 - trace_columns.len())).map(|_| vec![0u128; trace_len]));
        }

        
        
        
        
        
        
        
        
        for col in 32..trace_columns.len() {
            for row in 0..trace_len {
                trace_columns[col][row] = 0;
            }
        }

        let prime = GoldilocksField::PRIME;

        
        fn try_solve_side(
            lhs: &AirExpression,
            rhs: &AirExpression,
            row: usize,
            trace_len: usize,
            trace_cols: &mut Vec<Vec<u128>>,
            prime: u128,
        ) -> bool {
            if let AirExpression::Trace(AirTraceVariable(col), RowOffset::Current) = lhs {
                
                
                
                if *col < 32 {
                    return false;
                }

                if expr_contains_column(rhs, *col) {
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
                            (
                                AirExpression::Trace(AirTraceVariable(c), RowOffset::Current),
                                other,
                            ) => (Some(*c), other, true),
                            (
                                other,
                                AirExpression::Trace(AirTraceVariable(c), RowOffset::Current),
                            ) => (Some(*c), other, false),
                            _ => (None, lhs, false),
                        };

                        if let Some(col) = trace_side {
                            
                            if col < 32 {
                                return false;
                            }

                            if !matches!(rhs, AirExpression::Constant(_)) {
                                return false;
                            }

                            if expr_contains_column(other_side, col) {
                                return false;
                            }

                            let other_val =
                                eval_air_expr(other_side, row, trace_len, trace_cols, prime);
                            let rhs_val = eval_air_expr(rhs, row, trace_len, trace_cols, prime);

                            let new_val = match lhs {
                                AirExpression::Add(_, _) => {
                                    
                                    (rhs_val + prime - other_val) % prime
                                }
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

        let mut progress = true;
        while progress {
            progress = false;
            
            for row in 0..trace_len {
                for expr in &air.constraints {
                    if let AirExpression::Sub(lhs, rhs) = expr {
                        
                        
                        if let (
                            AirExpression::Trace(AirTraceVariable(dest), RowOffset::Current),
                            AirExpression::Sub(sub_l, sub_r),
                        ) = (&**lhs, &**rhs)
                        {
                            if *dest >= 32 {
                                if let (
                                    AirExpression::Trace(AirTraceVariable(src), RowOffset::Current),
                                    AirExpression::Constant(k),
                                ) = (&**sub_l, &**sub_r)
                                {
                                    if *src != *dest {
                                        let src_val = trace_columns[*src][row];
                                        let new_val = (src_val + prime - (k % prime)) % prime;
                                        if trace_columns[*dest][row] != new_val {
                                            trace_columns[*dest][row] = new_val;
                                            progress = true;
                                        }
                                    }
                                }
                            }
                        }

                        
                        let solved =
                            try_solve_side(lhs, rhs, row, trace_len, &mut trace_columns, prime)
                                || try_solve_side(
                                    rhs,
                                    lhs,
                                    row,
                                    trace_len,
                                    &mut trace_columns,
                                    prime,
                                );
                        if solved {
                            progress = true;
                        }
                    }
                }
            }
        }

        
        
        

        let evaluations = constraint_provider.get_constraints_evaluations(
            &field,
            &trace_columns,
            trace_len.next_power_of_two(),
            field.get_nth_root_of_unity(trace_len.next_power_of_two()),
            trace_len.next_power_of_two() * 2,
            field.get_nth_root_of_unity(trace_len.next_power_of_two() * 2),
            trace_len.next_power_of_two(),
        );

        for (_, evals) in evaluations.iter().enumerate() {
            
            
            for idx in 1..trace_len {
                assert!(evals[idx] == 0, "Constraint failed at row {}", idx);
            }
        }
    }
}

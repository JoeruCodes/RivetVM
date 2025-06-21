use lang::constraints::{AirExpression, RowOffset};

use crate::llvm::air::codegen::GeneratedAir;
use crate::{ConstraintProvider, Field, Unity};

pub struct AirConstraintProvider<F: Field + Clone> {
    pub generated_air: GeneratedAir<F>,
}

impl<F: Field + Clone> AirConstraintProvider<F> {
    fn mod_pow(mut base: u128, mut exp: u128, modulus: u128) -> u128 {
        let mut res = 1;
        base %= modulus;
        while exp > 0 {
            if exp % 2 == 1 {
                res = (res * base) % modulus;
            }
            base = (base * base) % modulus;
            exp /= 2;
        }
        res
    }

    fn eval_poly(coeffs: &Vec<u128>, x: u128, prime: u128) -> u128 {
        let mut result = 0;
        for &coeff in coeffs.iter().rev() {
            result = (result * x + coeff) % prime;
        }
        result
    }

    fn eval_air_expr(
        expr: &AirExpression,
        idx: usize,
        domain_size: usize,
        trace_eval_columns: &Vec<Vec<u128>>,
        prime: u128,
    ) -> u128 {
        match expr {
            AirExpression::Constant(c) => *c % prime,
            AirExpression::Add(lhs, rhs) => {
                let l =
                    Self::eval_air_expr(lhs, idx, domain_size, trace_eval_columns, prime) % prime;
                let r =
                    Self::eval_air_expr(rhs, idx, domain_size, trace_eval_columns, prime) % prime;
                (l + r) % prime
            }
            AirExpression::Sub(lhs, rhs) => {
                let l =
                    Self::eval_air_expr(lhs, idx, domain_size, trace_eval_columns, prime) % prime;
                let r =
                    Self::eval_air_expr(rhs, idx, domain_size, trace_eval_columns, prime) % prime;
                (l + prime - r) % prime
            }
            AirExpression::Mul(lhs, rhs) => {
                let l =
                    Self::eval_air_expr(lhs, idx, domain_size, trace_eval_columns, prime) % prime;
                let r =
                    Self::eval_air_expr(rhs, idx, domain_size, trace_eval_columns, prime) % prime;
                (l * r) % prime
            }
            AirExpression::Trace(var, offset) => {
                let column_index = var.0 as usize;
                if column_index >= trace_eval_columns.len() {
                    return 0;
                }
                let col = &trace_eval_columns[column_index];
                let effective_idx = match offset {
                    RowOffset::Current => idx,
                    RowOffset::Next => (idx + 1) % domain_size,
                };
                col[effective_idx]
            }

            _ => 0,
        }
    }
}

impl<F: Field + Clone> ConstraintProvider for AirConstraintProvider<F> {
    fn get_constraints_evaluations<FieldType: Field + Clone>(
        &self,
        _field: &FieldType,
        trace_coeffs: &Vec<Vec<u128>>,
        _initial_domain_sz: usize,
        _initial_root_of_unity: Unity,
        expanded_domain_sz: usize,
        expanded_root_of_unity: Unity,
        _trace_len_original: usize,
    ) -> Vec<Vec<u128>> {
        let prime = FieldType::PRIME;

        let trace_eval_columns = trace_coeffs
            .iter()
            .map(|col_vals| {
                if col_vals.len() >= expanded_domain_sz {
                    col_vals[..expanded_domain_sz].to_vec()
                } else {
                    let mut padded = vec![0u128; expanded_domain_sz];
                    padded[..col_vals.len()].copy_from_slice(col_vals);
                    padded
                }
            })
            .collect::<Vec<_>>();

        let mut constraints_evals = Vec::new();
        for expr in &self.generated_air.constraints {
            let mut evals = Vec::with_capacity(expanded_domain_sz);
            for idx in 0..expanded_domain_sz {
                let val =
                    Self::eval_air_expr(expr, idx, expanded_domain_sz, &trace_eval_columns, prime);
                evals.push(val);
            }
            constraints_evals.push(evals);
        }

        constraints_evals
    }
}

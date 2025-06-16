use lang::constraints::{AirExpression, AirTraceVariable, RowOffset};
use lang::ctx::AirGenContext;

use lang::constraints::lang_operand_to_air_expression;

fn new_boolean_aux(
    ctx: &mut AirGenContext,
    constraints: &mut Vec<AirExpression>,
    _name_hint: &str,
) -> AirExpression {
    let aux_var = ctx.new_aux_variable();
    let aux_expr = AirExpression::Trace(aux_var, RowOffset::Current);

    constraints.push(AirExpression::Mul(
        Box::new(aux_expr.clone()),
        Box::new(AirExpression::Sub(
            Box::new(aux_expr.clone()),
            Box::new(AirExpression::Constant(1)),
        )),
    ));
    aux_expr
}

fn fp_decompose_unsigned(
    val_expr: &AirExpression,
    num_bits: u32,
    ctx: &mut AirGenContext,
    constraints: &mut Vec<AirExpression>,
    hint_prefix: &str,
) -> Vec<AirExpression> {
    let mut bit_exprs = Vec::new();
    let mut sum_terms = AirExpression::Constant(0);

    if num_bits == 0 {
        constraints.push(val_expr.clone());
        return bit_exprs;
    }

    for i in 0..num_bits {
        let bit_aux_var = ctx.new_aux_variable();
        let bit_expr = AirExpression::Trace(bit_aux_var, RowOffset::Current);

        constraints.push(AirExpression::Mul(
            Box::new(bit_expr.clone()),
            Box::new(AirExpression::Sub(
                Box::new(bit_expr.clone()),
                Box::new(AirExpression::Constant(1)),
            )),
        ));
        bit_exprs.push(bit_expr.clone());

        let power_of_2_val = 1u128 << i;
        sum_terms = AirExpression::Add(
            Box::new(sum_terms),
            Box::new(AirExpression::Mul(
                Box::new(bit_expr.clone()),
                Box::new(AirExpression::Constant(power_of_2_val)),
            )),
        );
    }

    constraints.push(AirExpression::Sub(
        Box::new(val_expr.clone()),
        Box::new(sum_terms),
    ));

    bit_exprs
}

fn fp_reconstruct_from_bits(
    bits: &[AirExpression],
    ctx: &mut AirGenContext,
    constraints: &mut Vec<AirExpression>,
    hint_prefix: &str,
) -> AirExpression {
    if bits.is_empty() {
        return AirExpression::Constant(0);
    }
    let res_aux_var = ctx.new_aux_variable();
    let res_expr = AirExpression::Trace(res_aux_var, RowOffset::Current);

    let mut sum_terms = AirExpression::Constant(0);
    for (i, bit_expr) in bits.iter().enumerate() {
        let power_of_2_val = 1u128 << i;
        sum_terms = AirExpression::Add(
            Box::new(sum_terms),
            Box::new(AirExpression::Mul(
                Box::new(bit_expr.clone()),
                Box::new(AirExpression::Constant(power_of_2_val)),
            )),
        );
    }
    constraints.push(AirExpression::Sub(
        Box::new(res_expr.clone()),
        Box::new(sum_terms),
    ));
    res_expr
}

fn fp_logical_or_many(
    inputs: &[AirExpression],
    ctx: &mut AirGenContext,
    constraints: &mut Vec<AirExpression>,
    hint_prefix: &str,
) -> AirExpression {
    if inputs.is_empty() {
        return AirExpression::Constant(0);
    }
    if inputs.len() == 1 {
        return inputs[0].clone();
    }

    let mut current_or_res = inputs[0].clone();
    for i in 1..inputs.len() {
        current_or_res = fp_logical_or(
            &current_or_res,
            &inputs[i],
            ctx,
            constraints,
            &format!("{}_or_many_step{}", hint_prefix, i),
        );
    }
    current_or_res
}

pub fn fp_logical_and(
    a: &AirExpression,
    b: &AirExpression,
    ctx: &mut AirGenContext,
    constraints: &mut Vec<AirExpression>,
    hint_prefix: &str,
) -> AirExpression {
    let res_aux = new_boolean_aux(ctx, constraints, &format!("{}_and_res", hint_prefix));
    constraints.push(AirExpression::Sub(
        Box::new(res_aux.clone()),
        Box::new(AirExpression::Mul(Box::new(a.clone()), Box::new(b.clone()))),
    ));
    res_aux
}

pub fn fp_logical_or(
    a: &AirExpression,
    b: &AirExpression,
    ctx: &mut AirGenContext,
    constraints: &mut Vec<AirExpression>,
    hint_prefix: &str,
) -> AirExpression {
    let res_aux = new_boolean_aux(ctx, constraints, &format!("{}_or_res", hint_prefix));
    let a_plus_b = AirExpression::Add(Box::new(a.clone()), Box::new(b.clone()));
    let a_times_b = AirExpression::Mul(Box::new(a.clone()), Box::new(b.clone()));
    constraints.push(AirExpression::Sub(
        Box::new(res_aux.clone()),
        Box::new(AirExpression::Sub(Box::new(a_plus_b), Box::new(a_times_b))),
    ));
    res_aux
}

pub fn fp_logical_not(
    a: &AirExpression,
    ctx: &mut AirGenContext,
    constraints: &mut Vec<AirExpression>,
    hint_prefix: &str,
) -> AirExpression {
    let res_aux = new_boolean_aux(ctx, constraints, &format!("{}_not_res", hint_prefix));
    constraints.push(AirExpression::Sub(
        Box::new(res_aux.clone()),
        Box::new(AirExpression::Sub(
            Box::new(AirExpression::Constant(1)),
            Box::new(a.clone()),
        )),
    ));
    res_aux
}

pub fn fp_is_value_equal(
    val1_expr: &AirExpression,
    val2_expr: &AirExpression,
    ctx: &mut AirGenContext,
    constraints: &mut Vec<AirExpression>,
    hint_prefix: &str,
) -> AirExpression {
    let res_eq_aux_var = ctx.new_aux_variable();
    let res_eq_aux = AirExpression::Trace(res_eq_aux_var, RowOffset::Current);
    println!(
        "      fp_is_value_equal: {}_is_eq_aux_var: {:?}",
        hint_prefix, res_eq_aux_var
    );
    constraints.push(AirExpression::Mul(
        Box::new(res_eq_aux.clone()),
        Box::new(AirExpression::Sub(
            Box::new(res_eq_aux.clone()),
            Box::new(AirExpression::Constant(1)),
        )),
    ));

    let diff_expr = AirExpression::Sub(Box::new(val1_expr.clone()), Box::new(val2_expr.clone()));

    constraints.push(AirExpression::Mul(
        Box::new(res_eq_aux.clone()),
        Box::new(diff_expr.clone()),
    ));

    let inv_diff_aux_var = ctx.new_aux_variable();
    let inv_diff_expr = AirExpression::Trace(inv_diff_aux_var, RowOffset::Current);
    println!(
        "      fp_is_value_equal: {}_inv_diff_aux_var: {:?}",
        hint_prefix, inv_diff_aux_var
    );

    let one_minus_res_eq = AirExpression::Sub(
        Box::new(AirExpression::Constant(1)),
        Box::new(res_eq_aux.clone()),
    );
    let product_term =
        AirExpression::Mul(Box::new(diff_expr.clone()), Box::new(inv_diff_expr.clone()));
    let term_minus_one =
        AirExpression::Sub(Box::new(product_term), Box::new(AirExpression::Constant(1)));
    constraints.push(AirExpression::Mul(
        Box::new(one_minus_res_eq),
        Box::new(term_minus_one),
    ));

    res_eq_aux
}

pub fn fp_is_value_zero(
    val_expr: &AirExpression,
    ctx: &mut AirGenContext,
    constraints: &mut Vec<AirExpression>,
    hint_prefix: &str,
) -> AirExpression {
    fp_is_value_equal(
        val_expr,
        &AirExpression::Constant(0),
        ctx,
        constraints,
        &format!("{}_is_zero", hint_prefix),
    )
}

pub fn fp_is_all_ones(
    val_expr: &AirExpression,
    bit_count: u32,
    ctx: &mut AirGenContext,
    constraints: &mut Vec<AirExpression>,
    hint_prefix: &str,
) -> AirExpression {
    if bit_count == 0 {
        return fp_is_value_equal(
            val_expr,
            &AirExpression::Constant(0),
            ctx,
            constraints,
            &format!("{}_is_all_ones_b0", hint_prefix),
        );
    }
    let max_val = (1u128 << bit_count) - 1;
    fp_is_value_equal(
        val_expr,
        &AirExpression::Constant(max_val),
        ctx,
        constraints,
        &format!("{}_is_all_ones_b{}", hint_prefix, bit_count),
    )
}

pub fn fp_is_nan(
    exp_val_expr: &AirExpression,
    mant_val_expr: &AirExpression,
    exp_bit_count: u32,
    mant_bit_count: u32,
    ctx: &mut AirGenContext,
    constraints: &mut Vec<AirExpression>,
    hint_prefix: &str,
) -> AirExpression {
    let exp_is_all_ones = fp_is_all_ones(
        exp_val_expr,
        exp_bit_count,
        ctx,
        constraints,
        &format!("{}_exp_all_ones_nan", hint_prefix),
    );
    let mant_is_zero = fp_is_value_zero(
        mant_val_expr,
        ctx,
        constraints,
        &format!("{}_mant_zero_nan", hint_prefix),
    );
    let mant_is_nonzero = fp_logical_not(
        &mant_is_zero,
        ctx,
        constraints,
        &format!("{}_mant_nonzero_nan", hint_prefix),
    );

    fp_logical_and(
        &exp_is_all_ones,
        &mant_is_nonzero,
        ctx,
        constraints,
        &format!("{}_is_nan", hint_prefix),
    )
}

pub fn fp_is_inf(
    exp_val_expr: &AirExpression,
    mant_val_expr: &AirExpression,
    exp_bit_count: u32,
    _mant_bit_count: u32,
    ctx: &mut AirGenContext,
    constraints: &mut Vec<AirExpression>,
    hint_prefix: &str,
) -> AirExpression {
    let exp_is_all_ones = fp_is_all_ones(
        exp_val_expr,
        exp_bit_count,
        ctx,
        constraints,
        &format!("{}_exp_all_ones_inf", hint_prefix),
    );
    let mant_is_zero = fp_is_value_zero(
        mant_val_expr,
        ctx,
        constraints,
        &format!("{}_mant_zero_inf", hint_prefix),
    );

    fp_logical_and(
        &exp_is_all_ones,
        &mant_is_zero,
        ctx,
        constraints,
        &format!("{}_is_inf", hint_prefix),
    )
}

pub fn fp_is_true_zero(
    exp_val_expr: &AirExpression,
    mant_val_expr: &AirExpression,
    _exp_bit_count: u32,
    _mant_bit_count: u32,
    ctx: &mut AirGenContext,
    constraints: &mut Vec<AirExpression>,
    hint_prefix: &str,
) -> AirExpression {
    let exp_is_zero = fp_is_value_zero(
        exp_val_expr,
        ctx,
        constraints,
        &format!("{}_exp_zero_truezero", hint_prefix),
    );
    let mant_is_zero = fp_is_value_zero(
        mant_val_expr,
        ctx,
        constraints,
        &format!("{}_mant_zero_truezero", hint_prefix),
    );

    fp_logical_and(
        &exp_is_zero,
        &mant_is_zero,
        ctx,
        constraints,
        &format!("{}_is_true_zero", hint_prefix),
    )
}

pub fn fp_select(
    cond_expr: &AirExpression,
    val_if_true: &AirExpression,
    val_if_false: &AirExpression,
    ctx: &mut AirGenContext,
    constraints: &mut Vec<AirExpression>,
    hint_prefix: &str,
) -> AirExpression {
    let res_aux_var = ctx.new_aux_variable();
    let res_expr = AirExpression::Trace(res_aux_var, RowOffset::Current);
    println!(
        "      fp_select: {}_select_res_var: {:?}",
        hint_prefix, res_aux_var
    );

    let term_true = AirExpression::Mul(Box::new(cond_expr.clone()), Box::new(val_if_true.clone()));
    let one_minus_cond = AirExpression::Sub(
        Box::new(AirExpression::Constant(1)),
        Box::new(cond_expr.clone()),
    );
    let term_false = AirExpression::Mul(Box::new(one_minus_cond), Box::new(val_if_false.clone()));

    constraints.push(AirExpression::Sub(
        Box::new(res_expr.clone()),
        Box::new(AirExpression::Add(
            Box::new(term_true),
            Box::new(term_false),
        )),
    ));
    res_expr
}

pub fn fp_add(
    a: &AirExpression,
    b: &AirExpression,
    ctx: &mut AirGenContext,
    constraints: &mut Vec<AirExpression>,
    hint_prefix: &str,
) -> AirExpression {
    let res_aux_var = ctx.new_aux_variable();
    let res_expr = AirExpression::Trace(res_aux_var, RowOffset::Current);
    println!("      fp_add: {}_res_var: {:?}", hint_prefix, res_aux_var);

    constraints.push(AirExpression::Sub(
        Box::new(res_expr.clone()),
        Box::new(AirExpression::Add(Box::new(a.clone()), Box::new(b.clone()))),
    ));
    res_expr
}

pub fn fp_sub(
    a: &AirExpression,
    b: &AirExpression,
    ctx: &mut AirGenContext,
    constraints: &mut Vec<AirExpression>,
    hint_prefix: &str,
) -> AirExpression {
    let res_aux_var = ctx.new_aux_variable();
    let res_expr = AirExpression::Trace(res_aux_var, RowOffset::Current);
    println!("      fp_sub: {}_res_var: {:?}", hint_prefix, res_aux_var);

    constraints.push(AirExpression::Sub(
        Box::new(res_expr.clone()),
        Box::new(AirExpression::Sub(Box::new(a.clone()), Box::new(b.clone()))),
    ));
    res_expr
}

pub fn fp_mul(
    a: &AirExpression,
    b: &AirExpression,
    ctx: &mut AirGenContext,
    constraints: &mut Vec<AirExpression>,
    hint_prefix: &str,
) -> AirExpression {
    let res_aux_var = ctx.new_aux_variable();
    let res_expr = AirExpression::Trace(res_aux_var, RowOffset::Current);
    println!("      fp_mul: {}_res_var: {:?}", hint_prefix, res_aux_var);

    constraints.push(AirExpression::Sub(
        Box::new(res_expr.clone()),
        Box::new(AirExpression::Mul(Box::new(a.clone()), Box::new(b.clone()))),
    ));
    res_expr
}

pub fn fp_icmp_eq(
    op1: &AirExpression,
    op2: &AirExpression,
    ctx: &mut AirGenContext,
    constraints: &mut Vec<AirExpression>,
    hint_prefix: &str,
) -> AirExpression {
    fp_is_value_equal(op1, op2, ctx, constraints, hint_prefix)
}

pub fn fp_icmp_neq(
    op1: &AirExpression,
    op2: &AirExpression,
    ctx: &mut AirGenContext,
    constraints: &mut Vec<AirExpression>,
    hint_prefix: &str,
) -> AirExpression {
    let eq_res = fp_is_value_equal(
        op1,
        op2,
        ctx,
        constraints,
        &format!("{}_neq_internal_eq", hint_prefix),
    );
    fp_logical_not(&eq_res, ctx, constraints, hint_prefix)
}

pub fn fp_icmp_ult(
    op1: &AirExpression,
    op2: &AirExpression,
    bit_width: u32,
    ctx: &mut AirGenContext,
    constraints: &mut Vec<AirExpression>,
    hint_prefix: &str,
) -> AirExpression {
    let res_ult_var = ctx.new_aux_variable();
    let res_ult_expr = AirExpression::Trace(res_ult_var, RowOffset::Current);
    println!(
        "      fp_icmp_ult: {}_res_ult_var: {:?}",
        hint_prefix, res_ult_var
    );

    constraints.push(AirExpression::Mul(
        Box::new(res_ult_expr.clone()),
        Box::new(AirExpression::Sub(
            Box::new(res_ult_expr.clone()),
            Box::new(AirExpression::Constant(1)),
        )),
    ));

    let mut d_sum_bit_vars_exprs = Vec::new();
    for i in 0..bit_width {
        let bit_aux_var = ctx.new_aux_variable();
        let bit_expr_d = AirExpression::Trace(bit_aux_var, RowOffset::Current);
        constraints.push(AirExpression::Mul(
            Box::new(bit_expr_d.clone()),
            Box::new(AirExpression::Sub(
                Box::new(bit_expr_d.clone()),
                Box::new(AirExpression::Constant(1)),
            )),
        ));
        d_sum_bit_vars_exprs.push(bit_expr_d);
    }
    let d_sum_air = d_sum_bit_vars_exprs.iter().enumerate().fold(
        AirExpression::Constant(0),
        |acc, (i, bit_e)| {
            AirExpression::Add(
                Box::new(acc),
                Box::new(AirExpression::Mul(
                    Box::new(bit_e.clone()),
                    Box::new(AirExpression::Constant(1u128 << i)),
                )),
            )
        },
    );

    let b_minus_a_minus_1 = AirExpression::Sub(
        Box::new(AirExpression::Sub(
            Box::new(op2.clone()),
            Box::new(op1.clone()),
        )),
        Box::new(AirExpression::Constant(1)),
    );
    let term1_val = AirExpression::Sub(Box::new(b_minus_a_minus_1), Box::new(d_sum_air.clone()));
    constraints.push(AirExpression::Mul(
        Box::new(res_ult_expr.clone()),
        Box::new(term1_val),
    ));

    let one_minus_res_ult = AirExpression::Sub(
        Box::new(AirExpression::Constant(1)),
        Box::new(res_ult_expr.clone()),
    );
    let a_minus_b = AirExpression::Sub(Box::new(op1.clone()), Box::new(op2.clone()));
    let term2_val = AirExpression::Sub(Box::new(a_minus_b), Box::new(d_sum_air.clone()));
    constraints.push(AirExpression::Mul(
        Box::new(one_minus_res_ult),
        Box::new(term2_val),
    ));

    res_ult_expr
}

pub fn fp_icmp_ule(
    op1: &AirExpression,
    op2: &AirExpression,
    bit_width: u32,
    ctx: &mut AirGenContext,
    constraints: &mut Vec<AirExpression>,
    hint_prefix: &str,
) -> AirExpression {
    let op2_lt_op1 = fp_icmp_ult(
        op2,
        op1,
        bit_width,
        ctx,
        constraints,
        &format!("{}_ule_internal_ult", hint_prefix),
    );
    fp_logical_not(&op2_lt_op1, ctx, constraints, hint_prefix)
}

pub fn fp_icmp_uge(
    op1: &AirExpression,
    op2: &AirExpression,
    bit_width: u32,
    ctx: &mut AirGenContext,
    constraints: &mut Vec<AirExpression>,
    hint_prefix: &str,
) -> AirExpression {
    fp_icmp_ule(
        op2,
        op1,
        bit_width,
        ctx,
        constraints,
        &format!("{}_uge_internal_ule", hint_prefix),
    )
}

#[allow(clippy::too_many_arguments)]
pub fn fp_variable_right_shift_with_grs(
    val_to_shift: &AirExpression,
    shift_amount_expr: &AirExpression,
    val_bit_width: u32,
    max_shift_val: u32,
    ctx: &mut AirGenContext,
    constraints: &mut Vec<AirExpression>,
    hint_prefix: &str,
) -> (AirExpression, AirExpression, AirExpression, AirExpression) {
    if val_bit_width == 0 {
        return (
            AirExpression::Constant(0),
            AirExpression::Constant(0),
            AirExpression::Constant(0),
            AirExpression::Constant(0),
        );
    }

    let shift_amount_bit_width = if max_shift_val == 0 {
        0
    } else {
        (max_shift_val as f64).log2().ceil() as u32
    };

    let (final_shifted_val_expr, _remainder) = fp_variable_division(
        val_to_shift,
        shift_amount_expr,
        val_bit_width,
        shift_amount_bit_width,
        ctx,
        constraints,
        &format!("{}_vrs_div", hint_prefix),
    );

    let shift_amount_bits = fp_decompose_unsigned(
        shift_amount_expr,
        shift_amount_bit_width,
        ctx,
        constraints,
        &format!("{}_shift_amt_decomp", hint_prefix),
    );
    let val_bits = fp_decompose_unsigned(
        val_to_shift,
        val_bit_width,
        ctx,
        constraints,
        &format!("{}_val_decomp", hint_prefix),
    );

    let mut sum_g_bit = AirExpression::Constant(0);
    let mut sum_r_bit = AirExpression::Constant(0);
    let mut sum_s_bit = AirExpression::Constant(0);

    for k_u32 in 0..=max_shift_val {
        let k = k_u32 as usize;
        let k_str = format!("{}_k{}", hint_prefix, k_u32);

        let mut terms_for_eq_k = Vec::new();
        for i_u32 in 0..shift_amount_bit_width {
            let i = i_u32 as usize;
            let k_bit_i = (k_u32 >> i_u32) & 1;
            if k_bit_i == 1 {
                terms_for_eq_k.push(shift_amount_bits[i].clone());
            } else {
                terms_for_eq_k.push(fp_logical_not(
                    &shift_amount_bits[i],
                    ctx,
                    constraints,
                    &format!("{}_not_s{}", k_str, i),
                ));
            }
        }
        let is_shift_eq_k = if terms_for_eq_k.is_empty() && k_u32 == 0 {
            AirExpression::Constant(1)
        } else if terms_for_eq_k.is_empty() {
            AirExpression::Constant(0)
        } else {
            let mut current_and = terms_for_eq_k[0].clone();
            for i in 1..terms_for_eq_k.len() {
                current_and = fp_logical_and(
                    &current_and,
                    &terms_for_eq_k[i],
                    ctx,
                    constraints,
                    &format!("{}_eq_k_and_s{}", k_str, i),
                );
            }
            current_and
        };

        let g_bit_if_k = if k > 0 && (k - 1) < val_bit_width as usize {
            val_bits[k - 1].clone()
        } else {
            AirExpression::Constant(0)
        };

        let r_bit_if_k = if k > 1 && (k - 2) < val_bit_width as usize {
            val_bits[k - 2].clone()
        } else {
            AirExpression::Constant(0)
        };

        let mut sticky_source_bits_if_k = Vec::new();
        if k > 2 {
            for i_u32 in 0..(k - 2) as u32 {
                let i = i_u32 as usize;
                if i < val_bit_width as usize {
                    sticky_source_bits_if_k.push(val_bits[i].clone());
                }
            }
        }
        let s_bit_if_k = fp_logical_or_many(
            &sticky_source_bits_if_k,
            ctx,
            constraints,
            &format!("{}_sticky_or", k_str),
        );

        sum_g_bit = AirExpression::Add(
            Box::new(sum_g_bit),
            Box::new(fp_mul(
                &is_shift_eq_k,
                &g_bit_if_k,
                ctx,
                constraints,
                &format!("{}_sum_g_mul", k_str),
            )),
        );
        sum_r_bit = AirExpression::Add(
            Box::new(sum_r_bit),
            Box::new(fp_mul(
                &is_shift_eq_k,
                &r_bit_if_k,
                ctx,
                constraints,
                &format!("{}_sum_r_mul", k_str),
            )),
        );
        sum_s_bit = AirExpression::Add(
            Box::new(sum_s_bit),
            Box::new(fp_mul(
                &is_shift_eq_k,
                &s_bit_if_k,
                ctx,
                constraints,
                &format!("{}_sum_s_mul", k_str),
            )),
        );
    }

    let final_g_aux = new_boolean_aux(ctx, constraints, &format!("{}_final_g_bool", hint_prefix));
    constraints.push(AirExpression::Sub(
        Box::new(final_g_aux.clone()),
        Box::new(sum_g_bit),
    ));

    let final_r_aux = new_boolean_aux(ctx, constraints, &format!("{}_final_r_bool", hint_prefix));
    constraints.push(AirExpression::Sub(
        Box::new(final_r_aux.clone()),
        Box::new(sum_r_bit),
    ));

    let final_s_aux = new_boolean_aux(ctx, constraints, &format!("{}_final_s_bool", hint_prefix));
    constraints.push(AirExpression::Sub(
        Box::new(final_s_aux.clone()),
        Box::new(sum_s_bit),
    ));

    (
        final_shifted_val_expr,
        final_g_aux,
        final_r_aux,
        final_s_aux,
    )
}

#[allow(clippy::too_many_arguments)]
pub fn fp_normalize_and_round_significand(
    intermediate_sig: &AirExpression,
    intermediate_sign: &AirExpression,
    intermediate_biased_exp: &AirExpression,
    guard_bit_from_align: &AirExpression,
    round_bit_from_align: &AirExpression,
    sticky_bit_from_align: &AirExpression,
    mant_bit_count: u32,
    _exp_bit_count: u32,
    ctx: &mut AirGenContext,
    constraints: &mut Vec<AirExpression>,
    hint_prefix: &str,
) -> (
    AirExpression,
    AirExpression,
    AirExpression,
    AirExpression, /*is_true_zero_after_norm_round*/
) {
    let int_sig_is_zero = fp_is_value_zero(
        intermediate_sig,
        ctx,
        constraints,
        &format!("{}_int_sig_is_zero", hint_prefix),
    );

    let norm_sig_width = mant_bit_count + 2;
    let intermediate_sig_bits = fp_decompose_unsigned(
        intermediate_sig,
        norm_sig_width,
        ctx,
        constraints,
        &format!("{}_int_sig_decomp", hint_prefix),
    );

    let sig_overflow_bit_pos = mant_bit_count + 1;
    let sig_overflowed_one_bit = if sig_overflow_bit_pos < norm_sig_width {
        intermediate_sig_bits[sig_overflow_bit_pos as usize].clone()
    } else {
        AirExpression::Constant(0)
    };

    let sig_after_norm_rs = ctx.new_aux_variable();
    let sig_after_norm_rs_expr = AirExpression::Trace(sig_after_norm_rs, RowOffset::Current);
    let exp_after_norm_rs = ctx.new_aux_variable();
    let exp_after_norm_rs_expr = AirExpression::Trace(exp_after_norm_rs, RowOffset::Current);

    let g_after_norm_rs = new_boolean_aux(
        ctx,
        constraints,
        &format!("{}_g_after_norm_rs", hint_prefix),
    );
    let r_after_norm_rs = new_boolean_aux(
        ctx,
        constraints,
        &format!("{}_r_after_norm_rs", hint_prefix),
    );
    let s_after_norm_rs = new_boolean_aux(
        ctx,
        constraints,
        &format!("{}_s_after_norm_rs", hint_prefix),
    );

    let mut shifted_sig_bits_if_overflow = Vec::new();
    if norm_sig_width > 0 {
        for i in 1..norm_sig_width {
            shifted_sig_bits_if_overflow.push(intermediate_sig_bits[i as usize].clone());
        }
    }

    while shifted_sig_bits_if_overflow.len() < (mant_bit_count + 1) as usize {
        shifted_sig_bits_if_overflow.insert(0, AirExpression::Constant(0));
    }
    if shifted_sig_bits_if_overflow.len() > (mant_bit_count + 1) as usize {
        shifted_sig_bits_if_overflow.truncate((mant_bit_count + 1) as usize);
    }
    let sig_if_overflow_val = fp_reconstruct_from_bits(
        &shifted_sig_bits_if_overflow,
        ctx,
        constraints,
        &format!("{}_sig_if_ovf_rec", hint_prefix),
    );
    let exp_if_overflow_val = fp_add(
        intermediate_biased_exp,
        &AirExpression::Constant(1),
        ctx,
        constraints,
        &format!("{}_exp_if_ovf", hint_prefix),
    );
    let g_if_overflow_val = if !intermediate_sig_bits.is_empty() {
        intermediate_sig_bits[0].clone()
    } else {
        AirExpression::Constant(0)
    };
    let r_if_overflow_val = guard_bit_from_align.clone();
    let s_if_overflow_val_inter = fp_logical_or(
        round_bit_from_align,
        sticky_bit_from_align,
        ctx,
        constraints,
        &format!("{}_s_inter_if_ovf", hint_prefix),
    );
    let s_if_overflow_val = s_if_overflow_val_inter;

    let mut sig_bits_if_not_overflow = Vec::new();
    for i in 0..=(mant_bit_count) {
        if i < norm_sig_width {
            sig_bits_if_not_overflow.push(intermediate_sig_bits[i as usize].clone());
        } else {
            sig_bits_if_not_overflow.push(AirExpression::Constant(0));
        }
    }
    let sig_if_not_overflow_val = fp_reconstruct_from_bits(
        &sig_bits_if_not_overflow,
        ctx,
        constraints,
        &format!("{}_sig_not_ovf_rec", hint_prefix),
    );
    let exp_if_not_overflow_val = intermediate_biased_exp.clone();
    let g_if_not_overflow_val = guard_bit_from_align.clone();
    let r_if_not_overflow_val = round_bit_from_align.clone();
    let s_if_not_overflow_val = sticky_bit_from_align.clone();

    let selected_sig_norm = fp_select(
        &sig_overflowed_one_bit,
        &sig_if_overflow_val,
        &sig_if_not_overflow_val,
        ctx,
        constraints,
        &format!("{}_sel_sig_norm", hint_prefix),
    );
    constraints.push(AirExpression::Sub(
        Box::new(sig_after_norm_rs_expr.clone()),
        Box::new(selected_sig_norm),
    ));

    let selected_exp_norm = fp_select(
        &sig_overflowed_one_bit,
        &exp_if_overflow_val,
        &exp_if_not_overflow_val,
        ctx,
        constraints,
        &format!("{}_sel_exp_norm", hint_prefix),
    );
    constraints.push(AirExpression::Sub(
        Box::new(exp_after_norm_rs_expr.clone()),
        Box::new(selected_exp_norm),
    ));

    let selected_g_norm = fp_select(
        &sig_overflowed_one_bit,
        &g_if_overflow_val,
        &g_if_not_overflow_val,
        ctx,
        constraints,
        &format!("{}_sel_g_norm", hint_prefix),
    );
    constraints.push(AirExpression::Sub(
        Box::new(g_after_norm_rs.clone()),
        Box::new(selected_g_norm),
    ));

    let selected_r_norm = fp_select(
        &sig_overflowed_one_bit,
        &r_if_overflow_val,
        &r_if_not_overflow_val,
        ctx,
        constraints,
        &format!("{}_sel_r_norm", hint_prefix),
    );
    constraints.push(AirExpression::Sub(
        Box::new(r_after_norm_rs.clone()),
        Box::new(selected_r_norm),
    ));

    let selected_s_norm = fp_select(
        &sig_overflowed_one_bit,
        &s_if_overflow_val,
        &s_if_not_overflow_val,
        ctx,
        constraints,
        &format!("{}_sel_s_norm", hint_prefix),
    );
    constraints.push(AirExpression::Sub(
        Box::new(s_after_norm_rs.clone()),
        Box::new(selected_s_norm),
    ));

    let sig_for_round_bits = fp_decompose_unsigned(
        &sig_after_norm_rs_expr,
        mant_bit_count + 1,
        ctx,
        constraints,
        &format!("{}_sig_for_round_decomp", hint_prefix),
    );
    let lsb_of_sig_for_round = if !sig_for_round_bits.is_empty() {
        sig_for_round_bits[0].clone()
    } else {
        AirExpression::Constant(0)
    };

    let r_or_s = fp_logical_or(
        &r_after_norm_rs,
        &s_after_norm_rs,
        ctx,
        constraints,
        &format!("{}_r_or_s_round", hint_prefix),
    );
    let r_or_s_or_lsb = fp_logical_or(
        &r_or_s,
        &lsb_of_sig_for_round,
        ctx,
        constraints,
        &format!("{}_r_s_lsb_round", hint_prefix),
    );
    let should_increment_sig = fp_logical_and(
        &g_after_norm_rs,
        &r_or_s_or_lsb,
        ctx,
        constraints,
        &format!("{}_should_inc_sig", hint_prefix),
    );

    let sig_after_round_val = fp_add(
        &sig_after_norm_rs_expr,
        &should_increment_sig,
        ctx,
        constraints,
        &format!("{}_sig_plus_inc", hint_prefix),
    );
    let exp_after_round_val = exp_after_norm_rs_expr.clone();

    let sig_after_round_bits = fp_decompose_unsigned(
        &sig_after_round_val,
        mant_bit_count + 2,
        ctx,
        constraints,
        &format!("{}_sig_after_round_decomp", hint_prefix),
    );
    let round_overflow_bit_pos = mant_bit_count + 1;
    let round_caused_sig_overflow = if round_overflow_bit_pos < (mant_bit_count + 2) {
        sig_after_round_bits[round_overflow_bit_pos as usize].clone()
    } else {
        AirExpression::Constant(0)
    };

    let final_mant_if_round_ovf = AirExpression::Constant(1u128 << mant_bit_count);
    let mut final_mant_bits_if_not_round_ovf = Vec::new();
    for i in 0..=mant_bit_count {
        if i < (mant_bit_count + 2) {
            final_mant_bits_if_not_round_ovf.push(sig_after_round_bits[i as usize].clone());
        } else {
            final_mant_bits_if_not_round_ovf.push(AirExpression::Constant(0));
        }
    }
    let final_mant_if_not_round_ovf_val = fp_reconstruct_from_bits(
        &final_mant_bits_if_not_round_ovf,
        ctx,
        constraints,
        &format!("{}_final_mant_not_rovf_rec", hint_prefix),
    );

    let final_normalized_mantissa = fp_select(
        &round_caused_sig_overflow,
        &final_mant_if_round_ovf,
        &final_mant_if_not_round_ovf_val,
        ctx,
        constraints,
        &format!("{}_final_mant_sel", hint_prefix),
    );

    let final_biased_exponent_pre_zero_check = fp_add(
        &exp_after_round_val,
        &round_caused_sig_overflow,
        ctx,
        constraints,
        &format!("{}_exp_plus_round_ovf", hint_prefix),
    );

    let final_sign_output = fp_select(
        &int_sig_is_zero,
        &intermediate_sign,
        &intermediate_sign,
        ctx,
        constraints,
        &format!("{}_final_sign_zero_sel", hint_prefix),
    );
    let final_exponent_output = fp_select(
        &int_sig_is_zero,
        &AirExpression::Constant(0),
        &final_biased_exponent_pre_zero_check,
        ctx,
        constraints,
        &format!("{}_final_exp_zero_sel", hint_prefix),
    );
    let final_mantissa_output_from_sig = fp_select(
        &int_sig_is_zero,
        &AirExpression::Constant(0),
        &final_normalized_mantissa,
        ctx,
        constraints,
        &format!("{}_final_mant_zero_sel", hint_prefix),
    );

    let final_mantissa_output_bits = fp_decompose_unsigned(
        &final_mantissa_output_from_sig,
        mant_bit_count + 1,
        ctx,
        constraints,
        &format!("{}_final_mant_out_decomp", hint_prefix),
    );
    let actual_mantissa_bits_for_result: Vec<AirExpression> = final_mantissa_output_bits
        .iter()
        .take(mant_bit_count as usize)
        .cloned()
        .collect();
    let final_mantissa_to_return = fp_reconstruct_from_bits(
        &actual_mantissa_bits_for_result,
        ctx,
        constraints,
        &format!("{}_final_actual_mant_rec", hint_prefix),
    );

    (
        final_sign_output,
        final_exponent_output,
        final_mantissa_to_return,
        int_sig_is_zero,
    )
}

pub fn setup_sem_aux_vars(
    op: lang::Operand,
    op_name_prefix: &str,
    ctx: &mut AirGenContext,
    _s_b_count: u32,
    e_b_count: u32,
    m_b_count: u32,
    current_air_constraints: &mut Vec<AirExpression>,
) -> (AirTraceVariable, AirTraceVariable, AirTraceVariable) {
    let op_expr = lang_operand_to_air_expression(op);
    println!(
        "    setup_sem_aux_vars ({}) Main Expr: {:?}",
        op_name_prefix, op_expr
    );

    let sign_var = ctx.new_aux_variable();
    let exponent_val_col = ctx.new_aux_variable();
    let mantissa_val_col = ctx.new_aux_variable();

    println!(
        "      {}_sign_col: {:?}, {}_exp_val_col: {:?}, {}_mant_val_col: {:?}",
        op_name_prefix,
        sign_var,
        op_name_prefix,
        exponent_val_col,
        op_name_prefix,
        mantissa_val_col
    );

    let sign_var_expr = AirExpression::Trace(sign_var, RowOffset::Current);
    current_air_constraints.push(AirExpression::Mul(
        Box::new(sign_var_expr.clone()),
        Box::new(AirExpression::Sub(
            Box::new(sign_var_expr.clone()),
            Box::new(AirExpression::Constant(1)),
        )),
    ));

    let exponent_component_bits = ctx.add_unsigned_range_proof_constraints(
        AirExpression::Trace(exponent_val_col, RowOffset::Current),
        e_b_count,
    );
    let mantissa_component_bits = ctx.add_unsigned_range_proof_constraints(
        AirExpression::Trace(mantissa_val_col, RowOffset::Current),
        m_b_count,
    );

    let mut reconstructed_mantissa_from_bits = AirExpression::Constant(0);
    for (i, m_bit_var) in mantissa_component_bits.iter().enumerate() {
        reconstructed_mantissa_from_bits = AirExpression::Add(
            Box::new(reconstructed_mantissa_from_bits),
            Box::new(AirExpression::Mul(
                Box::new(AirExpression::Trace(*m_bit_var, RowOffset::Current)),
                Box::new(AirExpression::Constant(1u128 << i)),
            )),
        );
    }

    let mut reconstructed_exponent_from_bits = AirExpression::Constant(0);
    for (i, e_bit_var) in exponent_component_bits.iter().enumerate() {
        reconstructed_exponent_from_bits = AirExpression::Add(
            Box::new(reconstructed_exponent_from_bits),
            Box::new(AirExpression::Mul(
                Box::new(AirExpression::Trace(*e_bit_var, RowOffset::Current)),
                Box::new(AirExpression::Constant(1u128 << i)),
            )),
        );
    }

    let exponent_term = AirExpression::Mul(
        Box::new(reconstructed_exponent_from_bits),
        Box::new(AirExpression::Constant(1u128 << m_b_count)),
    );

    let sign_term = AirExpression::Mul(
        Box::new(sign_var_expr.clone()),
        Box::new(AirExpression::Constant(1u128 << (e_b_count + m_b_count))),
    );

    let s_plus_e_terms = AirExpression::Add(Box::new(sign_term), Box::new(exponent_term));
    let total_reconstructed_bit_pattern = AirExpression::Add(
        Box::new(s_plus_e_terms),
        Box::new(reconstructed_mantissa_from_bits),
    );

    current_air_constraints.push(AirExpression::Sub(
        Box::new(op_expr.clone()),
        Box::new(total_reconstructed_bit_pattern),
    ));
    println!(
        "      setup_sem_aux_vars ({}) Recomposition constraint added connecting main var to S/E/M bits.",
        op_name_prefix
    );

    (sign_var, exponent_val_col, mantissa_val_col)
}

pub fn fp_power_of_2(
    val_expr: &AirExpression,
    val_bit_width: u32,
    ctx: &mut AirGenContext,
    constraints: &mut Vec<AirExpression>,
    hint_prefix: &str,
) -> AirExpression {
    let val_bits = fp_decompose_unsigned(
        val_expr,
        val_bit_width,
        ctx,
        constraints,
        &format!("{}_val_decomp", hint_prefix),
    );

    let mut cumulative_product = AirExpression::Constant(1);

    let mut c_i = AirExpression::Constant(2);

    for i in 0..val_bit_width {
        let bit_i_expr = &val_bits[i as usize];

        let c_i_minus_1 = fp_sub(
            &c_i,
            &AirExpression::Constant(1),
            ctx,
            constraints,
            &format!("{}_c_i_minus_1_{}", hint_prefix, i),
        );
        let term_i = fp_add(
            &fp_mul(
                bit_i_expr,
                &c_i_minus_1,
                ctx,
                constraints,
                &format!("{}_term_i_mul_{}", hint_prefix, i),
            ),
            &AirExpression::Constant(1),
            ctx,
            constraints,
            &format!("{}_term_i_add_{}", hint_prefix, i),
        );

        cumulative_product = fp_mul(
            &cumulative_product,
            &term_i,
            ctx,
            constraints,
            &format!("{}_prod_step_{}", hint_prefix, i),
        );

        if i < val_bit_width - 1 {
            c_i = fp_mul(
                &c_i,
                &c_i,
                ctx,
                constraints,
                &format!("{}_c_i_sq_{}", hint_prefix, i),
            );
        }
    }

    cumulative_product
}

#[allow(clippy::too_many_arguments)]
pub fn fp_variable_division(
    dividend_expr: &AirExpression,
    shift_amount_expr: &AirExpression,
    dividend_bit_width: u32,
    shift_amount_bit_width: u32,
    ctx: &mut AirGenContext,
    constraints: &mut Vec<AirExpression>,
    hint_prefix: &str,
) -> (AirExpression, AirExpression) {
    let quotient_aux = ctx.new_aux_variable();
    let quotient_expr = AirExpression::Trace(quotient_aux, RowOffset::Current);
    ctx.add_unsigned_range_proof_constraints(quotient_expr.clone(), dividend_bit_width);

    let remainder_aux = ctx.new_aux_variable();
    let remainder_expr = AirExpression::Trace(remainder_aux, RowOffset::Current);
    ctx.add_unsigned_range_proof_constraints(remainder_expr.clone(), dividend_bit_width);

    let divisor_expr = fp_power_of_2(
        shift_amount_expr,
        shift_amount_bit_width,
        ctx,
        constraints,
        &format!("{}_divisor_pow2", hint_prefix),
    );

    let quot_times_div = fp_mul(
        &quotient_expr,
        &divisor_expr,
        ctx,
        constraints,
        &format!("{}_q_x_d", hint_prefix),
    );
    let qd_plus_r = fp_add(
        &quot_times_div,
        &remainder_expr,
        ctx,
        constraints,
        &format!("{}_qd_plus_r", hint_prefix),
    );
    constraints.push(AirExpression::Sub(
        Box::new(dividend_expr.clone()),
        Box::new(qd_plus_r),
    ));

    let rem_lt_divisor = fp_icmp_ult(
        &remainder_expr,
        &divisor_expr,
        dividend_bit_width + 1,
        ctx,
        constraints,
        &format!("{}_rem_lt_div", hint_prefix),
    );

    constraints.push(AirExpression::Sub(
        Box::new(rem_lt_divisor),
        Box::new(AirExpression::Constant(1)),
    ));

    (quotient_expr, remainder_expr)
}

pub fn fp_find_msb(
    value_expr: &AirExpression,
    bitwidth: u32,
    ctx: &mut AirGenContext,
    constraints: &mut Vec<AirExpression>,
    hint_prefix: &str,
) -> (AirExpression, AirExpression) {
    if bitwidth == 0 {
        return (AirExpression::Constant(0), AirExpression::Constant(0));
    }

    let value_bits = fp_decompose_unsigned(
        value_expr,
        bitwidth,
        ctx,
        constraints,
        &format!("{}_val_decomp", hint_prefix),
    );

    let mut h_bits = vec![AirExpression::Constant(0); bitwidth as usize];
    if bitwidth > 1 {
        for i in (0..(bitwidth - 1)).rev() {
            let i_usize = i as usize;
            h_bits[i_usize] = fp_logical_or(
                &h_bits[i_usize + 1],
                &value_bits[i_usize + 1],
                ctx,
                constraints,
                &format!("{}_h_bit_{}", hint_prefix, i),
            );
        }
    }

    let mut p_bits = Vec::new();
    for i in 0..bitwidth {
        let i_usize = i as usize;
        let not_h_i = fp_logical_not(
            &h_bits[i_usize],
            ctx,
            constraints,
            &format!("{}_not_h_bit_{}", hint_prefix, i),
        );
        let p_i = fp_logical_and(
            &value_bits[i_usize],
            &not_h_i,
            ctx,
            constraints,
            &format!("{}_p_bit_{}", hint_prefix, i),
        );
        p_bits.push(p_i);
    }

    let mut sum_of_p_bits = AirExpression::Constant(0);
    if bitwidth > 0 {
        sum_of_p_bits = p_bits[0].clone();
        if bitwidth > 1 {
            for i in 1..bitwidth as usize {
                sum_of_p_bits = fp_add(
                    &sum_of_p_bits,
                    &p_bits[i],
                    ctx,
                    constraints,
                    &format!("{}_sum_p_bits_{}", hint_prefix, i),
                );
            }
        }
    }
    constraints.push(AirExpression::Sub(
        Box::new(sum_of_p_bits),
        Box::new(AirExpression::Constant(1)),
    ));

    let mut msb_pos_expr = AirExpression::Constant(0);

    if bitwidth > 1 {
        for i in 1..bitwidth as usize {
            let weight = AirExpression::Constant(i as u128);
            let term = fp_mul(
                &p_bits[i],
                &weight,
                ctx,
                constraints,
                &format!("{}_pos_term_{}", hint_prefix, i),
            );
            msb_pos_expr = fp_add(
                &msb_pos_expr,
                &term,
                ctx,
                constraints,
                &format!("{}_pos_sum_{}", hint_prefix, i),
            );
        }
    }

    let msb_value_expr = fp_reconstruct_from_bits(
        &p_bits,
        ctx,
        constraints,
        &format!("{}_msb_val_recon", hint_prefix),
    );

    let value_without_msb_expr = fp_sub(
        value_expr,
        &msb_value_expr,
        ctx,
        constraints,
        &format!("{}_val_minus_msb", hint_prefix),
    );

    (msb_pos_expr, value_without_msb_expr)
}

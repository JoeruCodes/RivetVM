use lang::Operand;

use crate::llvm::air::types::RowOffset;

use super::{
    codegen::ctx::AirGenContext,
    types::{AirExpression, AirTraceVariable},
};

pub fn generate_signed_range_proof_constraints(
    x_signed_expr: &AirExpression,
    bitwidth: u32,
    air_gen_ctx: &mut AirGenContext,
    air_constraints: &mut Vec<AirExpression>,
    var_name: &str,
) -> (Vec<AirExpression>, Option<AirExpression>) {
    if bitwidth == 0 {
        println!(
            "    SDIV Range Proof for {}: bitwidth is 0, skipping.",
            var_name
        );
        return (Vec::new(), None);
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
        let bit_aux_var = air_gen_ctx.new_aux_variable();
        let bit_expr = AirExpression::Trace(bit_aux_var, RowOffset::Current);

        let bit_minus_one = AirExpression::Sub(
            Box::new(bit_expr.clone()),
            Box::new(AirExpression::Constant(1)),
        );
        air_constraints.push(AirExpression::Mul(
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

    air_constraints.push(AirExpression::Sub(
        Box::new(x_unsigned_expr),
        Box::new(sum_from_bits),
    ));
    println!(
        "      {}_unsigned decomposition constraint added for {}.
",
        var_name, var_name
    );

    let msb_expr_opt = bit_vars_exprs.last().cloned();
    (bit_vars_exprs, msb_expr_opt)
}

pub fn lang_operand_to_air_expression(lang_op: Operand) -> AirExpression {
    match lang_op {
        Operand::Var(v) => AirExpression::Trace(AirTraceVariable(v.0), RowOffset::Current),
        Operand::Const(c) => AirExpression::Constant(c),
    }
}

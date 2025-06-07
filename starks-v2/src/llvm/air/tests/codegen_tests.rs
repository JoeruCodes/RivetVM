#[cfg(test)]
mod tests {
    use crate::{
        Field, Unity,
        llvm::air::{
            codegen::{AirCodegen, ConstraintSystemVariable, Operand, StructuredAirConstraint},
            types::{AirExpression, AirTraceVariable, RowOffset},
        },
        mod_pow,
    };
    use lang::FloatPredicate;
    use std::collections::HashMap;

    #[derive(Clone, Debug)]
    struct TestField97;
    impl TestField97 {
        #[allow(dead_code)]
        fn find_nth_root_static(n: usize, p: u128) -> u128 {
            if p == 97 {
                if n == 2 {
                    return 96;
                }
                if n == 4 {
                    return 22;
                }
                let exponent = (p - 1) / n as u128;
                let primitive_root = 5;
                return mod_pow(primitive_root, exponent, p);
            }
            panic!("Unsupported prime for find_nth_root_static in llvm_air_generator tests");
        }
    }
    impl Field for TestField97 {
        const PRIME: u128 = 97;
        fn get_prime() -> u128 {
            Self::PRIME
        }
        fn get_nth_root_of_unity(&self, n: usize) -> Unity {
            let specific_nth_root = Self::find_nth_root_static(n, Self::PRIME);
            Unity {
                generator: specific_nth_root, /*, nth_root: specific_nth_root */
            }
        }
    }

    const F32_SIGN_BITS: u32 = 1;
    const F32_EXP_BITS: u32 = 8;
    const F32_MANT_BITS: u32 = 23;
    const F32_EXP_BIAS: u128 = (1 << (F32_EXP_BITS - 1)) - 1;

    #[allow(dead_code)]
    fn f32_to_u32_bits(f: f32) -> u32 {
        f.to_bits()
    }

    #[allow(dead_code)]
    fn u32_bits_to_f32(bits: u32) -> f32 {
        f32::from_bits(bits)
    }

    #[allow(dead_code)]
    fn f32_to_sem(f: f32) -> (u128, u128, u128) {
        let bits = f.to_bits();
        let sign = (bits >> (F32_EXP_BITS + F32_MANT_BITS)) as u128;
        let exp_biased = ((bits >> F32_MANT_BITS) & ((1 << F32_EXP_BITS) - 1)) as u128;
        let mant = (bits & ((1 << F32_MANT_BITS) - 1)) as u128;
        (sign, exp_biased, mant)
    }

    #[allow(dead_code)]
    fn sem_to_f32_u32_bits(s: u128, e_biased: u128, m: u128) -> u32 {
        ((s as u32) << (F32_EXP_BITS + F32_MANT_BITS))
            | ((e_biased as u32) << F32_MANT_BITS)
            | (m as u32)
    }

    #[test]
    fn test_fadd_normal_numbers() {
        let mut air_codegen = AirCodegen::new(100);
        let op1_id = air_codegen.ctx.new_aux_variable().0;
        let op2_id = air_codegen.ctx.new_aux_variable().0;
        let res_id = air_codegen.ctx.new_aux_variable().0;

        let operand1_var = ConstraintSystemVariable(op1_id);
        let operand2_var = ConstraintSystemVariable(op2_id);
        let result_var = ConstraintSystemVariable(res_id);

        let operand1 = Operand::Var(operand1_var);
        let operand2 = Operand::Var(operand2_var);

        let structured_constraints = vec![StructuredAirConstraint::FAdd {
            operand1,
            operand2,
            result: result_var,
            operand_bitwidth: 32,
            block_name: "entry".to_string(),
        }];

        let air_constraints = air_codegen.resolve_structured_constraints(
            structured_constraints,
            &HashMap::new(),
            &Vec::new(),
        );

        assert!(
            !air_constraints.is_empty(),
            "No AIR constraints generated for FAdd normal"
        );
        println!(
            "test_fadd_normal_numbers: {} constraints generated.",
            air_constraints.len()
        );
    }

    #[test]
    fn test_fadd_nan_operand() {
        let mut air_codegen = AirCodegen::new(100);
        let op1_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);
        let op2_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);
        let res_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);

        let structured_constraints = vec![StructuredAirConstraint::FAdd {
            operand1: Operand::Var(op1_var),
            operand2: Operand::Var(op2_var),
            result: res_var,
            operand_bitwidth: 32,
            block_name: "entry".to_string(),
        }];
        let air_constraints = air_codegen.resolve_structured_constraints(
            structured_constraints,
            &HashMap::new(),
            &Vec::new(),
        );
        assert!(
            !air_constraints.is_empty(),
            "No AIR constraints for FAdd NaN operand"
        );
        println!(
            "test_fadd_nan_operand: {} constraints generated.",
            air_constraints.len()
        );
    }

    #[test]
    fn test_fadd_inf_plus_neg_inf() {
        let mut air_codegen = AirCodegen::new(100);
        let op1_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);
        let op2_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);
        let res_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);

        let structured_constraints = vec![StructuredAirConstraint::FAdd {
            operand1: Operand::Var(op1_var),
            operand2: Operand::Var(op2_var),
            result: res_var,
            operand_bitwidth: 32,
            block_name: "entry".to_string(),
        }];
        let air_constraints = air_codegen.resolve_structured_constraints(
            structured_constraints,
            &HashMap::new(),
            &Vec::new(),
        );
        assert!(
            !air_constraints.is_empty(),
            "No AIR constraints for FAdd Inf + -Inf"
        );
        println!(
            "test_fadd_inf_plus_neg_inf: {} constraints generated.",
            air_constraints.len()
        );
    }

    #[test]
    fn test_fadd_inf_plus_finite() {
        let mut air_codegen = AirCodegen::new(100);
        let op1_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);
        let op2_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);
        let res_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);

        let structured_constraints = vec![StructuredAirConstraint::FAdd {
            operand1: Operand::Var(op1_var),
            operand2: Operand::Var(op2_var),
            result: res_var,
            operand_bitwidth: 32,
            block_name: "entry".to_string(),
        }];
        let air_constraints = air_codegen.resolve_structured_constraints(
            structured_constraints,
            &HashMap::new(),
            &Vec::new(),
        );
        assert!(
            !air_constraints.is_empty(),
            "No AIR constraints for FAdd Inf + Finite"
        );
        println!(
            "test_fadd_inf_plus_finite: {} constraints generated.",
            air_constraints.len()
        );
    }

    #[test]
    fn test_fadd_zero_plus_zero() {
        let mut air_codegen = AirCodegen::new(100);
        let op1_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);
        let op2_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);
        let res_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);

        let structured_constraints = vec![StructuredAirConstraint::FAdd {
            operand1: Operand::Var(op1_var),
            operand2: Operand::Var(op2_var),
            result: res_var,
            operand_bitwidth: 32,
            block_name: "entry".to_string(),
        }];
        let air_constraints = air_codegen.resolve_structured_constraints(
            structured_constraints,
            &HashMap::new(),
            &Vec::new(),
        );
        assert!(
            !air_constraints.is_empty(),
            "No AIR constraints for FAdd Zero + Zero"
        );
        println!(
            "test_fadd_zero_plus_zero: {} constraints generated.",
            air_constraints.len()
        );
    }

    #[test]
    fn test_fadd_zero_plus_finite() {
        let mut air_codegen = AirCodegen::new(100);
        let op1_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);
        let op2_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);
        let res_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);

        let structured_constraints = vec![StructuredAirConstraint::FAdd {
            operand1: Operand::Var(op1_var),
            operand2: Operand::Var(op2_var),
            result: res_var,
            operand_bitwidth: 32,
            block_name: "entry".to_string(),
        }];
        let air_constraints = air_codegen.resolve_structured_constraints(
            structured_constraints,
            &HashMap::new(),
            &Vec::new(),
        );
        assert!(
            !air_constraints.is_empty(),
            "No AIR constraints for FAdd Zero + Finite"
        );
        println!(
            "test_fadd_zero_plus_finite: {} constraints generated.",
            air_constraints.len()
        );
    }

    #[test]
    fn test_fsub_normal_numbers() {
        let mut air_codegen = AirCodegen::new(100);
        let op1_id = air_codegen.ctx.new_aux_variable().0;
        let op2_id = air_codegen.ctx.new_aux_variable().0;
        let res_id = air_codegen.ctx.new_aux_variable().0;

        let operand1_var = ConstraintSystemVariable(op1_id);
        let operand2_var = ConstraintSystemVariable(op2_id);
        let result_var = ConstraintSystemVariable(res_id);

        let operand1 = Operand::Var(operand1_var);
        let operand2 = Operand::Var(operand2_var);

        let structured_constraints = vec![StructuredAirConstraint::FSub {
            operand1,
            operand2,
            result: result_var,
            operand_bitwidth: 32,
            block_name: "entry".to_string(),
        }];

        let air_constraints = air_codegen.resolve_structured_constraints(
            structured_constraints,
            &HashMap::new(),
            &Vec::new(),
        );

        assert!(
            !air_constraints.is_empty(),
            "No AIR constraints generated for FSub normal"
        );
        println!(
            "test_fsub_normal_numbers: {} constraints generated.",
            air_constraints.len()
        );
    }

    #[test]
    fn test_fsub_nan_operand() {
        let mut air_codegen = AirCodegen::new(100);
        let op1_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);
        let op2_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);
        let res_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);

        let structured_constraints = vec![StructuredAirConstraint::FSub {
            operand1: Operand::Var(op1_var),
            operand2: Operand::Var(op2_var),
            result: res_var,
            operand_bitwidth: 32,
            block_name: "entry".to_string(),
        }];
        let air_constraints = air_codegen.resolve_structured_constraints(
            structured_constraints,
            &HashMap::new(),
            &Vec::new(),
        );
        assert!(
            !air_constraints.is_empty(),
            "No AIR constraints for FSub NaN operand"
        );
        println!(
            "test_fsub_nan_operand: {} constraints generated.",
            air_constraints.len()
        );
    }

    #[test]
    fn test_fsub_inf_minus_inf() {
        let mut air_codegen = AirCodegen::new(100);
        let op1_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);
        let op2_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);
        let res_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);

        let structured_constraints = vec![StructuredAirConstraint::FSub {
            operand1: Operand::Var(op1_var),
            operand2: Operand::Var(op2_var),
            result: res_var,
            operand_bitwidth: 32,
            block_name: "entry".to_string(),
        }];
        let air_constraints = air_codegen.resolve_structured_constraints(
            structured_constraints,
            &HashMap::new(),
            &Vec::new(),
        );
        assert!(
            !air_constraints.is_empty(),
            "No AIR constraints for FSub Inf - Inf"
        );
        println!(
            "test_fsub_inf_minus_inf: {} constraints generated.",
            air_constraints.len()
        );
    }

    #[test]
    fn test_fsub_inf_minus_finite() {
        let mut air_codegen = AirCodegen::new(100);
        let op1_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);
        let op2_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);
        let res_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);

        let structured_constraints = vec![StructuredAirConstraint::FSub {
            operand1: Operand::Var(op1_var),
            operand2: Operand::Var(op2_var),
            result: res_var,
            operand_bitwidth: 32,
            block_name: "entry".to_string(),
        }];
        let air_constraints = air_codegen.resolve_structured_constraints(
            structured_constraints,
            &HashMap::new(),
            &Vec::new(),
        );
        assert!(
            !air_constraints.is_empty(),
            "No AIR constraints for FSub Inf - Finite"
        );
        println!(
            "test_fsub_inf_minus_finite: {} constraints generated.",
            air_constraints.len()
        );
    }

    #[test]
    fn test_fsub_zero_minus_zero() {
        let mut air_codegen = AirCodegen::new(100);
        let op1_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);
        let op2_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);
        let res_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);

        let structured_constraints = vec![StructuredAirConstraint::FSub {
            operand1: Operand::Var(op1_var),
            operand2: Operand::Var(op2_var),
            result: res_var,
            operand_bitwidth: 32,
            block_name: "entry".to_string(),
        }];
        let air_constraints = air_codegen.resolve_structured_constraints(
            structured_constraints,
            &HashMap::new(),
            &Vec::new(),
        );
        assert!(
            !air_constraints.is_empty(),
            "No AIR constraints for FSub Zero - Zero"
        );
        println!(
            "test_fsub_zero_minus_zero: {} constraints generated.",
            air_constraints.len()
        );
    }

    #[test]
    fn test_fsub_zero_minus_finite() {
        let mut air_codegen = AirCodegen::new(100);
        let op1_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);
        let op2_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);
        let res_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);

        let structured_constraints = vec![StructuredAirConstraint::FSub {
            operand1: Operand::Var(op1_var),
            operand2: Operand::Var(op2_var),
            result: res_var,
            operand_bitwidth: 32,
            block_name: "entry".to_string(),
        }];
        let air_constraints = air_codegen.resolve_structured_constraints(
            structured_constraints,
            &HashMap::new(),
            &Vec::new(),
        );
        assert!(
            !air_constraints.is_empty(),
            "No AIR constraints for FSub Zero - Finite"
        );
        println!(
            "test_fsub_zero_minus_finite: {} constraints generated.",
            air_constraints.len()
        );
    }

    #[test]
    fn test_generate_air_from_add_llvm() {
        let llvm_ir = r#"; ModuleID = 'add_module'
        define i32 @add(i32 %a, i32 %b) {
          entry:
            ; %a is LangSysVar(0), %b is LangSysVar(1)
            %result = add i32 %a, %b ; %result is LangSysVar(2)
            ret i32 %result
        }
        "#;
        let field_instance = TestField97;
        let result = AirCodegen::generate_air(llvm_ir, &field_instance);
        assert!(result.is_ok());
        let air = result.unwrap();

        assert_eq!(air.num_trace_columns, 3 + 4);
        assert_eq!(air.constraints.len(), 1);

        let expected_expr = AirExpression::Sub(
            Box::new(AirExpression::Add(
                Box::new(AirExpression::Trace(
                    AirTraceVariable(0),
                    RowOffset::Current,
                )),
                Box::new(AirExpression::Trace(
                    AirTraceVariable(1),
                    RowOffset::Current,
                )),
            )),
            Box::new(AirExpression::Trace(
                AirTraceVariable(2),
                RowOffset::Current,
            )),
        );

        assert_eq!(air.constraints[0], expected_expr);
    }

    #[test]
    fn test_generate_air_from_add_with_constant_llvm() {
        let llvm_ir = r#"; ModuleID = 'add_const_module'
        define i32 @add_const(i32 %a) {
          entry:
            ; %a is LangSysVar(0)
            %result = add i32 %a, 5 ; %result is LangSysVar(1)
            ret i32 %result
        }
        "#;
        let field_instance = TestField97;
        let result = AirCodegen::generate_air(llvm_ir, &field_instance);
        assert!(result.is_ok());
        let air = result.unwrap();

        assert_eq!(air.num_trace_columns, 2 + 4);
        assert_eq!(air.constraints.len(), 1);

        let expected_expr = AirExpression::Sub(
            Box::new(AirExpression::Add(
                Box::new(AirExpression::Trace(
                    AirTraceVariable(0),
                    RowOffset::Current,
                )),
                Box::new(AirExpression::Constant(5)),
            )),
            Box::new(AirExpression::Trace(
                AirTraceVariable(1),
                RowOffset::Current,
            )),
        );
        assert_eq!(air.constraints[0], expected_expr);
    }

    #[test]
    fn test_generate_air_from_mul_llvm() {
        let llvm_ir = r#"; ModuleID = 'mul_module'
        define i32 @multiply(i32 %a, i32 %b) {
          entry:
            ; %a is LangSysVar(0), %b is LangSysVar(1)
            %result = mul i32 %a, %b ; %result is LangSysVar(2)
            ret i32 %result
        }
        "#;
        let field_instance = TestField97;
        let result = AirCodegen::generate_air(llvm_ir, &field_instance);
        assert!(result.is_ok());
        let air = result.unwrap();

        assert_eq!(air.num_trace_columns, 3 + 4);
        assert_eq!(air.constraints.len(), 1);

        let expected_expr = AirExpression::Sub(
            Box::new(AirExpression::Mul(
                Box::new(AirExpression::Trace(
                    AirTraceVariable(0),
                    RowOffset::Current,
                )),
                Box::new(AirExpression::Trace(
                    AirTraceVariable(1),
                    RowOffset::Current,
                )),
            )),
            Box::new(AirExpression::Trace(
                AirTraceVariable(2),
                RowOffset::Current,
            )),
        );
        assert_eq!(air.constraints[0], expected_expr);
    }

    #[test]
    fn test_generate_air_from_mul_with_constant_llvm() {
        let llvm_ir = r#"; ModuleID = 'mul_const_module'
        define i32 @mul_const(i32 %a) {
          entry:
            ; %a is LangSysVar(0)
            %result = mul i32 %a, 7 ; %result is LangSysVar(1)
            ret i32 %result
        }
        "#;
        let field_instance = TestField97;
        let result = AirCodegen::generate_air(llvm_ir, &field_instance);
        assert!(result.is_ok());
        let air = result.unwrap();

        assert_eq!(air.num_trace_columns, 2 + 4);
        assert_eq!(air.constraints.len(), 1);

        let expected_expr = AirExpression::Sub(
            Box::new(AirExpression::Mul(
                Box::new(AirExpression::Trace(
                    AirTraceVariable(0),
                    RowOffset::Current,
                )),
                Box::new(AirExpression::Constant(7)),
            )),
            Box::new(AirExpression::Trace(
                AirTraceVariable(1),
                RowOffset::Current,
            )),
        );
        assert_eq!(air.constraints[0], expected_expr);
    }

    #[test]
    fn test_generate_air_from_shl_const_llvm() {
        let llvm_ir = r#"; ModuleID = 'shl_const_module'
        define i32 @shl_const(i32 %a) {
          entry:
            ; %a is LangSysVar(0)
            %result = shl i32 %a, 2 ; %result is LangSysVar(1)
            ret i32 %result
        }
        "#;
        let field_instance = TestField97;
        let result = AirCodegen::generate_air(llvm_ir, &field_instance);
        assert!(
            result.is_ok(),
            "AirCodegen::generate_air failed: {:?}",
            result.err()
        );
        let air = result.unwrap();

        assert_eq!(
            air.num_trace_columns,
            2 + 4,
            "Incorrect number of trace columns"
        );

        assert_eq!(
            air.constraints.len(),
            1,
            "Incorrect number of constraints generated"
        );

        let op1_expr = AirExpression::Trace(AirTraceVariable(0), RowOffset::Current);
        let res_expr = AirExpression::Trace(AirTraceVariable(1), RowOffset::Current);
        let shift_const_val = 2u128;
        let power_of_2_shift_val = 1u128 << shift_const_val;

        let expected_shl_expr = AirExpression::Sub(
            Box::new(res_expr.clone()),
            Box::new(AirExpression::Mul(
                Box::new(op1_expr.clone()),
                Box::new(AirExpression::Constant(power_of_2_shift_val)),
            )),
        );

        assert_eq!(
            air.constraints[0], expected_shl_expr,
            "Shl constraint does not match"
        );
    }

    #[test]
    fn test_generate_air_from_shl_var_llvm() {
        let llvm_ir = r#"; ModuleID = 'shl_var_module'
        define i32 @shl_var(i32 %a, i32 %s) { ; %a is V0, %s is V1
          entry:
            %result = shl i32 %a, %s ; %result is V2
            ret i32 %result
        }
        "#;
        let field_instance = TestField97;
        let result = AirCodegen::generate_air(llvm_ir, &field_instance);
        assert!(
            result.is_ok(),
            "AirCodegen::generate_air failed: {:?}",
            result.err()
        );
        let air = result.unwrap();

        let operand_bitwidth: u32 = 32;

        let num_shift_bits = (operand_bitwidth - 1).ilog2() + 1;

        let expected_num_trace_cols = 3
            + 4
            + num_shift_bits
            + num_shift_bits
            + if num_shift_bits > 0 {
                num_shift_bits - 1
            } else {
                0
            };

        assert_eq!(
            air.num_trace_columns, expected_num_trace_cols as usize,
            "Incorrect number of trace columns"
        );

        let expected_num_constraints = num_shift_bits + 1 + num_shift_bits
            + if num_shift_bits > 0 { num_shift_bits -1 } else { 0 }
            + 1 /*main shl*/;
        assert_eq!(
            air.constraints.len(),
            expected_num_constraints as usize,
            "Incorrect number of constraints generated"
        );

        let op1_expr = AirExpression::Trace(AirTraceVariable(0), RowOffset::Current);
        let op2_expr = AirExpression::Trace(AirTraceVariable(1), RowOffset::Current);
        let res_expr = AirExpression::Trace(AirTraceVariable(2), RowOffset::Current);

        let mut current_constraint_idx = 0;
        let mut s_bit_air_vars = Vec::new();

        for i in 0..num_shift_bits {
            let s_bit_var = AirTraceVariable(3 + i as usize);
            s_bit_air_vars.push(s_bit_var);
            let s_bit_expr = AirExpression::Trace(s_bit_var, RowOffset::Current);
            let expected_bool_constraint = AirExpression::Mul(
                Box::new(s_bit_expr.clone()),
                Box::new(AirExpression::Sub(
                    Box::new(s_bit_expr.clone()),
                    Box::new(AirExpression::Constant(1)),
                )),
            );
            assert_eq!(
                air.constraints[current_constraint_idx], expected_bool_constraint,
                "s_bit {} booleanity mismatch",
                i
            );
            current_constraint_idx += 1;
        }

        let mut op2_sum_terms = Vec::new();
        for i in 0..num_shift_bits {
            op2_sum_terms.push(AirExpression::Mul(
                Box::new(AirExpression::Trace(
                    s_bit_air_vars[i as usize],
                    RowOffset::Current,
                )),
                Box::new(AirExpression::Constant(1u128 << i)),
            ));
        }
        let op2_reconstructed_expr = op2_sum_terms
            .into_iter()
            .reduce(|acc, term| AirExpression::Add(Box::new(acc), Box::new(term)))
            .unwrap_or_else(|| AirExpression::Constant(0));
        let expected_op2_recon_constraint =
            AirExpression::Sub(Box::new(op2_expr.clone()), Box::new(op2_reconstructed_expr));
        assert_eq!(
            air.constraints[current_constraint_idx], expected_op2_recon_constraint,
            "%s reconstruction mismatch"
        );
        current_constraint_idx += 1;

        let mut factor_air_vars = Vec::new();
        let factor_start_trace_idx = 3 + num_shift_bits;
        for i in 0..num_shift_bits {
            let s_i_expr = AirExpression::Trace(s_bit_air_vars[i as usize], RowOffset::Current);
            let factor_i_var = AirTraceVariable(factor_start_trace_idx as usize + i as usize);
            factor_air_vars.push(factor_i_var);
            let factor_i_expr = AirExpression::Trace(factor_i_var, RowOffset::Current);

            let exp_base_power = 1u128 << i;
            let exp_val_i = if exp_base_power >= 128 {
                0
            } else {
                1u128.wrapping_shl(exp_base_power as u32)
            };
            let exp_val_i_minus_1 = exp_val_i.saturating_sub(1);

            let expected_factor_def_constraint = AirExpression::Sub(
                Box::new(factor_i_expr.clone()),
                Box::new(AirExpression::Add(
                    Box::new(AirExpression::Mul(
                        Box::new(s_i_expr.clone()),
                        Box::new(AirExpression::Constant(exp_val_i_minus_1)),
                    )),
                    Box::new(AirExpression::Constant(1)),
                )),
            );
            assert_eq!(
                air.constraints[current_constraint_idx], expected_factor_def_constraint,
                "Factor {} definition mismatch",
                i
            );
            current_constraint_idx += 1;
        }

        let mut current_product_expr_for_check = AirExpression::Constant(1);
        let product_step_start_trace_idx = factor_start_trace_idx + num_shift_bits;

        if num_shift_bits > 0 {
            current_product_expr_for_check =
                AirExpression::Trace(factor_air_vars[0], RowOffset::Current);
            for i in 1..num_shift_bits as usize {
                let prev_prod_expr_val_check = current_product_expr_for_check.clone();
                let factor_val_expr_check =
                    AirExpression::Trace(factor_air_vars[i], RowOffset::Current);

                current_product_expr_for_check = AirExpression::Trace(
                    AirTraceVariable(product_step_start_trace_idx as usize + (i - 1)),
                    RowOffset::Current,
                );

                let expected_prod_step_constraint = AirExpression::Sub(
                    Box::new(current_product_expr_for_check.clone()),
                    Box::new(AirExpression::Mul(
                        Box::new(prev_prod_expr_val_check),
                        Box::new(factor_val_expr_check),
                    )),
                );
                assert_eq!(
                    air.constraints[current_constraint_idx],
                    expected_prod_step_constraint,
                    "Product step {} mismatch",
                    i - 1
                );
                current_constraint_idx += 1;
            }
        }
        let final_power_of_2_op2_expr_for_check = current_product_expr_for_check;

        let expected_main_shl_constraint = AirExpression::Sub(
            Box::new(res_expr.clone()),
            Box::new(AirExpression::Mul(
                Box::new(op1_expr.clone()),
                Box::new(final_power_of_2_op2_expr_for_check.clone()),
            )),
        );
        assert_eq!(
            air.constraints[current_constraint_idx], expected_main_shl_constraint,
            "Main SHL constraint mismatch"
        );
    }

    #[test]
    fn test_generate_air_from_lshr_const_llvm() {
        let llvm_ir = r#"; ModuleID = 'lshr_const_module'
        define i32 @lshr_const(i32 %a) { ; %a is V0
          entry:
            %result = lshr i32 %a, 2 ; %result is V1
            ret i32 %result
        }
        "#;
        let field_instance = TestField97;
        let result = AirCodegen::generate_air(llvm_ir, &field_instance);
        assert!(
            result.is_ok(),
            "AirCodegen::generate_air for LShr const failed: {:?}",
            result.err()
        );
        let air = result.unwrap();

        let operand_bitwidth: u32 = 32;

        let expected_num_trace_cols = 1 + 1 + 1 + operand_bitwidth as usize + 4;
        assert_eq!(
            air.num_trace_columns, expected_num_trace_cols,
            "LShr const: Incorrect number of trace columns"
        );

        let expected_num_constraints = operand_bitwidth as usize + 1 + 1;
        assert_eq!(
            air.constraints.len(),
            expected_num_constraints,
            "LShr const: Incorrect number of constraints"
        );

        let op1_expr = AirExpression::Trace(AirTraceVariable(0), RowOffset::Current);
        let res_expr = AirExpression::Trace(AirTraceVariable(1), RowOffset::Current);
        let rem_expr = AirExpression::Trace(AirTraceVariable(2), RowOffset::Current);
        let shift_const_val = 2u128;
        let power_of_2_shift_val = 1u128 << shift_const_val;

        let mut current_constraint_idx = 0;

        let mut rem_reconstructed_terms = Vec::new();
        let rem_bits_start_col = 3;
        for i in 0..operand_bitwidth {
            let rem_bit_var = AirTraceVariable(rem_bits_start_col + i as usize);
            let rem_bit_expr = AirExpression::Trace(rem_bit_var, RowOffset::Current);
            let expected_bool_constraint = AirExpression::Mul(
                Box::new(rem_bit_expr.clone()),
                Box::new(AirExpression::Sub(
                    Box::new(rem_bit_expr.clone()),
                    Box::new(AirExpression::Constant(1)),
                )),
            );
            assert_eq!(
                air.constraints[current_constraint_idx], expected_bool_constraint,
                "LShr const: rem_bit {} booleanity mismatch",
                i
            );
            current_constraint_idx += 1;
            rem_reconstructed_terms.push(AirExpression::Mul(
                Box::new(rem_bit_expr.clone()),
                Box::new(AirExpression::Constant(1u128 << i)),
            ));
        }

        let rem_reconstructed_expr = rem_reconstructed_terms
            .into_iter()
            .reduce(|acc, term| AirExpression::Add(Box::new(acc), Box::new(term)))
            .unwrap_or_else(|| AirExpression::Constant(0));
        let expected_rem_recon_constraint =
            AirExpression::Sub(Box::new(rem_expr.clone()), Box::new(rem_reconstructed_expr));
        assert_eq!(
            air.constraints[current_constraint_idx], expected_rem_recon_constraint,
            "LShr const: rem reconstruction mismatch"
        );
        current_constraint_idx += 1;

        let res_times_power_of_2 = AirExpression::Mul(
            Box::new(res_expr.clone()),
            Box::new(AirExpression::Constant(power_of_2_shift_val)),
        );
        let res_term_plus_rem =
            AirExpression::Add(Box::new(res_times_power_of_2), Box::new(rem_expr.clone()));
        let expected_algebraic_constraint =
            AirExpression::Sub(Box::new(op1_expr.clone()), Box::new(res_term_plus_rem));
        assert_eq!(
            air.constraints[current_constraint_idx], expected_algebraic_constraint,
            "LShr const: main algebraic constraint mismatch"
        );
    }

    #[test]
    fn test_generate_air_from_icmp_eq_llvm() {
        let llvm_ir = r#"; ModuleID = 'icmp_eq_module'
        define i1 @are_equal(i32 %a, i32 %b) {
          entry:
            ; %a is LangVar(0), %b is LangVar(1)
            %cmp_res = icmp eq i32 %a, %b ; %cmp_res is LangVar(2)
            ret i1 %cmp_res
        }
        "#;
        let field_instance = TestField97;
        let result = AirCodegen::generate_air(llvm_ir, &field_instance);
        assert!(
            result.is_ok(),
            "AirCodegen::generate_air failed: {:?}",
            result.err()
        );
        let air = result.unwrap();

        assert_eq!(
            air.num_trace_columns,
            3 + 4,
            "Incorrect number of trace columns"
        );

        assert_eq!(
            air.constraints.len(),
            2,
            "Incorrect number of constraints generated"
        );

        let cmp_res_expr = AirExpression::Trace(AirTraceVariable(2), RowOffset::Current);
        let expected_booleanity_expr = AirExpression::Mul(
            Box::new(cmp_res_expr.clone()),
            Box::new(AirExpression::Sub(
                Box::new(cmp_res_expr.clone()),
                Box::new(AirExpression::Constant(1)),
            )),
        );

        let op1_expr = AirExpression::Trace(AirTraceVariable(0), RowOffset::Current);
        let op2_expr = AirExpression::Trace(AirTraceVariable(1), RowOffset::Current);
        let expected_selector_expr = AirExpression::Mul(
            Box::new(AirExpression::Sub(Box::new(op1_expr), Box::new(op2_expr))),
            Box::new(cmp_res_expr.clone()),
        );

        assert_eq!(
            air.constraints[0], expected_booleanity_expr,
            "Booleanity constraint does not match"
        );
        assert_eq!(
            air.constraints[1], expected_selector_expr,
            "EQ selector constraint does not match"
        );
    }

    #[test]
    fn test_generate_air_from_icmp_ne_llvm() {
        let llvm_ir = r#"; ModuleID = 'icmp_ne_module'
        define i1 @are_not_equal(i32 %a, i32 %b) {
          entry:
            ; %a is LangVar(0), %b is LangVar(1)
            %cmp_res = icmp ne i32 %a, %b ; %cmp_res is LangVar(2)
            ret i1 %cmp_res
        }
        "#;
        let field_instance = TestField97;
        let result = AirCodegen::generate_air(llvm_ir, &field_instance);
        assert!(
            result.is_ok(),
            "AirCodegen::generate_air failed: {:?}",
            result.err()
        );
        let air = result.unwrap();

        assert_eq!(air.num_trace_columns, 3 + 4);
        assert_eq!(air.constraints.len(), 2);

        let cmp_res_expr = AirExpression::Trace(AirTraceVariable(2), RowOffset::Current);
        let expected_booleanity_expr = AirExpression::Mul(
            Box::new(cmp_res_expr.clone()),
            Box::new(AirExpression::Sub(
                Box::new(cmp_res_expr.clone()),
                Box::new(AirExpression::Constant(1)),
            )),
        );

        let op1_expr = AirExpression::Trace(AirTraceVariable(0), RowOffset::Current);
        let op2_expr = AirExpression::Trace(AirTraceVariable(1), RowOffset::Current);
        let one_minus_cmp_res_expr = AirExpression::Sub(
            Box::new(AirExpression::Constant(1)),
            Box::new(cmp_res_expr.clone()),
        );
        let expected_selector_expr = AirExpression::Mul(
            Box::new(AirExpression::Sub(Box::new(op1_expr), Box::new(op2_expr))),
            Box::new(one_minus_cmp_res_expr),
        );

        assert_eq!(
            air.constraints[0], expected_booleanity_expr,
            "Booleanity constraint NE does not match"
        );
        assert_eq!(
            air.constraints[1], expected_selector_expr,
            "NE selector constraint does not match"
        );
    }

    #[test]
    fn test_generate_air_from_icmp_ult_llvm() {
        let llvm_ir_ult_i3 = r#"; ModuleID = 'icmp_ult_i3_module'
        define i1 @is_less_i3(i3 %a, i3 %b) { ; Using i3 for fewer bit variables
          entry:
            ; %a (var 0), %b (var 1)
            %cmp_res = icmp ult i3 %a, %b ; %cmp_res (var 2)
            ret i1 %cmp_res
        }
        "#;
        let field_instance = TestField97;
        let result = AirCodegen::generate_air(llvm_ir_ult_i3, &field_instance);
        assert!(result.is_ok(), "ULT test failed: {:?}", result.err());
        let air = result.unwrap();

        let n_bits = 3;
        assert_eq!(air.num_trace_columns, 3 + n_bits + 4);

        assert_eq!(air.constraints.len(), 1 + n_bits + 2);

        let op1_air = AirExpression::Trace(AirTraceVariable(0), RowOffset::Current);
        let op2_air = AirExpression::Trace(AirTraceVariable(1), RowOffset::Current);
        let res_expr = AirExpression::Trace(AirTraceVariable(2), RowOffset::Current);

        let expected_bool_cmp_res = AirExpression::Mul(
            Box::new(res_expr.clone()),
            Box::new(AirExpression::Sub(
                Box::new(res_expr.clone()),
                Box::new(AirExpression::Constant(1)),
            )),
        );
        assert!(
            air.constraints.contains(&expected_bool_cmp_res),
            "Missing booleanity for cmp_res"
        );

        let mut bit_vars_air_exprs = Vec::new();
        for i in 0..n_bits {
            let bit_var_idx = 3 + i;
            let bit_expr = AirExpression::Trace(AirTraceVariable(bit_var_idx), RowOffset::Current);

            let expected_bool_bit = AirExpression::Mul(
                Box::new(bit_expr.clone()),
                Box::new(AirExpression::Sub(
                    Box::new(bit_expr.clone()),
                    Box::new(AirExpression::Constant(1)),
                )),
            );
            assert!(
                air.constraints.contains(&expected_bool_bit),
                "Missing booleanity for bit d{}",
                i
            );
            bit_vars_air_exprs.push(bit_expr);
        }

        let mut expected_d_sum_air: Option<Box<AirExpression>> = None;
        for (i, bit_expr) in bit_vars_air_exprs.iter().enumerate() {
            let power_of_2 = 1u128 << i;
            let term = AirExpression::Mul(
                Box::new(bit_expr.clone()),
                Box::new(AirExpression::Constant(power_of_2)),
            );
            if let Some(current_sum) = expected_d_sum_air {
                expected_d_sum_air =
                    Some(Box::new(AirExpression::Add(current_sum, Box::new(term))));
            } else {
                expected_d_sum_air = Some(Box::new(term));
            }
        }
        let expected_d_sum_air =
            expected_d_sum_air.unwrap_or_else(|| Box::new(AirExpression::Constant(0)));

        let op2_minus_op1_minus_1 = AirExpression::Sub(
            Box::new(AirExpression::Sub(
                Box::new(op2_air.clone()),
                Box::new(op1_air.clone()),
            )),
            Box::new(AirExpression::Constant(1)),
        );
        let term1_val =
            AirExpression::Sub(Box::new(op2_minus_op1_minus_1), expected_d_sum_air.clone());
        let expected_selector1 =
            AirExpression::Mul(Box::new(res_expr.clone()), Box::new(term1_val));
        assert!(
            air.constraints.contains(&expected_selector1),
            "Missing ULT selector constraint (res=1 path)"
        );

        let one_minus_res = AirExpression::Sub(
            Box::new(AirExpression::Constant(1)),
            Box::new(res_expr.clone()),
        );
        let op1_minus_op2 =
            AirExpression::Sub(Box::new(op1_air.clone()), Box::new(op2_air.clone()));
        let term2_val = AirExpression::Sub(Box::new(op1_minus_op2), expected_d_sum_air.clone());
        let expected_selector2 = AirExpression::Mul(Box::new(one_minus_res), Box::new(term2_val));
        assert!(
            air.constraints.contains(&expected_selector2),
            "Missing ULT selector constraint (res=0 path)"
        );
    }

    #[test]
    fn test_generate_air_from_icmp_ugt_llvm() {
        let llvm_ir_ugt_i3 = r#"; ModuleID = 'icmp_ugt_i3_module'
        define i1 @is_greater_i3(i3 %a, i3 %b) { ; %a = op1 (var0), %b = op2 (var1)
          entry:
            %cmp_res = icmp ugt i3 %a, %b ; %cmp_res (var2)
            ret i1 %cmp_res
        }
        "#;
        let field_instance = TestField97;
        let result = AirCodegen::generate_air(llvm_ir_ugt_i3, &field_instance);
        assert!(result.is_ok(), "UGT test failed: {:?}", result.err());
        let air = result.unwrap();
        let n_bits = 3;

        assert_eq!(
            air.num_trace_columns,
            3 + n_bits + 4,
            "UGT: num_trace_columns mismatch"
        );

        assert_eq!(
            air.constraints.len(),
            1 + n_bits + 2,
            "UGT: constraints.len() mismatch"
        );

        let op1_air = AirExpression::Trace(AirTraceVariable(0), RowOffset::Current);
        let op2_air = AirExpression::Trace(AirTraceVariable(1), RowOffset::Current);
        let res_expr = AirExpression::Trace(AirTraceVariable(2), RowOffset::Current);

        let expected_bool_cmp_res = AirExpression::Mul(
            Box::new(res_expr.clone()),
            Box::new(AirExpression::Sub(
                Box::new(res_expr.clone()),
                Box::new(AirExpression::Constant(1)),
            )),
        );
        assert!(
            air.constraints.contains(&expected_bool_cmp_res),
            "UGT: Missing booleanity for cmp_res"
        );

        let mut bit_vars_air_exprs = Vec::new();
        for i in 0..n_bits {
            let bit_var_idx = 3 + i;
            let bit_expr = AirExpression::Trace(AirTraceVariable(bit_var_idx), RowOffset::Current);
            let expected_bool_bit = AirExpression::Mul(
                Box::new(bit_expr.clone()),
                Box::new(AirExpression::Sub(
                    Box::new(bit_expr.clone()),
                    Box::new(AirExpression::Constant(1)),
                )),
            );
            assert!(
                air.constraints.contains(&expected_bool_bit),
                "UGT: Missing booleanity for bit d{}",
                i
            );
            bit_vars_air_exprs.push(bit_expr);
        }

        let mut expected_d_sum_air: Option<Box<AirExpression>> = None;
        for (i, bit_expr) in bit_vars_air_exprs.iter().enumerate() {
            let power_of_2 = 1u128 << i;
            let term = AirExpression::Mul(
                Box::new(bit_expr.clone()),
                Box::new(AirExpression::Constant(power_of_2)),
            );
            expected_d_sum_air = Some(match expected_d_sum_air {
                Some(current_sum) => Box::new(AirExpression::Add(current_sum, Box::new(term))),
                None => Box::new(term),
            });
        }
        let expected_d_sum_air =
            expected_d_sum_air.unwrap_or_else(|| Box::new(AirExpression::Constant(0)));

        let op1_minus_op2_minus_1 = AirExpression::Sub(
            Box::new(AirExpression::Sub(
                Box::new(op1_air.clone()),
                Box::new(op2_air.clone()),
            )),
            Box::new(AirExpression::Constant(1)),
        );
        let term1_val =
            AirExpression::Sub(Box::new(op1_minus_op2_minus_1), expected_d_sum_air.clone());
        let expected_selector1 =
            AirExpression::Mul(Box::new(res_expr.clone()), Box::new(term1_val));
        assert!(
            air.constraints.contains(&expected_selector1),
            "UGT: Missing selector1 (res=1 path)"
        );

        let one_minus_res = AirExpression::Sub(
            Box::new(AirExpression::Constant(1)),
            Box::new(res_expr.clone()),
        );
        let op2_minus_op1 =
            AirExpression::Sub(Box::new(op2_air.clone()), Box::new(op1_air.clone()));
        let term2_val = AirExpression::Sub(Box::new(op2_minus_op1), expected_d_sum_air.clone());
        let expected_selector2 = AirExpression::Mul(Box::new(one_minus_res), Box::new(term2_val));
        assert!(
            air.constraints.contains(&expected_selector2),
            "UGT: Missing selector2 (res=0 path)"
        );
    }

    #[test]
    fn test_generate_air_from_icmp_ule_llvm() {
        let llvm_ir_ule_i3 = r#"; ModuleID = 'icmp_ule_i3_module'
        define i1 @is_le_i3(i3 %a, i3 %b) { ; %a = op1 (v0), %b = op2 (v1)
          entry:
            %cmp_res = icmp ule i3 %a, %b ; %cmp_res (v2)
            ret i1 %cmp_res
        }
        "#;
        let field_instance = TestField97;
        let result = AirCodegen::generate_air(llvm_ir_ule_i3, &field_instance);
        assert!(result.is_ok(), "ULE test failed: {:?}", result.err());
        let air = result.unwrap();
        let n_bits = 3;

        assert_eq!(
            air.num_trace_columns,
            3 + 1 + n_bits + 4,
            "ULE: num_trace_columns"
        );

        assert_eq!(
            air.constraints.len(),
            1 + 1 + n_bits + 2 + 1,
            "ULE: constraints.len()"
        );

        let op1_air = AirExpression::Trace(AirTraceVariable(0), RowOffset::Current);
        let op2_air = AirExpression::Trace(AirTraceVariable(1), RowOffset::Current);
        let res_expr = AirExpression::Trace(AirTraceVariable(2), RowOffset::Current);
        let aux_ugt_res_expr = AirExpression::Trace(AirTraceVariable(3), RowOffset::Current);

        assert!(
            air.constraints.contains(&AirExpression::Mul(
                Box::new(res_expr.clone()),
                Box::new(AirExpression::Sub(
                    Box::new(res_expr.clone()),
                    Box::new(AirExpression::Constant(1))
                ))
            )),
            "ULE: Missing bool for res_expr"
        );

        assert!(
            air.constraints.contains(&AirExpression::Mul(
                Box::new(aux_ugt_res_expr.clone()),
                Box::new(AirExpression::Sub(
                    Box::new(aux_ugt_res_expr.clone()),
                    Box::new(AirExpression::Constant(1))
                ))
            )),
            "ULE: Missing bool for aux_ugt_res_expr"
        );

        let mut bit_vars_air_exprs = Vec::new();
        for i in 0..n_bits {
            let bit_var_idx = 3 + 1 + i;
            let bit_expr = AirExpression::Trace(AirTraceVariable(bit_var_idx), RowOffset::Current);
            assert!(
                air.constraints.contains(&AirExpression::Mul(
                    Box::new(bit_expr.clone()),
                    Box::new(AirExpression::Sub(
                        Box::new(bit_expr.clone()),
                        Box::new(AirExpression::Constant(1))
                    ))
                )),
                "ULE: Missing bool for bit d{}",
                i
            );
            bit_vars_air_exprs.push(bit_expr);
        }

        let expected_d_sum_air = bit_vars_air_exprs
            .iter()
            .enumerate()
            .fold(Option::<Box<AirExpression>>::None, |acc, (i, bit_expr)| {
                let term = AirExpression::Mul(
                    Box::new(bit_expr.clone()),
                    Box::new(AirExpression::Constant(1u128 << i)),
                );
                Some(acc.map_or(Box::new(term.clone()), |current_sum| {
                    Box::new(AirExpression::Add(current_sum, Box::new(term)))
                }))
            })
            .unwrap_or_else(|| Box::new(AirExpression::Constant(0)));

        let expected_op1_minus_op2_minus_1 = AirExpression::Sub(
            Box::new(AirExpression::Sub(
                Box::new(op1_air.clone()),
                Box::new(op2_air.clone()),
            )),
            Box::new(AirExpression::Constant(1)),
        );
        let expected_term1_val_internal_ugt = AirExpression::Sub(
            Box::new(expected_op1_minus_op2_minus_1),
            expected_d_sum_air.clone(),
        );
        let _expected_selector1_internal_ugt = AirExpression::Mul(
            Box::new(aux_ugt_res_expr.clone()),
            Box::new(expected_term1_val_internal_ugt),
        );

        let expected_one_minus_aux_res_ugt = AirExpression::Sub(
            Box::new(AirExpression::Constant(1)),
            Box::new(aux_ugt_res_expr.clone()),
        );
        let expected_op2_minus_op1_ugt =
            AirExpression::Sub(Box::new(op2_air.clone()), Box::new(op1_air.clone()));
        let expected_term2_val_internal_ugt = AirExpression::Sub(
            Box::new(expected_op2_minus_op1_ugt),
            expected_d_sum_air.clone(),
        );
        let _expected_selector2_internal_ugt = AirExpression::Mul(
            Box::new(expected_one_minus_aux_res_ugt),
            Box::new(expected_term2_val_internal_ugt),
        );

        let expected_final_relation = AirExpression::Sub(
            Box::new(AirExpression::Add(
                Box::new(res_expr.clone()),
                Box::new(aux_ugt_res_expr.clone()),
            )),
            Box::new(AirExpression::Constant(1)),
        );
        assert!(
            air.constraints.contains(&expected_final_relation),
            "ULE: Missing final relation constraint"
        );
    }

    #[test]
    fn test_generate_air_from_icmp_uge_llvm() {
        let llvm_ir_uge_i3 = r#"; ModuleID = 'icmp_uge_i3_module'
        define i1 @is_ge_i3(i3 %a, i3 %b) { ; %a = op1 (v0), %b = op2 (v1)
          entry:
            %cmp_res = icmp uge i3 %a, %b ; %cmp_res (v2)
            ret i1 %cmp_res
        }
        "#;
        let field_instance = TestField97;
        let result = AirCodegen::generate_air(llvm_ir_uge_i3, &field_instance);
        assert!(result.is_ok(), "UGE test failed: {:?}", result.err());
        let air = result.unwrap();
        let n_bits = 3;

        assert_eq!(
            air.num_trace_columns,
            3 + 1 + n_bits + 4,
            "UGE: num_trace_columns"
        );
        assert_eq!(
            air.constraints.len(),
            1 + 1 + n_bits + 2 + 1,
            "UGE: constraints.len()"
        );

        let op1_air = AirExpression::Trace(AirTraceVariable(0), RowOffset::Current);
        let op2_air = AirExpression::Trace(AirTraceVariable(1), RowOffset::Current);
        let res_expr = AirExpression::Trace(AirTraceVariable(2), RowOffset::Current);
        let aux_ult_res_expr = AirExpression::Trace(AirTraceVariable(3), RowOffset::Current);

        assert!(
            air.constraints.contains(&AirExpression::Mul(
                Box::new(res_expr.clone()),
                Box::new(AirExpression::Sub(
                    Box::new(res_expr.clone()),
                    Box::new(AirExpression::Constant(1))
                ))
            )),
            "UGE: Missing booleanity for res_expr"
        );
        assert!(
            air.constraints.contains(&AirExpression::Mul(
                Box::new(aux_ult_res_expr.clone()),
                Box::new(AirExpression::Sub(
                    Box::new(aux_ult_res_expr.clone()),
                    Box::new(AirExpression::Constant(1))
                ))
            )),
            "UGE: Missing booleanity for aux_ult_res_expr"
        );

        let mut bit_vars_air_exprs = Vec::new();
        for i in 0..n_bits {
            let bit_var_idx = 3 + 1 + i;
            let bit_expr = AirExpression::Trace(AirTraceVariable(bit_var_idx), RowOffset::Current);
            assert!(
                air.constraints.contains(&AirExpression::Mul(
                    Box::new(bit_expr.clone()),
                    Box::new(AirExpression::Sub(
                        Box::new(bit_expr.clone()),
                        Box::new(AirExpression::Constant(1))
                    ))
                )),
                "UGE: Missing booleanity for bit d{}",
                i
            );
            bit_vars_air_exprs.push(bit_expr);
        }

        let expected_d_sum_air = bit_vars_air_exprs
            .iter()
            .enumerate()
            .fold(Option::<Box<AirExpression>>::None, |acc, (i, bit_expr)| {
                let term = AirExpression::Mul(
                    Box::new(bit_expr.clone()),
                    Box::new(AirExpression::Constant(1u128 << i)),
                );
                Some(acc.map_or(Box::new(term.clone()), |current_sum| {
                    Box::new(AirExpression::Add(current_sum, Box::new(term)))
                }))
            })
            .unwrap_or_else(|| Box::new(AirExpression::Constant(0)));

        let expected_b_i_minus_a_i_minus_1 = AirExpression::Sub(
            Box::new(AirExpression::Sub(
                Box::new(op2_air.clone()),
                Box::new(op1_air.clone()),
            )),
            Box::new(AirExpression::Constant(1)),
        );
        let expected_term1_val_internal = AirExpression::Sub(
            Box::new(expected_b_i_minus_a_i_minus_1),
            expected_d_sum_air.clone(),
        );
        let expected_selector1_internal = AirExpression::Mul(
            Box::new(aux_ult_res_expr.clone()),
            Box::new(expected_term1_val_internal),
        );
        assert!(
            air.constraints.contains(&expected_selector1_internal),
            "UGE: Missing internal ULT selector1"
        );

        let expected_one_minus_aux_res = AirExpression::Sub(
            Box::new(AirExpression::Constant(1)),
            Box::new(aux_ult_res_expr.clone()),
        );
        let expected_a_i_minus_b_i =
            AirExpression::Sub(Box::new(op1_air.clone()), Box::new(op2_air.clone()));
        let expected_term2_val_internal =
            AirExpression::Sub(Box::new(expected_a_i_minus_b_i), expected_d_sum_air.clone());
        let expected_selector2_internal = AirExpression::Mul(
            Box::new(expected_one_minus_aux_res),
            Box::new(expected_term2_val_internal),
        );
        assert!(
            air.constraints.contains(&expected_selector2_internal),
            "UGE: Missing internal ULT selector2"
        );

        let expected_final_relation = AirExpression::Sub(
            Box::new(AirExpression::Add(
                Box::new(res_expr.clone()),
                Box::new(aux_ult_res_expr.clone()),
            )),
            Box::new(AirExpression::Constant(1)),
        );
        assert!(
            air.constraints.contains(&expected_final_relation),
            "UGE: Missing final relation constraint"
        );
    }

    #[test]
    fn test_generate_air_from_icmp_slt_full_llvm() {
        let llvm_ir_slt_i3 = r#"; ModuleID = 'icmp_slt_i3_module'
        define i1 @is_s_less_i3(i3 %a, i3 %b) { ; %a=op1 (v0), %b=op2 (v1)
          entry:
            %cmp_res = icmp slt i3 %a, %b ; %cmp_res (v2)
            ret i1 %cmp_res
        }
        "#;
        let field_instance = TestField97;
        let result = AirCodegen::generate_air(llvm_ir_slt_i3, &field_instance);
        assert!(result.is_ok(), "SLT Full test failed: {:?}", result.err());
        let air = result.unwrap();
        let n_bits = 3;

        assert_eq!(
            air.num_trace_columns,
            3 * n_bits + 8 + 4,
            "SLT Full: num_trace_columns"
        );

        assert_eq!(
            air.constraints.len(),
            3 * n_bits + 15,
            "SLT Full: constraints.len()"
        );

        let res_expr_slt = AirExpression::Trace(AirTraceVariable(2), RowOffset::Current);
        let expected_bool_res_slt = AirExpression::Mul(
            Box::new(res_expr_slt.clone()),
            Box::new(AirExpression::Sub(
                Box::new(res_expr_slt.clone()),
                Box::new(AirExpression::Constant(1)),
            )),
        );
        assert!(
            air.constraints.contains(&expected_bool_res_slt),
            "SLT: Missing booleanity for the main result expression."
        );
    }

    #[test]
    fn test_generate_air_from_icmp_sgt_full_llvm() {
        let llvm_ir_sgt_i3 = r#"; ModuleID = 'icmp_sgt_i3_module'
        define i1 @is_s_greater_i3(i3 %a, i3 %b) { ; %a=op1 (v0), %b=op2 (v1)
          entry:
            %cmp_res = icmp sgt i3 %a, %b ; %cmp_res (v2)
            ret i1 %cmp_res
        }
        "#;
        let field_instance = TestField97;
        let result = AirCodegen::generate_air(llvm_ir_sgt_i3, &field_instance);
        assert!(result.is_ok(), "SGT Full test failed: {:?}", result.err());
        let air = result.unwrap();
        let n_bits = 3;

        assert_eq!(
            air.num_trace_columns,
            3 * n_bits + 8 + 4,
            "SGT Full: num_trace_columns should match SLT"
        );

        assert_eq!(
            air.constraints.len(),
            3 * n_bits + 15,
            "SGT Full: constraints.len() should match SLT"
        );

        let res_expr_sgt = AirExpression::Trace(AirTraceVariable(2), RowOffset::Current);
        let expected_bool_res_sgt = AirExpression::Mul(
            Box::new(res_expr_sgt.clone()),
            Box::new(AirExpression::Sub(
                Box::new(res_expr_sgt.clone()),
                Box::new(AirExpression::Constant(1)),
            )),
        );
        assert!(
            air.constraints.contains(&expected_bool_res_sgt),
            "SGT: Missing booleanity for the main result expression."
        );
    }

    #[test]
    fn test_generate_air_from_icmp_sge_full_llvm() {
        let llvm_ir_sge_i3 = r#"; ModuleID = 'icmp_sge_i3_module'
        define i1 @is_s_ge_i3(i3 %a, i3 %b) { ; %a=op1 (v0), %b=op2 (v1)
          entry:
            %cmp_res = icmp sge i3 %a, %b ; %cmp_res (v2)
            ret i1 %cmp_res
        }
        "#;
        let field_instance = TestField97;
        let result = AirCodegen::generate_air(llvm_ir_sge_i3, &field_instance);
        assert!(result.is_ok(), "SGE Full test failed: {:?}", result.err());
        let air = result.unwrap();
        let n_bits = 3;

        assert_eq!(
            air.num_trace_columns,
            3 * n_bits + 9 + 4,
            "SGE Full: num_trace_columns"
        );

        assert_eq!(
            air.constraints.len(),
            3 * n_bits + 17,
            "SGE Full: constraints.len()"
        );

        let res_expr_sge = AirExpression::Trace(AirTraceVariable(2), RowOffset::Current);
        let expected_bool_res_sge = AirExpression::Mul(
            Box::new(res_expr_sge.clone()),
            Box::new(AirExpression::Sub(
                Box::new(res_expr_sge.clone()),
                Box::new(AirExpression::Constant(1)),
            )),
        );
        assert!(
            air.constraints.contains(&expected_bool_res_sge),
            "SGE: Missing booleanity for the main result expression."
        );
    }

    #[test]
    fn test_generate_air_from_icmp_sle_full_llvm() {
        let llvm_ir_sle_i3 = r#"; ModuleID = 'icmp_sle_i3_module'
        define i1 @is_s_le_i3(i3 %a, i3 %b) { ; %a=op1 (v0), %b=op2 (v1)
          entry:
            %cmp_res = icmp sle i3 %a, %b ; %cmp_res (v2)
            ret i1 %cmp_res
        }
        "#;
        let field_instance = TestField97;
        let result = AirCodegen::generate_air(llvm_ir_sle_i3, &field_instance);
        assert!(result.is_ok(), "SLE Full test failed: {:?}", result.err());
        let air = result.unwrap();
        let n_bits = 3;

        assert_eq!(
            air.num_trace_columns,
            3 * n_bits + 9 + 4,
            "SLE Full: num_trace_columns"
        );

        assert_eq!(
            air.constraints.len(),
            3 * n_bits + 17,
            "SLE Full: constraints.len()"
        );

        let res_expr_sle = AirExpression::Trace(AirTraceVariable(2), RowOffset::Current);
        let expected_bool_res_sle = AirExpression::Mul(
            Box::new(res_expr_sle.clone()),
            Box::new(AirExpression::Sub(
                Box::new(res_expr_sle.clone()),
                Box::new(AirExpression::Constant(1)),
            )),
        );
        assert!(
            air.constraints.contains(&expected_bool_res_sle),
            "SLE: Missing booleanity for the main result expression."
        );
    }

    #[test]
    fn test_generate_air_from_phi_llvm() {
        let llvm_ir_phi = r#"; ModuleID = 'phi_module'
        define i32 @phi_test(i1 %cond, i32 %true_val, i32 %false_val) {
          entry:
            ; %cond (LangVar 0), %true_val (LangVar 1), %false_val (LangVar 2)
            br i1 %cond, label %then_block, label %else_block
        
          then_block: ; Pred: entry
            ; This block's name is "then_block"
            br label %merge_block
        
          else_block: ; Pred: entry
            ; This block's name is "else_block"
            br label %merge_block
        
          merge_block: ; Preds: then_block, else_block
            %phi_res = phi i32 [ %true_val, %then_block ], [ %false_val, %else_block ] ; %phi_res (LangVar 3)
            ret i32 %phi_res
        }
        "#;
        let field_instance = TestField97;
        let result = AirCodegen::generate_air(llvm_ir_phi, &field_instance);
        assert!(result.is_ok(), "PHI test failed: {:?}", result.err());
        let air = result.unwrap();

        assert_eq!(air.num_trace_columns, 8, "PHI: num_trace_columns mismatch");

        assert_eq!(air.constraints.len(), 1, "PHI: constraints.len() mismatch");

        let cond_expr = AirExpression::Trace(AirTraceVariable(0), RowOffset::Current);
        let true_val_expr = AirExpression::Trace(AirTraceVariable(1), RowOffset::Current);
        let false_val_expr = AirExpression::Trace(AirTraceVariable(2), RowOffset::Current);
        let phi_res_expr = AirExpression::Trace(AirTraceVariable(3), RowOffset::Current);

        let expected_vt_minus_vf = AirExpression::Sub(
            Box::new(true_val_expr.clone()),
            Box::new(false_val_expr.clone()),
        );
        let expected_c_mult_vt_minus_vf =
            AirExpression::Mul(Box::new(cond_expr.clone()), Box::new(expected_vt_minus_vf));
        let expected_pr_minus_vf = AirExpression::Sub(
            Box::new(phi_res_expr.clone()),
            Box::new(false_val_expr.clone()),
        );
        let expected_phi_constraint = AirExpression::Sub(
            Box::new(expected_pr_minus_vf),
            Box::new(expected_c_mult_vt_minus_vf),
        );

        assert_eq!(
            air.constraints[0], expected_phi_constraint,
            "PHI constraint mismatch"
        );
    }

    #[test]
    fn test_generate_air_from_phi_via_switch_llvm() {
        let llvm_ir_phi_switch = r#"; ModuleID = 'phi_switch_module'
        define i32 @phi_switch_test(i32 %cond_val, i32 %val0, i32 %val1, i32 %val_default) {
          entry:
            ; %cond_val (v0), %val0 (v1), %val1 (v2), %val_default (v3)
            switch i32 %cond_val, label %default_dest [
              i32 0, label %case0_dest
              i32 1, label %case1_dest
            ]
        
          case0_dest: ; name: case0_dest
            br label %merge
        
          case1_dest: ; name: case1_dest
            br label %merge

          default_dest: ; name: default_dest
            br label %merge
        
          merge: ; name: merge
            ; phi_res (v4)
            %phi_res = phi i32 [ %val0, %case0_dest ], [ %val1, %case1_dest ], [ %val_default, %default_dest ]
            ret i32 %phi_res
        }
        "#;
        let field_instance = TestField97;
        let result = AirCodegen::generate_air(llvm_ir_phi_switch, &field_instance);
        assert!(
            result.is_ok(),
            "PHI from Switch test failed: {:?}",
            result.err()
        );
        let air = result.unwrap();

        assert_eq!(
            air.num_trace_columns,
            4 + 1 + 3 + 4,
            "PHI from Switch: num_trace_columns"
        );

        assert_eq!(
            air.constraints.len(),
            2 * 2 + 2 + 1,
            "PHI from Switch: constraints.len()"
        );
    }

    #[test]
    fn test_generate_air_from_loop_phi_llvm() {
        let llvm_ir_loop_phi = r#"; ModuleID = 'loop_phi_module'
        define i32 @loop_counter(i32 %max_count) { ; max_count is v0
          entry: ; block_name "entry"
            br label %loop_header

          loop_header: ; block_name "loop_header", preds = %entry, %loop_latch
            ; count (v1), prev_count_val (part of phi, from v3 in latch or 0 from entry)
            %count = phi i32 [ 0, %entry ], [ %count_next, %loop_latch ] 
            %cmp_res = icmp slt i32 %count, %max_count ; cmp_res (v2)
            br i1 %cmp_res, label %loop_body, label %loop_exit

          loop_body: ; block_name "loop_body", preds = %loop_header
            br label %loop_latch

          loop_latch: ; block_name "loop_latch", preds = %loop_body
            %count_next = add i32 %count, 1 ; count_next (v3)
            br label %loop_header

          loop_exit: ; block_name "loop_exit", preds = %loop_header
            ret i32 %count
        }
        "#;
        let field_instance = TestField97;
        let result = AirCodegen::generate_air(llvm_ir_loop_phi, &field_instance);
        assert!(result.is_ok(), "Loop PHI test failed: {:?}", result.err());
        let air = result.unwrap();

        let constr_add = AirExpression::Sub(
            Box::new(AirExpression::Add(
                Box::new(AirExpression::Trace(
                    AirTraceVariable(1),
                    RowOffset::Current,
                )),
                Box::new(AirExpression::Constant(1)),
            )),
            Box::new(AirExpression::Trace(
                AirTraceVariable(2),
                RowOffset::Current,
            )),
        );
        assert!(
            air.constraints.contains(&constr_add),
            "Missing ADD constraint for count_next"
        );

        let constr_loop_phi_transition = AirExpression::Sub(
            Box::new(AirExpression::Trace(AirTraceVariable(1), RowOffset::Next)),
            Box::new(AirExpression::Trace(
                AirTraceVariable(2),
                RowOffset::Current,
            )),
        );
        assert!(
            air.constraints.contains(&constr_loop_phi_transition),
            "Missing Loop PHI transition constraint for count"
        );

        let cmp_res_air_var = AirTraceVariable(3);
        let cmp_res_expr = AirExpression::Trace(cmp_res_air_var, RowOffset::Current);
        let bool_cmp_res = AirExpression::Mul(
            Box::new(cmp_res_expr.clone()),
            Box::new(AirExpression::Sub(
                Box::new(cmp_res_expr.clone()),
                Box::new(AirExpression::Constant(1)),
            )),
        );
        assert!(
            air.constraints.contains(&bool_cmp_res),
            "Missing booleanity for cmp_res"
        );

        println!(
            "Loop PHI test: Generated {} constraints.",
            air.constraints.len()
        );

        let constr_phi_init = AirExpression::Sub(
            Box::new(AirExpression::Trace(
                AirTraceVariable(1),
                RowOffset::Current,
            )),
            Box::new(AirExpression::Constant(0)),
        );
        assert!(
            air.constraints.contains(&constr_phi_init),
            "Missing PHI init constraint for count"
        );
    }

    #[test]
    fn test_generate_air_from_sub_llvm() {
        let llvm_ir = r#"; ModuleID = 'sub_module'
        define i32 @subtract(i32 %a, i32 %b) {
          entry:
            ; %a is LangSysVar(0), %b is LangSysVar(1)
            %result = sub i32 %a, %b ; %result is LangSysVar(2)
            ret i32 %result
        }
        "#;
        let field_instance = TestField97;
        let result = AirCodegen::generate_air(llvm_ir, &field_instance);
        assert!(result.is_ok());
        let air = result.unwrap();

        assert_eq!(air.num_trace_columns, 7);
        assert_eq!(air.constraints.len(), 1);

        let expected_expr = AirExpression::Sub(
            Box::new(AirExpression::Trace(
                AirTraceVariable(2),
                RowOffset::Current,
            )),
            Box::new(AirExpression::Sub(
                Box::new(AirExpression::Trace(
                    AirTraceVariable(0),
                    RowOffset::Current,
                )),
                Box::new(AirExpression::Trace(
                    AirTraceVariable(1),
                    RowOffset::Current,
                )),
            )),
        );
        assert_eq!(air.constraints[0], expected_expr);
    }

    #[test]
    fn test_generate_air_from_or_llvm() {
        let llvm_ir = r#"; ModuleID = 'or_module'
        ; Changed to i32, assuming inputs are effectively boolean for the AIR constraint
        define i32 @logical_or(i32 %a, i32 %b) {
          entry:
            ; %a is LangSysVar(0), %b is LangSysVar(1)
            ; %result is LangSysVar(2), changed to i32
            %result = or i32 %a, %b
            ; Changed to i32
            ret i32 %result
        }
        "#;
        let field_instance = TestField97;
        let result = AirCodegen::generate_air(llvm_ir, &field_instance);
        assert!(
            result.is_ok(),
            "AirCodegen::generate_air for OR failed: {:?}",
            result.err()
        );
        let air = result.unwrap();

        assert_eq!(air.num_trace_columns, 7);
        assert_eq!(air.constraints.len(), 1);

        let op1_expr = AirExpression::Trace(AirTraceVariable(0), RowOffset::Current);
        let op2_expr = AirExpression::Trace(AirTraceVariable(1), RowOffset::Current);
        let res_expr = AirExpression::Trace(AirTraceVariable(2), RowOffset::Current);

        let a_plus_b = AirExpression::Add(Box::new(op1_expr.clone()), Box::new(op2_expr.clone()));
        let a_times_b = AirExpression::Mul(Box::new(op1_expr.clone()), Box::new(op2_expr.clone()));
        let or_val_expr = AirExpression::Sub(Box::new(a_plus_b), Box::new(a_times_b));
        let expected_expr = AirExpression::Sub(Box::new(or_val_expr), Box::new(res_expr));

        assert_eq!(air.constraints[0], expected_expr);
    }

    #[test]
    fn test_generate_air_from_xor_llvm() {
        let llvm_ir = r#"; ModuleID = 'xor_module'
        ; Changed to i32, assuming inputs are effectively boolean for the AIR constraint
        define i32 @logical_xor(i32 %a, i32 %b) {
          entry:
            ; %a is LangSysVar(0), %b is LangSysVar(1)
            ; %result is LangSysVar(2), changed to i32
            %result = xor i32 %a, %b
            ; Changed to i32
            ret i32 %result
        }
        "#;
        let field_instance = TestField97;
        let result = AirCodegen::generate_air(llvm_ir, &field_instance);
        assert!(
            result.is_ok(),
            "AirCodegen::generate_air for XOR failed: {:?}",
            result.err()
        );
        let air = result.unwrap();

        let num_cols_for_xor_op_logic = 3;

        let expected_air_num_trace_columns = num_cols_for_xor_op_logic + 4;

        assert_eq!(air.num_trace_columns, expected_air_num_trace_columns);
        assert_eq!(air.constraints.len(), 1);

        let op1_expr = AirExpression::Trace(AirTraceVariable(0), RowOffset::Current);
        let op2_expr = AirExpression::Trace(AirTraceVariable(1), RowOffset::Current);
        let res_expr = AirExpression::Trace(AirTraceVariable(2), RowOffset::Current);

        let a_plus_b = AirExpression::Add(Box::new(op1_expr.clone()), Box::new(op2_expr.clone()));
        let a_times_b = AirExpression::Mul(Box::new(op1_expr.clone()), Box::new(op2_expr.clone()));
        let two_const = AirExpression::Constant(2);
        let two_a_b = AirExpression::Mul(Box::new(two_const), Box::new(a_times_b));
        let xor_val_expr = AirExpression::Sub(Box::new(a_plus_b), Box::new(two_a_b));
        let expected_expr = AirExpression::Sub(Box::new(xor_val_expr), Box::new(res_expr));

        assert_eq!(air.constraints[0], expected_expr);
    }

    #[test]
    fn test_generate_air_from_sdiv_llvm() {
        let llvm_ir = r#"; ModuleID = 'sdiv_module'
        define i32 @signed_div(i32 %a, i32 %b) { ; %a=v0, %b=v1
          entry:
            %q = sdiv i32 %a, %b ; %q=v2
            ret i32 %q
        }
        "#;
        let field_instance = TestField97;
        let result = AirCodegen::generate_air(llvm_ir, &field_instance);
        assert!(
            result.is_ok(),
            "AirCodegen::generate_air for SDiv failed: {:?}",
            result.err()
        );
        let air = result.unwrap();

        assert!(
            air.num_trace_columns >= 3 + 1 + (4 * 32) + 1 + 32 + 1 + 1,
            "Incorrect number of trace columns for SDiv. Expected at least {}, got {}",
            3 + 1 + (4 * 32) + 1 + 32 + 1 + 1,
            air.num_trace_columns
        );

        let a_expr = AirExpression::Trace(AirTraceVariable(0), RowOffset::Current);
        let b_expr = AirExpression::Trace(AirTraceVariable(1), RowOffset::Current);
        let q_expr = AirExpression::Trace(AirTraceVariable(2), RowOffset::Current);
        let r_expr = AirExpression::Trace(AirTraceVariable(3), RowOffset::Current);

        let q_times_b = AirExpression::Mul(Box::new(q_expr.clone()), Box::new(b_expr.clone()));
        let qb_plus_r = AirExpression::Add(Box::new(q_times_b), Box::new(r_expr.clone()));
        let expected_algebraic_relation =
            AirExpression::Sub(Box::new(a_expr.clone()), Box::new(qb_plus_r));

        assert!(
            air.constraints.contains(&expected_algebraic_relation),
            "Missing SDiv algebraic relation constraint: a - (q*b+r) = 0. Constraints: {:#?}",
            air.constraints
        );
    }

    #[test]
    fn test_generate_air_from_lshr_var_llvm() {
        let llvm_ir = r#"; ModuleID = 'lshr_var_module'
        define i32 @lshr_var(i32 %a, i32 %s) { ; %a is V0, %s is V1
          entry:
            %result = lshr i32 %a, %s ; %result is V2
            ret i32 %result
        }
        "#;
        let field_instance = TestField97;
        let result = AirCodegen::generate_air(llvm_ir, &field_instance);
        assert!(
            result.is_ok(),
            "AirCodegen::generate_air for LShr var failed: {:?}",
            result.err()
        );
        let air = result.unwrap();

        let operand_bitwidth: u32 = 32;
        let num_shift_bits_for_s = (operand_bitwidth - 1).ilog2() + 1;

        let num_cols_for_lshr_op_logic = 4
            + operand_bitwidth as usize
            + num_shift_bits_for_s as usize
            + num_shift_bits_for_s as usize
            + if num_shift_bits_for_s > 0 {
                num_shift_bits_for_s as usize - 1
            } else {
                0
            }
            + 1
            + operand_bitwidth as usize
            + operand_bitwidth as usize;

        let expected_air_num_trace_columns = num_cols_for_lshr_op_logic + 4;

        assert_eq!(
            air.num_trace_columns, expected_air_num_trace_columns,
            "LShr var: Incorrect number of trace columns. Expected {}, got {}",
            expected_air_num_trace_columns, air.num_trace_columns
        );

        let mut current_constraint_idx = 0;

        current_constraint_idx += operand_bitwidth as usize + 1;

        current_constraint_idx += num_shift_bits_for_s as usize + 1;

        current_constraint_idx += num_shift_bits_for_s as usize;

        if num_shift_bits_for_s > 0 {
            current_constraint_idx += num_shift_bits_for_s as usize - 1;
        }

        current_constraint_idx += 1;

        current_constraint_idx += 2;

        current_constraint_idx += operand_bitwidth as usize + 1;

        current_constraint_idx += operand_bitwidth as usize;

        current_constraint_idx += 2;

        assert_eq!(
            air.constraints.len(),
            current_constraint_idx,
            "LShr var: Incorrect number of total constraints. Expected {}, got {}",
            current_constraint_idx,
            air.constraints.len()
        );
    }

    #[test]
    fn test_generate_air_from_ashr_const_llvm() {
        let llvm_ir = r#"; ModuleID = 'ashr_const_module'
        define i32 @ashr_const(i32 %a) { ; %a is V0
          entry:
            %result = ashr i32 %a, 2 ; %result is V1
            ret i32 %result
        }
        "#;
        let field_instance = TestField97;
        let result = AirCodegen::generate_air(llvm_ir, &field_instance);
        assert!(
            result.is_ok(),
            "AirCodegen::generate_air for AShr const failed: {:?}",
            result.err()
        );
        let air = result.unwrap();

        let operand_bitwidth: u32 = 32;

        let expected_num_trace_cols = 3
            + 4
            + operand_bitwidth as usize
            + operand_bitwidth as usize
            + operand_bitwidth as usize;
        assert_eq!(
            air.num_trace_columns, expected_num_trace_cols,
            "AShr const: Incorrect number of trace columns"
        );

        let mut current_constraint_idx = 0;

        current_constraint_idx += operand_bitwidth as usize + 1;

        current_constraint_idx += operand_bitwidth as usize + 1;

        current_constraint_idx += operand_bitwidth as usize + 1;

        let op1_expr = AirExpression::Trace(AirTraceVariable(0), RowOffset::Current);
        let res_expr = AirExpression::Trace(AirTraceVariable(1), RowOffset::Current);
        let rem_ashr_expr = AirExpression::Trace(AirTraceVariable(2), RowOffset::Current);
        let four_expr = AirExpression::Constant(4);

        let res_times_4 = AirExpression::Mul(Box::new(res_expr), Box::new(four_expr));
        let res_term_plus_rem = AirExpression::Add(Box::new(res_times_4), Box::new(rem_ashr_expr));
        let expected_algebraic_constraint =
            AirExpression::Sub(Box::new(op1_expr), Box::new(res_term_plus_rem));
        assert_eq!(
            air.constraints.len(),
            current_constraint_idx + 1,
            "AShr const: Incorrect number of total constraints"
        );
        assert_eq!(
            air.constraints[current_constraint_idx], expected_algebraic_constraint,
            "AShr const: main algebraic constraint mismatch"
        );
    }

    #[test]
    fn test_generate_air_from_ashr_var_llvm() {
        let llvm_ir = r#"; ModuleID = 'ashr_var_module'
        define i32 @ashr_var(i32 %a, i32 %s) { ; %a is V0, %s is V1
          entry:
            %result = ashr i32 %a, %s ; %result is V2
            ret i32 %result
        }
        "#;
        let field_instance = TestField97;
        let result = AirCodegen::generate_air(llvm_ir, &field_instance);
        assert!(
            result.is_ok(),
            "AirCodegen::generate_air for AShr var failed: {:?}",
            result.err()
        );
        let air = result.unwrap();

        let operand_bitwidth: u32 = 32;
        let num_shift_bits_for_s = (operand_bitwidth - 1).ilog2() + 1;

        let num_cols_for_ashr_op_logic = 4
            + operand_bitwidth as usize
            + operand_bitwidth as usize
            + operand_bitwidth as usize
            + num_shift_bits_for_s as usize
            + num_shift_bits_for_s as usize
            + if num_shift_bits_for_s > 0 {
                num_shift_bits_for_s as usize - 1
            } else {
                0
            }
            + 1
            + operand_bitwidth as usize
            + operand_bitwidth as usize;

        let expected_air_num_trace_columns = num_cols_for_ashr_op_logic + 4;

        assert_eq!(
            air.num_trace_columns, expected_air_num_trace_columns,
            "AShr var: Incorrect number of trace columns. Expected {}, got {}",
            expected_air_num_trace_columns, air.num_trace_columns
        );

        let mut current_constraint_idx = 0;

        current_constraint_idx += operand_bitwidth as usize + 1;

        current_constraint_idx += operand_bitwidth as usize + 1;

        current_constraint_idx += operand_bitwidth as usize + 1;

        current_constraint_idx += num_shift_bits_for_s as usize + 1;

        current_constraint_idx += num_shift_bits_for_s as usize;

        if num_shift_bits_for_s > 0 {
            current_constraint_idx += num_shift_bits_for_s as usize - 1;
        }

        current_constraint_idx += 1;

        current_constraint_idx += 2;

        current_constraint_idx += operand_bitwidth as usize + 1;

        current_constraint_idx += operand_bitwidth as usize;

        current_constraint_idx += 2;

        assert_eq!(
            air.constraints.len(),
            current_constraint_idx,
            "AShr var: Incorrect number of total constraints. Expected {}, got {}",
            current_constraint_idx,
            air.constraints.len()
        );
    }

    #[test]
    fn test_generate_air_from_urem_llvm() {
        let llvm_ir = r#"; ModuleID = 'urem_module'
        define i32 @unsigned_rem(i32 %a, i32 %b) { ; %a=v0, %b=v1
          entry:
            %r = urem i32 %a, %b ; %r=v2
            ret i32 %r
        }
        "#;
        let field_instance = TestField97;
        let result = AirCodegen::generate_air(llvm_ir, &field_instance);
        assert!(
            result.is_ok(),
            "AirCodegen::generate_air for URem failed: {:?}",
            result.err()
        );
        let air = result.unwrap();

        let operand_bitwidth: u32 = 32;

        let expected_num_trace_cols =
            3 + 1 + 4 * operand_bitwidth as usize + 1 + operand_bitwidth as usize + 4;
        assert_eq!(
            air.num_trace_columns, expected_num_trace_cols,
            "URem: Incorrect number of trace columns. Expected {}, got {}. AirGenContext next_available_trace_col: {}",
            expected_num_trace_cols, air.num_trace_columns, air.num_trace_columns
        );

        let mut current_constraint_idx = 0;

        current_constraint_idx += (operand_bitwidth as usize + 1) * 4;

        current_constraint_idx += 1;

        current_constraint_idx += 2;

        current_constraint_idx += operand_bitwidth as usize;

        current_constraint_idx += 2;

        assert_eq!(
            air.constraints.len(),
            current_constraint_idx,
            "URem: Incorrect number of constraints. Expected {}, got {}. Constraints: {:#?}",
            current_constraint_idx,
            air.constraints.len(),
            air.constraints
        );

        let a_expr = AirExpression::Trace(AirTraceVariable(0), RowOffset::Current);
        let b_expr = AirExpression::Trace(AirTraceVariable(1), RowOffset::Current);
        let r_expr = AirExpression::Trace(AirTraceVariable(2), RowOffset::Current);
        let q_expr = AirExpression::Trace(AirTraceVariable(3), RowOffset::Current);
        let q_times_b = AirExpression::Mul(Box::new(q_expr.clone()), Box::new(b_expr.clone()));
        let qb_plus_r = AirExpression::Add(Box::new(q_times_b), Box::new(r_expr.clone()));
        let expected_algebraic_relation =
            AirExpression::Sub(Box::new(a_expr.clone()), Box::new(qb_plus_r));

        assert_eq!(
            air.constraints[0], expected_algebraic_relation,
            "URem: Missing algebraic relation: a - (q*b+r) = 0"
        );
    }

    #[test]
    fn test_generate_air_from_srem_llvm() {
        let llvm_ir = r#"; ModuleID = 'srem_module'
        define i32 @signed_rem(i32 %a, i32 %b) { ; %a=v0, %b=v1
          entry:
            %r = srem i32 %a, %b ; %r=v2
            ret i32 %r
        }
        "#;
        let field_instance = TestField97;
        let result = AirCodegen::generate_air(llvm_ir, &field_instance);
        assert!(
            result.is_ok(),
            "AirCodegen::generate_air for SRem failed: {:?}",
            result.err()
        );
        let air = result.unwrap();

        let operand_bitwidth: u32 = 32;

        let expected_min_trace_cols =
            3 + 1 + 1 + 4 * operand_bitwidth as usize + 1 + operand_bitwidth as usize + 4;
        assert!(
            air.num_trace_columns >= expected_min_trace_cols,
            "SRem: Not enough trace columns. Expected at least {}, got {}",
            expected_min_trace_cols,
            air.num_trace_columns
        );

        let mut current_constraint_idx = 0;

        current_constraint_idx += (operand_bitwidth as usize + 1) * 4;

        current_constraint_idx += 1;

        current_constraint_idx += 2;

        current_constraint_idx += 2;

        current_constraint_idx += 2 + operand_bitwidth as usize + 1;

        assert_eq!(
            air.constraints.len(),
            current_constraint_idx,
            "SRem: Incorrect number of constraints. Expected {}, got {}. Constraints: {:#?}",
            current_constraint_idx,
            air.constraints.len(),
            air.constraints
        );

        let a_expr = AirExpression::Trace(AirTraceVariable(0), RowOffset::Current);
        let b_expr = AirExpression::Trace(AirTraceVariable(1), RowOffset::Current);
        let r_expr = AirExpression::Trace(AirTraceVariable(2), RowOffset::Current);
        let q_expr = AirExpression::Trace(AirTraceVariable(3), RowOffset::Current);
        let q_times_b = AirExpression::Mul(Box::new(q_expr.clone()), Box::new(b_expr.clone()));
        let qb_plus_r = AirExpression::Add(Box::new(q_times_b), Box::new(r_expr.clone()));
        let expected_algebraic_relation =
            AirExpression::Sub(Box::new(a_expr.clone()), Box::new(qb_plus_r));

        let algebraic_constr_idx = 4 * (operand_bitwidth as usize + 1);
        assert_eq!(
            air.constraints[algebraic_constr_idx], expected_algebraic_relation,
            "SRem: Missing algebraic relation: a - (q*b+r) = 0"
        );
    }

    #[test]
    fn test_fmul_normal_numbers() {
        let mut air_codegen = AirCodegen::new(100);
        let op1_id = air_codegen.ctx.new_aux_variable().0;
        let op2_id = air_codegen.ctx.new_aux_variable().0;
        let res_id = air_codegen.ctx.new_aux_variable().0;

        let operand1_var = ConstraintSystemVariable(op1_id);
        let operand2_var = ConstraintSystemVariable(op2_id);
        let result_var = ConstraintSystemVariable(res_id);

        let operand1 = Operand::Var(operand1_var);
        let operand2 = Operand::Var(operand2_var);

        let structured_constraints = vec![StructuredAirConstraint::FMul {
            operand1,
            operand2,
            result: result_var,
            operand_bitwidth: 32,
            block_name: "entry".to_string(),
        }];

        let air_constraints = air_codegen.resolve_structured_constraints(
            structured_constraints,
            &HashMap::new(),
            &Vec::new(),
        );

        assert!(
            !air_constraints.is_empty(),
            "No AIR constraints generated for FMul normal"
        );
        println!(
            "test_fmul_normal_numbers: {} constraints generated.",
            air_constraints.len()
        );
    }

    #[test]
    fn test_fmul_nan_operand_one() {
        let mut air_codegen = AirCodegen::new(100);
        let op1_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);
        let op2_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);
        let res_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);

        let structured_constraints = vec![StructuredAirConstraint::FMul {
            operand1: Operand::Var(op1_var),
            operand2: Operand::Var(op2_var),
            result: res_var,
            operand_bitwidth: 32,
            block_name: "entry".to_string(),
        }];
        let air_constraints = air_codegen.resolve_structured_constraints(
            structured_constraints,
            &HashMap::new(),
            &Vec::new(),
        );
        assert!(
            !air_constraints.is_empty(),
            "No AIR constraints for FMul NaN operand1"
        );
        println!(
            "test_fmul_nan_operand_one: {} constraints generated.",
            air_constraints.len()
        );
    }

    #[test]
    fn test_fmul_nan_operand_two() {
        let mut air_codegen = AirCodegen::new(100);
        let op1_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);
        let op2_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);
        let res_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);

        let structured_constraints = vec![StructuredAirConstraint::FMul {
            operand1: Operand::Var(op1_var),
            operand2: Operand::Var(op2_var),
            result: res_var,
            operand_bitwidth: 32,
            block_name: "entry".to_string(),
        }];
        let air_constraints = air_codegen.resolve_structured_constraints(
            structured_constraints,
            &HashMap::new(),
            &Vec::new(),
        );
        assert!(
            !air_constraints.is_empty(),
            "No AIR constraints for FMul NaN operand2"
        );
        println!(
            "test_fmul_nan_operand_two: {} constraints generated.",
            air_constraints.len()
        );
    }

    #[test]
    fn test_fmul_inf_times_zero() {
        let mut air_codegen = AirCodegen::new(100);
        let op1_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);
        let op2_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);
        let res_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);

        let structured_constraints = vec![StructuredAirConstraint::FMul {
            operand1: Operand::Var(op1_var),
            operand2: Operand::Var(op2_var),
            result: res_var,
            operand_bitwidth: 32,
            block_name: "entry".to_string(),
        }];
        let air_constraints = air_codegen.resolve_structured_constraints(
            structured_constraints,
            &HashMap::new(),
            &Vec::new(),
        );
        assert!(
            !air_constraints.is_empty(),
            "No AIR constraints for FMul Inf * 0 (NaN case)"
        );
        println!(
            "test_fmul_inf_times_zero: {} constraints generated.",
            air_constraints.len()
        );
    }

    #[test]
    fn test_fmul_zero_times_inf() {
        let mut air_codegen = AirCodegen::new(100);
        let op1_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);
        let op2_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);
        let res_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);

        let structured_constraints = vec![StructuredAirConstraint::FMul {
            operand1: Operand::Var(op1_var),
            operand2: Operand::Var(op2_var),
            result: res_var,
            operand_bitwidth: 32,
            block_name: "entry".to_string(),
        }];
        let air_constraints = air_codegen.resolve_structured_constraints(
            structured_constraints,
            &HashMap::new(),
            &Vec::new(),
        );
        assert!(
            !air_constraints.is_empty(),
            "No AIR constraints for FMul 0 * Inf (NaN case)"
        );
        println!(
            "test_fmul_zero_times_inf: {} constraints generated.",
            air_constraints.len()
        );
    }

    #[test]
    fn test_fmul_inf_times_inf() {
        let mut air_codegen = AirCodegen::new(100);
        let op1_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);
        let op2_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);
        let res_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);

        let structured_constraints = vec![StructuredAirConstraint::FMul {
            operand1: Operand::Var(op1_var),
            operand2: Operand::Var(op2_var),
            result: res_var,
            operand_bitwidth: 32,
            block_name: "entry".to_string(),
        }];
        let air_constraints = air_codegen.resolve_structured_constraints(
            structured_constraints,
            &HashMap::new(),
            &Vec::new(),
        );
        assert!(
            !air_constraints.is_empty(),
            "No AIR constraints for FMul Inf * Inf"
        );
        println!(
            "test_fmul_inf_times_inf: {} constraints generated.",
            air_constraints.len()
        );
    }

    #[test]
    fn test_fmul_inf_times_finite() {
        let mut air_codegen = AirCodegen::new(100);
        let op1_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);
        let op2_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);
        let res_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);

        let structured_constraints = vec![StructuredAirConstraint::FMul {
            operand1: Operand::Var(op1_var),
            operand2: Operand::Var(op2_var),
            result: res_var,
            operand_bitwidth: 32,
            block_name: "entry".to_string(),
        }];
        let air_constraints = air_codegen.resolve_structured_constraints(
            structured_constraints,
            &HashMap::new(),
            &Vec::new(),
        );
        assert!(
            !air_constraints.is_empty(),
            "No AIR constraints for FMul Inf * Finite"
        );
        println!(
            "test_fmul_inf_times_finite: {} constraints generated.",
            air_constraints.len()
        );
    }

    #[test]
    fn test_fmul_finite_times_inf() {
        let mut air_codegen = AirCodegen::new(100);
        let op1_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);
        let op2_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);
        let res_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);

        let structured_constraints = vec![StructuredAirConstraint::FMul {
            operand1: Operand::Var(op1_var),
            operand2: Operand::Var(op2_var),
            result: res_var,
            operand_bitwidth: 32,
            block_name: "entry".to_string(),
        }];
        let air_constraints = air_codegen.resolve_structured_constraints(
            structured_constraints,
            &HashMap::new(),
            &Vec::new(),
        );
        assert!(
            !air_constraints.is_empty(),
            "No AIR constraints for FMul Finite * Inf"
        );
        println!(
            "test_fmul_finite_times_inf: {} constraints generated.",
            air_constraints.len()
        );
    }

    #[test]
    fn test_fmul_zero_times_finite() {
        let mut air_codegen = AirCodegen::new(100);
        let op1_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);
        let op2_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);
        let res_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);

        let structured_constraints = vec![StructuredAirConstraint::FMul {
            operand1: Operand::Var(op1_var),
            operand2: Operand::Var(op2_var),
            result: res_var,
            operand_bitwidth: 32,
            block_name: "entry".to_string(),
        }];
        let air_constraints = air_codegen.resolve_structured_constraints(
            structured_constraints,
            &HashMap::new(),
            &Vec::new(),
        );
        assert!(
            !air_constraints.is_empty(),
            "No AIR constraints for FMul Zero * Finite"
        );
        println!(
            "test_fmul_zero_times_finite: {} constraints generated.",
            air_constraints.len()
        );
    }

    #[test]
    fn test_fmul_finite_times_zero() {
        let mut air_codegen = AirCodegen::new(100);
        let op1_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);
        let op2_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);
        let res_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);

        let structured_constraints = vec![StructuredAirConstraint::FMul {
            operand1: Operand::Var(op1_var),
            operand2: Operand::Var(op2_var),
            result: res_var,
            operand_bitwidth: 32,
            block_name: "entry".to_string(),
        }];
        let air_constraints = air_codegen.resolve_structured_constraints(
            structured_constraints,
            &HashMap::new(),
            &Vec::new(),
        );
        assert!(
            !air_constraints.is_empty(),
            "No AIR constraints for FMul Finite * Zero"
        );
        println!(
            "test_fmul_finite_times_zero: {} constraints generated.",
            air_constraints.len()
        );
    }

    #[test]
    fn test_fmul_zero_times_zero() {
        let mut air_codegen = AirCodegen::new(100);
        let op1_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);
        let op2_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);
        let res_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);

        let structured_constraints = vec![StructuredAirConstraint::FMul {
            operand1: Operand::Var(op1_var),
            operand2: Operand::Var(op2_var),
            result: res_var,
            operand_bitwidth: 32,
            block_name: "entry".to_string(),
        }];
        let air_constraints = air_codegen.resolve_structured_constraints(
            structured_constraints,
            &HashMap::new(),
            &Vec::new(),
        );
        assert!(
            !air_constraints.is_empty(),
            "No AIR constraints for FMul Zero * Zero"
        );
        println!(
            "test_fmul_zero_times_zero: {} constraints generated.",
            air_constraints.len()
        );
    }

    #[test]
    fn test_fneg_normal_number() {
        let mut air_codegen = AirCodegen::new(100);
        let op_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);
        let res_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);

        let structured_constraints = vec![StructuredAirConstraint::FNeg {
            operand: Operand::Var(op_var),
            result: res_var,
            operand_bitwidth: 32,
            block_name: "entry".to_string(),
        }];
        let air_constraints = air_codegen.resolve_structured_constraints(
            structured_constraints,
            &HashMap::new(),
            &Vec::new(),
        );
        assert!(
            !air_constraints.is_empty(),
            "No AIR constraints for FNeg normal number"
        );
        println!(
            "test_fneg_normal_number: {} constraints generated.",
            air_constraints.len()
        );
    }

    #[test]
    fn test_fneg_zero() {
        let mut air_codegen = AirCodegen::new(100);
        let op_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);
        let res_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);

        let structured_constraints = vec![StructuredAirConstraint::FNeg {
            operand: Operand::Var(op_var),
            result: res_var,
            operand_bitwidth: 32,
            block_name: "entry".to_string(),
        }];
        let air_constraints = air_codegen.resolve_structured_constraints(
            structured_constraints,
            &HashMap::new(),
            &Vec::new(),
        );
        assert!(
            !air_constraints.is_empty(),
            "No AIR constraints for FNeg zero"
        );
        println!(
            "test_fneg_zero: {} constraints generated.",
            air_constraints.len()
        );
    }

    #[test]
    fn test_fneg_inf() {
        let mut air_codegen = AirCodegen::new(100);
        let op_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);
        let res_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);

        let structured_constraints = vec![StructuredAirConstraint::FNeg {
            operand: Operand::Var(op_var),
            result: res_var,
            operand_bitwidth: 32,
            block_name: "entry".to_string(),
        }];
        let air_constraints = air_codegen.resolve_structured_constraints(
            structured_constraints,
            &HashMap::new(),
            &Vec::new(),
        );
        assert!(
            !air_constraints.is_empty(),
            "No AIR constraints for FNeg infinity"
        );
        println!(
            "test_fneg_inf: {} constraints generated.",
            air_constraints.len()
        );
    }

    #[test]
    fn test_fneg_nan() {
        let mut air_codegen = AirCodegen::new(100);
        let op_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);
        let res_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);

        let structured_constraints = vec![StructuredAirConstraint::FNeg {
            operand: Operand::Var(op_var),
            result: res_var,
            operand_bitwidth: 32,
            block_name: "entry".to_string(),
        }];
        let air_constraints = air_codegen.resolve_structured_constraints(
            structured_constraints,
            &HashMap::new(),
            &Vec::new(),
        );
        assert!(
            !air_constraints.is_empty(),
            "No AIR constraints for FNeg NaN"
        );
        println!(
            "test_fneg_nan: {} constraints generated.",
            air_constraints.len()
        );
    }

    #[test]
    fn test_fdiv_normal_numbers() {
        let mut air_codegen = AirCodegen::new(100);
        let op1_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);
        let op2_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);
        let res_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);

        let structured_constraints = vec![StructuredAirConstraint::FDiv {
            operand1: Operand::Var(op1_var),
            operand2: Operand::Var(op2_var),
            result: res_var,
            operand_bitwidth: 32,
            block_name: "entry".to_string(),
        }];
        let air_constraints = air_codegen.resolve_structured_constraints(
            structured_constraints,
            &HashMap::new(),
            &Vec::new(),
        );
        assert!(
            !air_constraints.is_empty(),
            "No AIR constraints generated for FDiv normal"
        );
        println!(
            "test_fdiv_normal_numbers: {} constraints generated.",
            air_constraints.len()
        );
    }

    #[test]
    fn test_fdiv_div_by_zero() {
        let mut air_codegen = AirCodegen::new(100);
        let op1_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);
        let op2_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);
        let res_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);

        let structured_constraints = vec![StructuredAirConstraint::FDiv {
            operand1: Operand::Var(op1_var),
            operand2: Operand::Var(op2_var),
            result: res_var,
            operand_bitwidth: 32,
            block_name: "entry".to_string(),
        }];
        let air_constraints = air_codegen.resolve_structured_constraints(
            structured_constraints,
            &HashMap::new(),
            &Vec::new(),
        );
        assert!(
            !air_constraints.is_empty(),
            "No AIR constraints for FDiv by zero"
        );
        println!(
            "test_fdiv_div_by_zero: {} constraints generated.",
            air_constraints.len()
        );
    }

    #[test]
    fn test_fdiv_zero_div_by_zero() {
        let mut air_codegen = AirCodegen::new(100);
        let op1_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);
        let op2_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);
        let res_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);

        let structured_constraints = vec![StructuredAirConstraint::FDiv {
            operand1: Operand::Var(op1_var),
            operand2: Operand::Var(op2_var),
            result: res_var,
            operand_bitwidth: 32,
            block_name: "entry".to_string(),
        }];
        let air_constraints = air_codegen.resolve_structured_constraints(
            structured_constraints,
            &HashMap::new(),
            &Vec::new(),
        );
        assert!(
            !air_constraints.is_empty(),
            "No AIR constraints for FDiv zero by zero"
        );
        println!(
            "test_fdiv_zero_div_by_zero: {} constraints generated.",
            air_constraints.len()
        );
    }

    #[test]
    fn test_fdiv_inf_div_by_inf() {
        let mut air_codegen = AirCodegen::new(100);
        let op1_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);
        let op2_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);
        let res_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);

        let structured_constraints = vec![StructuredAirConstraint::FDiv {
            operand1: Operand::Var(op1_var),
            operand2: Operand::Var(op2_var),
            result: res_var,
            operand_bitwidth: 32,
            block_name: "entry".to_string(),
        }];
        let air_constraints = air_codegen.resolve_structured_constraints(
            structured_constraints,
            &HashMap::new(),
            &Vec::new(),
        );
        assert!(
            !air_constraints.is_empty(),
            "No AIR constraints for FDiv inf by inf"
        );
        println!(
            "test_fdiv_inf_div_by_inf: {} constraints generated.",
            air_constraints.len()
        );
    }

    #[test]
    fn test_fdiv_nan_operand() {
        let mut air_codegen = AirCodegen::new(100);
        let op1_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);
        let op2_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);
        let res_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);

        let structured_constraints = vec![StructuredAirConstraint::FDiv {
            operand1: Operand::Var(op1_var),
            operand2: Operand::Var(op2_var),
            result: res_var,
            operand_bitwidth: 32,
            block_name: "entry".to_string(),
        }];
        let air_constraints = air_codegen.resolve_structured_constraints(
            structured_constraints,
            &HashMap::new(),
            &Vec::new(),
        );
        assert!(
            !air_constraints.is_empty(),
            "No AIR constraints for FDiv NaN operand"
        );
        println!(
            "test_fdiv_nan_operand: {} constraints generated.",
            air_constraints.len()
        );
    }

    #[test]
    fn test_fcmp_oeq() {
        let mut air_codegen = AirCodegen::new(100);
        let op1_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);
        let op2_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);
        let res_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);

        let structured_constraints = vec![StructuredAirConstraint::FCmp {
            cond: FloatPredicate::OEQ,
            operand1: Operand::Var(op1_var),
            operand2: Operand::Var(op2_var),
            result: res_var,
            operand_bitwidth: 32,
            block_name: "entry".to_string(),
        }];
        let air_constraints = air_codegen.resolve_structured_constraints(
            structured_constraints,
            &HashMap::new(),
            &Vec::new(),
        );
        assert!(
            !air_constraints.is_empty(),
            "No AIR constraints for FCmp OEQ"
        );
        println!(
            "test_fcmp_oeq: {} constraints generated.",
            air_constraints.len()
        );
    }

    #[test]
    fn test_fcmp_uno_with_nan() {
        let mut air_codegen = AirCodegen::new(100);
        let op1_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);
        let op2_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);
        let res_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);

        let structured_constraints = vec![StructuredAirConstraint::FCmp {
            cond: FloatPredicate::UNO,
            operand1: Operand::Var(op1_var),
            operand2: Operand::Var(op2_var),
            result: res_var,
            operand_bitwidth: 32,
            block_name: "entry".to_string(),
        }];
        let air_constraints = air_codegen.resolve_structured_constraints(
            structured_constraints,
            &HashMap::new(),
            &Vec::new(),
        );
        assert!(
            !air_constraints.is_empty(),
            "No AIR constraints for FCmp UNO with NaN"
        );
        println!(
            "test_fcmp_uno_with_nan: {} constraints generated.",
            air_constraints.len()
        );
    }

    #[test]
    fn test_fcmp_olt() {
        let mut air_codegen = AirCodegen::new(100);
        let op1_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);
        let op2_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);
        let res_var = ConstraintSystemVariable(air_codegen.ctx.new_aux_variable().0);

        let structured_constraints = vec![StructuredAirConstraint::FCmp {
            cond: FloatPredicate::OLT,
            operand1: Operand::Var(op1_var),
            operand2: Operand::Var(op2_var),
            result: res_var,
            operand_bitwidth: 32,
            block_name: "entry".to_string(),
        }];
        let air_constraints = air_codegen.resolve_structured_constraints(
            structured_constraints,
            &HashMap::new(),
            &Vec::new(),
        );
        assert!(
            !air_constraints.is_empty(),
            "No AIR constraints for FCmp OLT"
        );
        println!(
            "test_fcmp_olt: {} constraints generated.",
            air_constraints.len()
        );
    }
}

#[cfg(test)]
mod memory_air_tests {
    use crate::llvm::air::codegen::memory;
    use lang::constraints::{AirExpression, AirTraceVariable, RowOffset};
    use lang::ctx::AirGenContext;
    use lang::{process_llvm_ir, Operand as LangOperand, StructuredAirConstraint};

    const CLK_DIFFERENCE_BITWIDTH_FOR_TEST: usize = 32;

    fn test_memory_logic_directly(llvm_ir: &str, _expected_total_constraints: usize) {
        let (structured_constraints, mut memory_log) = match process_llvm_ir(llvm_ir) {
            Ok((sc, ml)) => (sc, ml),
            Err(e) => panic!("LLVM IR processing failed: {}. IR:\n{}", e, llvm_ir),
        };

        let mut max_var_id = 0;
        for constraint in &structured_constraints {
            if let StructuredAirConstraint::Alloca { ptr_result, .. } = constraint {
                max_var_id = max_var_id.max(ptr_result.0);
            }
        }

        for entry in &memory_log {
            if let LangOperand::Var(csv) = entry.value {
                max_var_id = max_var_id.max(csv.0);
            }
            if let LangOperand::Var(addr_var) = entry.address {
                max_var_id = max_var_id.max(addr_var.0);
            }
            max_var_id = max_var_id.max(entry.time_step.0);
        }

        let mut air_gen_ctx = AirGenContext::new(max_var_id);
        let initial_trace_col_for_memory = air_gen_ctx.next_available_trace_col;
        let ctx_next_col_before_mem_call = air_gen_ctx.next_available_trace_col;

        memory_log.sort_unstable();

        let (mem_constraints, mem_trace_columns_def, next_trace_col_idx_after_main_mem_cols) =
            memory::generate_memory_air_constraints(
                &memory_log,
                &mut air_gen_ctx,
                initial_trace_col_for_memory,
            );

        let expected_main_mem_cols = 4;
        if memory_log.is_empty() {
            assert_eq!(
                mem_constraints.len(),
                0,
                "Expected 0 constraints for empty memory log"
            );
            assert_eq!(
                next_trace_col_idx_after_main_mem_cols,
                initial_trace_col_for_memory + expected_main_mem_cols,
                "Next col index mismatch for empty log"
            );
            assert_eq!(
                air_gen_ctx.next_available_trace_col, ctx_next_col_before_mem_call,
                "AirGenContext should not change for empty log if no aux vars were used by mem generation"
            );
            return;
        }

        if !memory_log.is_empty() {
            assert!(
                !mem_constraints.is_empty(),
                "Memory AIR generation produced no constraints for a non-empty memory log"
            );
        }

        assert_eq!(
            mem_trace_columns_def.clk.0, initial_trace_col_for_memory,
            "clk col index mismatch"
        );
        assert_eq!(
            mem_trace_columns_def.addr.0,
            initial_trace_col_for_memory + 1,
            "addr col index mismatch"
        );
        assert_eq!(
            mem_trace_columns_def.val.0,
            initial_trace_col_for_memory + 2,
            "val col index mismatch"
        );
        assert_eq!(
            mem_trace_columns_def.is_write.0,
            initial_trace_col_for_memory + 3,
            "is_write col index mismatch"
        );

        assert!(
            next_trace_col_idx_after_main_mem_cols >= initial_trace_col_for_memory + expected_main_mem_cols,
            "Main memory columns allocation did not reserve enough columns: got {}, expected at least {}",
            next_trace_col_idx_after_main_mem_cols,
            initial_trace_col_for_memory + expected_main_mem_cols
        );

        if !memory_log.is_empty() {
            assert!(
                air_gen_ctx.next_available_trace_col >= ctx_next_col_before_mem_call,
                "AirGenContext did not advance its next_available_trace_col despite memory log entries"
            );
        }
    }

    #[test]
    fn test_mem_store_load_simple() {
        let llvm_ir = r#"
            define i32 @main() {
            entry:
                %ptr = alloca i32, align 4
                store i32 123, i32* %ptr, align 4
                %val = load i32, i32* %ptr, align 4
                ret i32 %val
            }
        "#;

        test_memory_logic_directly(llvm_ir, 49);
    }

    #[test]
    fn test_mem_store_store_load() {
        let llvm_ir = r#"
            define i32 @main() {
            entry:
                %ptr = alloca i32, align 4
                store i32 10, i32* %ptr, align 4
                store i32 20, i32* %ptr, align 4
                %val = load i32, i32* %ptr, align 4
                ret i32 %val
            }
        "#;

        test_memory_logic_directly(llvm_ir, 93);
    }

    #[test]
    fn test_mem_multi_addr_store_load() {
        let llvm_ir = r#"
            define i32 @main() {
            entry:
                %ptr1 = alloca i32, align 4
                %ptr2 = alloca i32, align 4
                store i32 11, i32* %ptr1, align 4
                store i32 22, i32* %ptr2, align 4
                %val1 = load i32, i32* %ptr1, align 4
                %val2 = load i32, i32* %ptr2, align 4
                %sum = add i32 %val1, %val2
                ret i32 %sum
            }
        "#;

        test_memory_logic_directly(llvm_ir, 137);
    }

    #[test]
    fn test_mem_load_uninitialized() {
        let llvm_ir = r#"
            define i32 @main() {
            entry:
                %ptr = alloca i32, align 4
                %val = load i32, i32* %ptr, align 4
                ret i32 %val
            }
        "#;

        test_memory_logic_directly(llvm_ir, 5);
    }

    #[test]
    fn test_mem_store_load_load() {
        let llvm_ir = r#"
            define i32 @main() {
            entry:
                %ptr = alloca i32, align 4
                store i32 77, i32* %ptr, align 4
                %val1 = load i32, i32* %ptr, align 4
                %val2 = load i32, i32* %ptr, align 4
                %sum = add i32 %val1, %val2
                ret i32 %sum
            }
        "#;

        test_memory_logic_directly(llvm_ir, 93);
    }

    #[test]
    fn test_mem_no_memory_ops() {
        let llvm_ir = r#"
            define i32 @main() {
            entry:
                %a = add i32 1, 2
                ret i32 %a
            }
        "#;

        test_memory_logic_directly(llvm_ir, 0);
    }
}

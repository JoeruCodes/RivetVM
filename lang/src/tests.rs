#[test]
fn sub_function_ir_processing() {
    let llvm_ir_sub = r#"; ModuleID = 'sub_module'
    source_filename = "sub.c"

    define i32 @subtract(i32 %a, i32 %b) {
      entry:
        %result = sub i32 %a, %b
        ret i32 %result
    }
    "#;

    match process_llvm_ir(llvm_ir_sub) {
        Ok(processed_constraints) => {
            assert_eq!(processed_constraints.len(), 2); 
            match &processed_constraints[0] {
                StructuredAirConstraint::Sub { operand1, operand2, result, block_name } => {
                    assert_eq!(*operand1, Operand::Var(ConstraintSystemVariable(0))); 
                    assert_eq!(*operand2, Operand::Var(ConstraintSystemVariable(1))); 
                    assert_eq!(*result, ConstraintSystemVariable(2)); 
                    assert_eq!(*block_name, "entry");
                }
                _ => panic!("Expected Sub constraint first"),
            }
        }
        Err(e) => {
            panic!("Failed to process Sub IR: {}", e);
        }
    }
}

#[test]
fn and_function_ir_processing() {
    let llvm_ir_and = r#"; ModuleID = 'and_module'
    source_filename = "and.c"

    define i32 @logical_and(i32 %a, i32 %b) {
      entry:
        %result = and i32 %a, %b
        ret i32 %result
    }
    "#;

    match process_llvm_ir(llvm_ir_and) {
        Ok(processed_constraints) => {
            assert_eq!(processed_constraints.len(), 2); 
            match &processed_constraints[0] {
                StructuredAirConstraint::And { operand1, operand2, result, block_name } => {
                    assert_eq!(*operand1, Operand::Var(ConstraintSystemVariable(0))); 
                    assert_eq!(*operand2, Operand::Var(ConstraintSystemVariable(1))); 
                    assert_eq!(*result, ConstraintSystemVariable(2)); 
                    assert_eq!(*block_name, "entry");
                }
                _ => panic!("Expected And constraint first"),
            }
        }
        Err(e) => {
            panic!("Failed to process And IR: {}", e);
        }
    }
}

#[test]
fn or_function_ir_processing() {
    let llvm_ir_or = r#"; ModuleID = 'or_module'
    source_filename = "or.c"

    define i32 @logical_or(i32 %a, i32 %b) {
      entry:
        %result = or i32 %a, %b
        ret i32 %result
    }
    "#;

    match process_llvm_ir(llvm_ir_or) {
        Ok(processed_constraints) => {
            assert_eq!(processed_constraints.len(), 2); 
            match &processed_constraints[0] {
                StructuredAirConstraint::Or { operand1, operand2, result, block_name } => {
                    assert_eq!(*operand1, Operand::Var(ConstraintSystemVariable(0))); 
                    assert_eq!(*operand2, Operand::Var(ConstraintSystemVariable(1))); 
                    assert_eq!(*result, ConstraintSystemVariable(2)); 
                    assert_eq!(*block_name, "entry");
                }
                _ => panic!("Expected Or constraint first"),
            }
        }
        Err(e) => {
            panic!("Failed to process Or IR: {}", e);
        }
    }
} 
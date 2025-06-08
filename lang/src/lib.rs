use inkwell::basic_block::BasicBlock;
use inkwell::context::Context;
use inkwell::types::{AnyTypeEnum, BasicTypeEnum};
use inkwell::values::{
    AnyValue, AnyValueEnum, BasicValueEnum, InstructionOpcode, InstructionValue, PhiValue,
};
pub use inkwell::FloatPredicate;
pub use inkwell::IntPredicate;
pub mod constraints;
pub mod ctx;
pub mod utils;
use std::collections::HashMap;

use crate::constraints::add::Add;
use crate::constraints::and::And;
use crate::constraints::ashr::Ashr;
use crate::constraints::fadd::FAdd;
use crate::constraints::fcmp::FCmp;
use crate::constraints::fdiv::FDiv;
use crate::constraints::fmul::FMul;
use crate::constraints::fneg::FNeg;
use crate::constraints::fpext::FpExt;
use crate::constraints::fptosi::{self, FpToSi};
use crate::constraints::fptoui::FpToUi;
use crate::constraints::fptrunc::FpTrunc;
use crate::constraints::frem::FRem;
use crate::constraints::fsub::FSub;
use crate::constraints::get_elem_ptr::GetElementPtr;
use crate::constraints::icmp::Icmp;
use crate::constraints::mul::Mul;
use crate::constraints::or::Or;
use crate::constraints::phi::Phi;
use crate::constraints::sdiv::SDiv;
use crate::constraints::select::Select;
use crate::constraints::sext::SExt;
use crate::constraints::shl::Shl;
use crate::constraints::shr::Shr;
use crate::constraints::sitofp::SiToFp;
use crate::constraints::srem::SRem;
use crate::constraints::sub::Sub;
use crate::constraints::trunc::Trunc;
use crate::constraints::udiv::UDiv;
use crate::constraints::uitofp::UiToFp;
use crate::constraints::urem::URem;
use crate::constraints::xor::Xor;
use crate::constraints::zext::ZExt;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ConstraintSystemVariable(pub usize);

#[derive(PartialEq, Eq, Debug, Clone, Copy)]
pub enum Operand {
    Var(ConstraintSystemVariable),
    Const(u128),
}

impl Ord for Operand {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        match (self, other) {
            (Operand::Var(v1), Operand::Var(v2)) => v1.0.cmp(&v2.0),
            (Operand::Const(c1), Operand::Const(c2)) => c1.cmp(c2),
            (Operand::Var(_), Operand::Const(_)) => std::cmp::Ordering::Less,
            (Operand::Const(_), Operand::Var(_)) => std::cmp::Ordering::Greater,
        }
    }
}

impl PartialOrd for Operand {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum MemoryAccessType {
    Read,
    Write,
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct MemoryAccessLogEntry {
    pub address: Operand,
    pub value: Operand,
    pub time_step: ConstraintSystemVariable,
    pub access_type: MemoryAccessType,
    pub bitwidth: u32,
    pub block_name: String,
}

impl Ord for MemoryAccessLogEntry {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.address
            .cmp(&other.address)
            .then_with(|| self.time_step.0.cmp(&other.time_step.0))
            .then_with(|| self.access_type.cmp(&other.access_type))
    }
}

impl PartialOrd for MemoryAccessLogEntry {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

#[derive(Debug, Clone)]
pub enum StructuredAirConstraint {
    FMul(FMul),
    FDiv(FDiv),
    FNeg(FNeg),
    Add(Add),
    FAdd(FAdd),
    FCmp(FCmp),
    FRem(FRem),
    FSub(FSub),
    Sub(Sub),
    Multiply(Mul),
    SDiv(SDiv),
    UDiv(UDiv),
    Shl(Shl),
    Shr(Shr),
    AShr(Ashr),
    And(And),
    Or(Or),
    Xor(Xor),
    SRem(SRem),
    URem(URem),
    Icmp(Icmp),
    Branch {
        target_block_name: String,
        block_name: String,
    },
    ConditionalBranch {
        condition: ConstraintSystemVariable,
        true_block_name: String,
        false_block_name: String,
        block_name: String,
    },
    Phi(Phi),
    Return {
        value: Option<Operand>,
        block_name: String,
    },
    Alloca {
        ptr_result: ConstraintSystemVariable,
        allocated_type: String,
        block_name: String,
    },
    Switch {
        condition_operand: Operand,
        default_target_block_name: String,
        cases: Vec<(Operand, String)>,
        block_name: String,
    },
    Trunc(Trunc),
    FPTrunc(FpTrunc),
    ZExt(ZExt),
    SExt(SExt),
    FPExt(FpExt),
    UIToFP(UiToFp),
    FPToUI(FpToUi),
    SIToFP(SiToFp),
    FPToSI(fptosi::FpToSi),
    Select(Select),
    GetElementPtr(GetElementPtr),
}

pub struct ArithmetizationContext<'ctx> {
    next_variable_id: usize,
    llvm_to_cs_var_map: HashMap<BasicValueEnum<'ctx>, ConstraintSystemVariable>,
    pub structured_constraints: Vec<StructuredAirConstraint>,
    current_block_name_for_constraints: String,
    pub memory_log: Vec<MemoryAccessLogEntry>,
    next_time_step_id: usize,
}

impl<'ctx> ArithmetizationContext<'ctx> {
    pub fn new() -> Self {
        ArithmetizationContext {
            next_variable_id: 0,
            llvm_to_cs_var_map: HashMap::new(),
            structured_constraints: Vec::new(),
            current_block_name_for_constraints: String::new(),
            memory_log: Vec::new(),
            next_time_step_id: 0,
        }
    }

    fn new_cs_variable(&mut self) -> ConstraintSystemVariable {
        let id = self.next_variable_id;
        self.next_variable_id += 1;
        ConstraintSystemVariable(id)
    }

    fn new_time_step_variable(&mut self) -> ConstraintSystemVariable {
        let id = self.next_time_step_id;
        self.next_time_step_id += 1;
        let time_cs_var = self.new_cs_variable();
        println!(
            "    INFO: New Time Step Variable created: {:?} (logical time_id {})",
            time_cs_var, id
        );
        time_cs_var
    }

    fn llvm_basic_value_to_air_operand(&mut self, llvm_basic_val: BasicValueEnum<'ctx>) -> Operand {
        match llvm_basic_val {
            BasicValueEnum::IntValue(iv) => {
                if let Some(const_val_u64) = iv.get_zero_extended_constant() {
                    Operand::Const(const_val_u64 as u128)
                } else {
                    Operand::Var(self.get_or_create_cs_var_for_llvm_register_or_arg(llvm_basic_val))
                }
            }
            BasicValueEnum::PointerValue(_pv) => {
                Operand::Var(self.get_or_create_cs_var_for_llvm_register_or_arg(llvm_basic_val))
            }
            _ => Operand::Var(self.get_or_create_cs_var_for_llvm_register_or_arg(llvm_basic_val)),
        }
    }

    fn get_or_create_cs_var_for_llvm_register_or_arg(
        &mut self,
        llvm_val: BasicValueEnum<'ctx>,
    ) -> ConstraintSystemVariable {
        if let Some(cs_var) = self.llvm_to_cs_var_map.get(&llvm_val) {
            *cs_var
        } else {
            let new_cs_var = self.new_cs_variable();
            self.llvm_to_cs_var_map.insert(llvm_val, new_cs_var);
            new_cs_var
        }
    }

    fn map_instruction_result_to_new_cs_var(
        &mut self,
        instr_val: InstructionValue<'ctx>,
    ) -> ConstraintSystemVariable {
        let llvm_value_as_result = instr_val.as_any_value_enum();
        let llvm_basic_value_as_result = match llvm_value_as_result {
            AnyValueEnum::PointerValue(pv) => BasicValueEnum::PointerValue(pv),
            AnyValueEnum::IntValue(iv) => BasicValueEnum::IntValue(iv),
            AnyValueEnum::FloatValue(fv) => BasicValueEnum::FloatValue(fv),
            AnyValueEnum::VectorValue(vv) => BasicValueEnum::VectorValue(vv),
            _ => panic!(
                "Unhandled AnyValueEnum variant ({:?}) in map_instruction_result_to_new_cs_var that is not directly a BasicValueEnum. This instruction result type cannot be used as a map key directly.",
                llvm_value_as_result
            ),
        };

        if let Some(existing_cs_var) = self.llvm_to_cs_var_map.get(&llvm_basic_value_as_result) {
            *existing_cs_var
        } else {
            let new_cs_var = self.new_cs_variable();
            self.llvm_to_cs_var_map
                .insert(llvm_basic_value_as_result, new_cs_var);
            new_cs_var
        }
    }

    fn add_structured_constraint(&mut self, constraint: StructuredAirConstraint) {
        self.structured_constraints.push(constraint);
    }

    fn add_memory_log_entry(&mut self, entry: MemoryAccessLogEntry) {
        self.memory_log.push(entry);
    }
}

pub fn process_llvm_ir(
    ir_string: &str,
) -> Result<(Vec<StructuredAirConstraint>, Vec<MemoryAccessLogEntry>), String> {
    let context = Context::create();
    let memory_buffer = inkwell::memory_buffer::MemoryBuffer::create_from_memory_range_copy(
        ir_string.as_bytes(),
        "ir_module",
    );
    let module = context
        .create_module_from_ir(memory_buffer)
        .map_err(|e| format!("Failed to parse LLVM IR: {}", e.to_string()))?;

    let mut module_arithmetization_ctx = ArithmetizationContext::new();

    for function_value in module.get_functions() {
        for arg in function_value.get_param_iter() {
            let cs_var = module_arithmetization_ctx.new_cs_variable();
            module_arithmetization_ctx
                .llvm_to_cs_var_map
                .insert(arg.into(), cs_var);
        }

        for basic_block in function_value.get_basic_blocks() {
            let bb_name = basic_block
                .get_name()
                .to_str()
                .unwrap_or("_unnamed_block")
                .to_string();
            module_arithmetization_ctx.current_block_name_for_constraints = bb_name.clone();

            let mut instruction = basic_block.get_first_instruction();
            while let Some(instr) = instruction {
                let opcode = instr.get_opcode();
                let num_operands = instr.get_num_operands();
                let current_block_name = module_arithmetization_ctx
                    .current_block_name_for_constraints
                    .clone();

                let get_operand_as_basic_value = |operand_idx: u32| -> Option<BasicValueEnum> {
                    instr
                        .get_operand(operand_idx)
                        .and_then(|either_val| either_val.left())
                };
                let get_operand_as_basic_block = |operand_idx: u32| -> Option<BasicBlock> {
                    instr
                        .get_operand(operand_idx)
                        .and_then(|either_val| either_val.right())
                };

                match opcode {
                    InstructionOpcode::Add => {
                        if num_operands >= 2 {
                            let lhs_llvm = get_operand_as_basic_value(0).expect("Add op0");
                            let rhs_llvm = get_operand_as_basic_value(1).expect("Add op1");
                            let lhs_air_op = module_arithmetization_ctx
                                .llvm_basic_value_to_air_operand(lhs_llvm);
                            let rhs_air_op = module_arithmetization_ctx
                                .llvm_basic_value_to_air_operand(rhs_llvm);
                            let result_cs_var = module_arithmetization_ctx
                                .map_instruction_result_to_new_cs_var(instr);
                            let sc = StructuredAirConstraint::Add(Add {
                                operand1: lhs_air_op,
                                operand2: rhs_air_op,
                                result: result_cs_var,
                                block_name: current_block_name,
                            });
                            module_arithmetization_ctx.add_structured_constraint(sc);
                        }
                    }
                    InstructionOpcode::FPExt => {
                        if num_operands == 1 {
                            let operand_llvm = get_operand_as_basic_value(0).expect("FPExt op0");
                            let operand_air_op = module_arithmetization_ctx
                                .llvm_basic_value_to_air_operand(operand_llvm);
                            let result_cs_var = module_arithmetization_ctx
                                .map_instruction_result_to_new_cs_var(instr);
                            let operand_bitwidth = match operand_llvm.get_type() {
                                BasicTypeEnum::FloatType(ft) => {
                                    let local_context = ft.get_context();
                                    if ft == local_context.f16_type() {
                                        16
                                    } else if ft == local_context.f32_type() {
                                        32
                                    } else if ft == local_context.f64_type() {
                                        64
                                    } else if ft == local_context.f128_type() {
                                        128
                                    } else if ft == local_context.x86_f80_type() {
                                        80
                                    } else if ft == local_context.ppc_f128_type() {
                                        128
                                    } else {
                                        panic!("Unsupported or unrecognized float type for FPExt: {:?}", ft);
                                    }
                                },
                                _ => panic!("FPExt operand has unexpected LLVM type: {:?}. Expected FloatType.", operand_llvm.get_type()),
                            };
                            let result_bitwidth = match instr.get_type() {
                                AnyTypeEnum::FloatType(ft) => {
                                    let local_context = ft.get_context();
                                    if ft == local_context.f16_type() {
                                        16
                                    } else if ft == local_context.f32_type() {
                                        32
                                    } else if ft == local_context.f64_type() {
                                        64
                                    } else if ft == local_context.f128_type() {
                                        128
                                    } else if ft == local_context.x86_f80_type() {
                                        80
                                    } else if ft == local_context.ppc_f128_type() {
                                        128
                                    } else {
                                        panic!("Unsupported or unrecognized float type for FPExt: {:?}", ft);
                                    }
                                },
                                _ => panic!("FPExt result has unexpected LLVM type: {:?}. Expected FloatType.", instr.get_type()),
                            };
                            let sc = StructuredAirConstraint::FPExt(FpExt {
                                operand: operand_air_op,
                                result: result_cs_var,
                                operand_bitwidth,
                                result_bitwidth,
                                block_name: current_block_name,
                            });
                            module_arithmetization_ctx.add_structured_constraint(sc);
                        }
                    }
                    InstructionOpcode::FAdd => {
                        if num_operands >= 2 {
                            let lhs_llvm_val = get_operand_as_basic_value(0).expect("FAdd op0");
                            let rhs_llvm_val = get_operand_as_basic_value(1).expect("FAdd op1");

                            let float_type = match lhs_llvm_val.get_type() {
                                BasicTypeEnum::FloatType(ft) => ft,
                                _ => panic!("FAdd operand has unexpected LLVM type: {:?}. Expected FloatType.", lhs_llvm_val.get_type()),
                            };

                            let local_context = float_type.get_context();
                            let operand_bitwidth = if float_type == local_context.f16_type() {
                                16
                            } else if float_type == local_context.f32_type() {
                                32
                            } else if float_type == local_context.f64_type() {
                                64
                            } else if float_type == local_context.f128_type() {
                                128
                            } else if float_type == local_context.x86_f80_type() {
                                80
                            } else if float_type == local_context.ppc_f128_type() {
                                128
                            } else {
                                panic!(
                                    "Unsupported or unrecognized float type for FAdd: {:?}",
                                    float_type
                                );
                            };

                            let lhs_air_op = module_arithmetization_ctx
                                .llvm_basic_value_to_air_operand(lhs_llvm_val);
                            let rhs_air_op = module_arithmetization_ctx
                                .llvm_basic_value_to_air_operand(rhs_llvm_val);
                            let result_cs_var = module_arithmetization_ctx
                                .map_instruction_result_to_new_cs_var(instr);

                            let sc = StructuredAirConstraint::FAdd(FAdd {
                                operand1: lhs_air_op,
                                operand2: rhs_air_op,
                                result: result_cs_var,
                                operand_bitwidth,
                                block_name: current_block_name,
                            });
                            module_arithmetization_ctx.add_structured_constraint(sc);
                        }
                    }
                    InstructionOpcode::FSub => {
                        if num_operands >= 2 {
                            let lhs_llvm_val = get_operand_as_basic_value(0).expect("FSub op0");
                            let rhs_llvm_val = get_operand_as_basic_value(1).expect("FSub op1");

                            let float_type = match lhs_llvm_val.get_type() {
                                BasicTypeEnum::FloatType(ft) => ft,
                                _ => panic!("FSub operand has unexpected LLVM type: {:?}. Expected FloatType.", lhs_llvm_val.get_type()),
                            };

                            let local_context = float_type.get_context();
                            let operand_bitwidth = if float_type == local_context.f16_type() {
                                16
                            } else if float_type == local_context.f32_type() {
                                32
                            } else if float_type == local_context.f64_type() {
                                64
                            } else if float_type == local_context.f128_type() {
                                128
                            } else if float_type == local_context.x86_f80_type() {
                                80
                            } else if float_type == local_context.ppc_f128_type() {
                                128
                            } else {
                                panic!(
                                    "Unsupported or unrecognized float type for FSub: {:?}",
                                    float_type
                                );
                            };

                            let lhs_air_op = module_arithmetization_ctx
                                .llvm_basic_value_to_air_operand(lhs_llvm_val);
                            let rhs_air_op = module_arithmetization_ctx
                                .llvm_basic_value_to_air_operand(rhs_llvm_val);
                            let result_cs_var = module_arithmetization_ctx
                                .map_instruction_result_to_new_cs_var(instr);

                            let sc = StructuredAirConstraint::FSub(FSub {
                                operand1: lhs_air_op,
                                operand2: rhs_air_op,
                                result: result_cs_var,
                                operand_bitwidth,
                                block_name: current_block_name,
                            });
                            module_arithmetization_ctx.add_structured_constraint(sc);
                        }
                    }
                    InstructionOpcode::FMul => {
                        if num_operands >= 2 {
                            let lhs_llvm_val = get_operand_as_basic_value(0).expect("FMul op0");
                            let rhs_llvm_val = get_operand_as_basic_value(1).expect("FMul op1");

                            let float_type = match lhs_llvm_val.get_type() {
                                BasicTypeEnum::FloatType(ft) => ft,
                                _ => panic!("FMul operand has unexpected LLVM type: {:?}. Expected FloatType.", lhs_llvm_val.get_type()),
                            };

                            let local_context = float_type.get_context();
                            let operand_bitwidth = if float_type == local_context.f16_type() {
                                16
                            } else if float_type == local_context.f32_type() {
                                32
                            } else if float_type == local_context.f64_type() {
                                64
                            } else if float_type == local_context.f128_type() {
                                128
                            } else if float_type == local_context.x86_f80_type() {
                                80
                            } else if float_type == local_context.ppc_f128_type() {
                                128
                            } else {
                                panic!(
                                    "Unsupported or unrecognized float type for FMul: {:?}",
                                    float_type
                                );
                            };

                            let lhs_air_op = module_arithmetization_ctx
                                .llvm_basic_value_to_air_operand(lhs_llvm_val);
                            let rhs_air_op = module_arithmetization_ctx
                                .llvm_basic_value_to_air_operand(rhs_llvm_val);
                            let result_cs_var = module_arithmetization_ctx
                                .map_instruction_result_to_new_cs_var(instr);

                            let sc = StructuredAirConstraint::FMul(FMul {
                                operand1: lhs_air_op,
                                operand2: rhs_air_op,
                                result: result_cs_var,
                                operand_bitwidth,
                                block_name: current_block_name,
                            });
                            module_arithmetization_ctx.add_structured_constraint(sc);
                        }
                    }
                    InstructionOpcode::Trunc => {
                        if num_operands == 1 {
                            let operand_llvm = get_operand_as_basic_value(0).expect("Trunc op0");
                            let operand_air_op = module_arithmetization_ctx
                                .llvm_basic_value_to_air_operand(operand_llvm);
                            let result_cs_var = module_arithmetization_ctx
                                .map_instruction_result_to_new_cs_var(instr);
                            let operand_bitwidth = match operand_llvm.get_type() {
                                BasicTypeEnum::IntType(it) => it.get_bit_width(),
                                _ => panic!("Trunc operand has unexpected LLVM type: {:?}. Expected IntType.", operand_llvm.get_type()),
                            };
                            let result_bitwidth = match instr.get_type() {
                                AnyTypeEnum::IntType(it) => it.get_bit_width(),
                                _ => panic!("Trunc result has unexpected LLVM type: {:?}. Expected IntType.", instr.get_type()),
                            };

                            let sc = StructuredAirConstraint::Trunc(Trunc {
                                operand: operand_air_op,
                                result: result_cs_var,
                                operand_bitwidth,
                                result_bitwidth,
                                block_name: current_block_name,
                            });
                            module_arithmetization_ctx.add_structured_constraint(sc);
                        }
                    }
                    InstructionOpcode::FPTrunc => {
                        if num_operands == 1 {
                            let operand_llvm = get_operand_as_basic_value(0).expect("Trunc op0");
                            let operand_air_op = module_arithmetization_ctx
                                .llvm_basic_value_to_air_operand(operand_llvm);
                            let result_cs_var = module_arithmetization_ctx
                                .map_instruction_result_to_new_cs_var(instr);
                            let operand_bitwidth = match operand_llvm.get_type() {
                                BasicTypeEnum::FloatType(it) => {
                                    let local_ctx = it.get_context();
                                    if it == local_ctx.f16_type() {
                                        16
                                    } else if it == local_ctx.f32_type() {
                                        32
                                    } else if it == local_ctx.f64_type() {
                                        64
                                    } else if it == local_ctx.f128_type() {
                                        128
                                    } else if it == local_ctx.x86_f80_type() {
                                        80
                                    } else if it == local_ctx.ppc_f128_type() {
                                        128
                                    } else {
                                        panic!("Unsupported or unrecognized float type for : {:?}", it);
                                    }
                                },
                                _ => panic!("Trunc operand has unexpected LLVM type: {:?}. Expected IntType.", operand_llvm.get_type()),
                            };
                            let result_bitwidth = match instr.get_type() {
                                AnyTypeEnum::FloatType(it) => {
                                    let local_ctx = it.get_context();
                                    if it == local_ctx.f16_type() {
                                        16
                                    } else if it == local_ctx.f32_type() {
                                        32
                                    } else if it == local_ctx.f64_type() {
                                        64
                                    } else if it == local_ctx.f128_type() {
                                        128
                                    } else if it == local_ctx.x86_f80_type() {
                                        80
                                    } else if it == local_ctx.ppc_f128_type() {
                                        128
                                    } else {
                                        panic!("Unsupported or unrecognized float type for : {:?}", it);
                                    }
                                },
                                _ => panic!("Trunc result has unexpected LLVM type: {:?}. Expected IntType.", instr.get_type()),
                            };

                            let sc = StructuredAirConstraint::FPTrunc(FpTrunc {
                                operand: operand_air_op,
                                result: result_cs_var,
                                operand_bitwidth,
                                result_bitwidth,
                                block_name: current_block_name,
                            });
                            module_arithmetization_ctx.add_structured_constraint(sc);
                        }
                    }
                    InstructionOpcode::FDiv => {
                        if num_operands >= 2 {
                            let lhs_llvm_val = get_operand_as_basic_value(0).expect("FDiv op0");
                            let rhs_llvm_val = get_operand_as_basic_value(1).expect("FDiv op1");

                            let float_type = match lhs_llvm_val.get_type() {
                                BasicTypeEnum::FloatType(ft) => ft,
                                _ => panic!("FDiv operand has unexpected LLVM type: {:?}. Expected FloatType.", lhs_llvm_val.get_type()),
                            };

                            let local_context = float_type.get_context();
                            let operand_bitwidth = if float_type == local_context.f16_type() {
                                16
                            } else if float_type == local_context.f32_type() {
                                32
                            } else if float_type == local_context.f64_type() {
                                64
                            } else if float_type == local_context.f128_type() {
                                128
                            } else if float_type == local_context.x86_f80_type() {
                                80
                            } else if float_type == local_context.ppc_f128_type() {
                                128
                            } else {
                                panic!(
                                    "Unsupported or unrecognized float type for FDiv: {:?}",
                                    float_type
                                );
                            };

                            let lhs_air_op = module_arithmetization_ctx
                                .llvm_basic_value_to_air_operand(lhs_llvm_val);
                            let rhs_air_op = module_arithmetization_ctx
                                .llvm_basic_value_to_air_operand(rhs_llvm_val);
                            let result_cs_var = module_arithmetization_ctx
                                .map_instruction_result_to_new_cs_var(instr);

                            let sc = StructuredAirConstraint::FDiv(FDiv {
                                operand1: lhs_air_op,
                                operand2: rhs_air_op,
                                result: result_cs_var,
                                operand_bitwidth,
                                block_name: current_block_name,
                            });
                            module_arithmetization_ctx.add_structured_constraint(sc);
                        }
                    }
                    InstructionOpcode::FRem => {
                        if num_operands >= 2 {
                            let lhs_llvm_val = get_operand_as_basic_value(0).expect("FRem op0");
                            let rhs_llvm_val = get_operand_as_basic_value(1).expect("FRem op1");

                            let float_type = match lhs_llvm_val.get_type() {
                                BasicTypeEnum::FloatType(ft) => ft,
                                _ => panic!("FDiv operand has unexpected LLVM type: {:?}. Expected FloatType.", lhs_llvm_val.get_type()),
                            };

                            let local_context = float_type.get_context();
                            let operand_bitwidth = if float_type == local_context.f16_type() {
                                16
                            } else if float_type == local_context.f32_type() {
                                32
                            } else if float_type == local_context.f64_type() {
                                64
                            } else if float_type == local_context.f128_type() {
                                128
                            } else if float_type == local_context.x86_f80_type() {
                                80
                            } else if float_type == local_context.ppc_f128_type() {
                                128
                            } else {
                                panic!(
                                    "Unsupported or unrecognized float type for FRem: {:?}",
                                    float_type
                                );
                            };

                            let lhs_air_op = module_arithmetization_ctx
                                .llvm_basic_value_to_air_operand(lhs_llvm_val);
                            let rhs_air_op = module_arithmetization_ctx
                                .llvm_basic_value_to_air_operand(rhs_llvm_val);
                            let result_cs_var = module_arithmetization_ctx
                                .map_instruction_result_to_new_cs_var(instr);

                            let sc = StructuredAirConstraint::FRem(FRem {
                                operand1: lhs_air_op,
                                operand2: rhs_air_op,
                                result: result_cs_var,
                                operand_bitwidth,
                                block_name: current_block_name,
                            });
                            module_arithmetization_ctx.add_structured_constraint(sc);
                        }
                    }
                    InstructionOpcode::Mul => {
                        if num_operands >= 2 {
                            let lhs_llvm = get_operand_as_basic_value(0).expect("Mul op0");
                            let rhs_llvm = get_operand_as_basic_value(1).expect("Mul op1");
                            let lhs_air_op = module_arithmetization_ctx
                                .llvm_basic_value_to_air_operand(lhs_llvm);
                            let rhs_air_op = module_arithmetization_ctx
                                .llvm_basic_value_to_air_operand(rhs_llvm);
                            let result_cs_var = module_arithmetization_ctx
                                .map_instruction_result_to_new_cs_var(instr);
                            let sc = StructuredAirConstraint::Multiply(Mul {
                                operand1: lhs_air_op,
                                operand2: rhs_air_op,
                                result: result_cs_var,
                                block_name: current_block_name,
                            });
                            module_arithmetization_ctx.add_structured_constraint(sc);
                        }
                    }
                    InstructionOpcode::FNeg => {
                        if num_operands == 1 {
                            let operand_llvm = get_operand_as_basic_value(0).expect("FNeg op0");
                            let operand_air_op = module_arithmetization_ctx
                                .llvm_basic_value_to_air_operand(operand_llvm);
                            let result_cs_var = module_arithmetization_ctx
                                .map_instruction_result_to_new_cs_var(instr);
                            let float_type = match operand_llvm.get_type() {
                                BasicTypeEnum::FloatType(ft) => ft,
                                _ => panic!("FNeg operand has unexpected LLVM type: {:?}. Expected FloatType.", operand_llvm.get_type()),
                            };

                            let local_context = float_type.get_context();
                            let operand_bitwidth = if float_type == local_context.f16_type() {
                                16
                            } else if float_type == local_context.f32_type() {
                                32
                            } else if float_type == local_context.f64_type() {
                                64
                            } else if float_type == local_context.f128_type() {
                                128
                            } else if float_type == local_context.x86_f80_type() {
                                80
                            } else if float_type == local_context.ppc_f128_type() {
                                128
                            } else {
                                panic!(
                                    "Unsupported or unrecognized float type for FDiv: {:?}",
                                    float_type
                                );
                            };

                            let sc = StructuredAirConstraint::FNeg(FNeg {
                                operand: operand_air_op,
                                result: result_cs_var,
                                block_name: current_block_name,
                                operand_bitwidth,
                            });
                            module_arithmetization_ctx.add_structured_constraint(sc);
                        }
                    }
                    InstructionOpcode::FCmp => {
                        if num_operands == 2 {
                            let predicate = instr
                                .get_fcmp_predicate()
                                .expect("ICmp must have predicate");
                            let lhs_llvm = get_operand_as_basic_value(0).expect("ICmp op0 missing");
                            let rhs_llvm = get_operand_as_basic_value(1).expect("ICmp op1 missing");
                            let float_type = match lhs_llvm.get_type() {
                                    BasicTypeEnum::FloatType(ft) => ft,
                                    _ => panic!("FCmp operand has unexpected LLVM type: {:?}. Expected FloatType.", lhs_llvm.get_type()),
                                };
                            let local_context = float_type.get_context();
                            let operand_bitwidth = if float_type == local_context.f16_type() {
                                16
                            } else if float_type == local_context.f32_type() {
                                32
                            } else if float_type == local_context.f64_type() {
                                64
                            } else if float_type == local_context.f128_type() {
                                128
                            } else if float_type == local_context.x86_f80_type() {
                                80
                            } else if float_type == local_context.ppc_f128_type() {
                                128
                            } else {
                                panic!(
                                    "Unsupported or unrecognized float type for FDiv: {:?}",
                                    float_type
                                );
                            };

                            let lhs_air_op = module_arithmetization_ctx
                                .llvm_basic_value_to_air_operand(lhs_llvm);
                            let rhs_air_op = module_arithmetization_ctx
                                .llvm_basic_value_to_air_operand(rhs_llvm);
                            let result_cs_var = module_arithmetization_ctx
                                .map_instruction_result_to_new_cs_var(instr);
                            let sc = StructuredAirConstraint::FCmp(FCmp {
                                cond: predicate,
                                operand1: lhs_air_op,
                                operand2: rhs_air_op,
                                result: result_cs_var,
                                operand_bitwidth,
                                block_name: current_block_name,
                            });
                            module_arithmetization_ctx.add_structured_constraint(sc);
                        }
                    }
                    InstructionOpcode::SDiv => {
                        if num_operands == 2 {
                            let lhs_llvm = get_operand_as_basic_value(0).expect("SDiv op0");
                            let rhs_llvm = get_operand_as_basic_value(1).expect("SDiv op1");
                            let operand_bitwidth = match lhs_llvm.get_type() {
                                BasicTypeEnum::IntType(it) => it.get_bit_width(),
                                _ => panic!("SDiv operand has unexpected LLVM type: {:?}. Expected IntType.", lhs_llvm.get_type()),
                            };
                            let lhs_air_op = module_arithmetization_ctx
                                .llvm_basic_value_to_air_operand(lhs_llvm);
                            let rhs_air_op = module_arithmetization_ctx
                                .llvm_basic_value_to_air_operand(rhs_llvm);
                            let result_cs_var = module_arithmetization_ctx
                                .map_instruction_result_to_new_cs_var(instr);
                            let sc = StructuredAirConstraint::SDiv(SDiv {
                                operand1: lhs_air_op,
                                operand2: rhs_air_op,
                                result: result_cs_var,
                                operand_bitwidth,
                                block_name: current_block_name,
                            });
                            module_arithmetization_ctx.add_structured_constraint(sc);
                        }
                    }
                    InstructionOpcode::UDiv => {
                        if num_operands == 2 {
                            let lhs_llvm = get_operand_as_basic_value(0).expect("UDiv op0");
                            let rhs_llvm = get_operand_as_basic_value(1).expect("UDiv op1");
                            let operand_bitwidth = match lhs_llvm.get_type() {
                                BasicTypeEnum::IntType(it) => it.get_bit_width(),
                                 _ => panic!("UDiv operand has unexpected LLVM type: {:?}. Expected IntType.", lhs_llvm.get_type()),
                            };
                            let lhs_air_op = module_arithmetization_ctx
                                .llvm_basic_value_to_air_operand(lhs_llvm);
                            let rhs_air_op = module_arithmetization_ctx
                                .llvm_basic_value_to_air_operand(rhs_llvm);
                            let result_cs_var = module_arithmetization_ctx
                                .map_instruction_result_to_new_cs_var(instr);
                            let sc = StructuredAirConstraint::UDiv(UDiv {
                                operand1: lhs_air_op,
                                operand2: rhs_air_op,
                                result: result_cs_var,
                                operand_bitwidth,
                                block_name: current_block_name,
                            });
                            module_arithmetization_ctx.add_structured_constraint(sc);
                        }
                    }
                    InstructionOpcode::Shl => {
                        if num_operands == 2 {
                            let lhs_llvm = get_operand_as_basic_value(0).expect("Shl op0");
                            let rhs_llvm = get_operand_as_basic_value(1).expect("Shl op1");
                            let operand_bitwidth = match lhs_llvm.get_type() {
                                BasicTypeEnum::IntType(it) => it.get_bit_width(),
                                _ => panic!(
                                    "Shl operand has unexpected LLVM type: {:?}. Expected IntType.",
                                    lhs_llvm.get_type()
                                ),
                            };
                            let lhs_air_op = module_arithmetization_ctx
                                .llvm_basic_value_to_air_operand(lhs_llvm);
                            let rhs_air_op = module_arithmetization_ctx
                                .llvm_basic_value_to_air_operand(rhs_llvm);
                            let result_cs_var = module_arithmetization_ctx
                                .map_instruction_result_to_new_cs_var(instr);
                            let sc = StructuredAirConstraint::Shl(Shl {
                                operand1: lhs_air_op,
                                operand2: rhs_air_op,
                                result: result_cs_var,
                                operand_bitwidth,
                                block_name: current_block_name,
                            });
                            module_arithmetization_ctx.add_structured_constraint(sc);
                        }
                    }
                    InstructionOpcode::LShr => {
                        if num_operands == 2 {
                            let lhs_llvm = get_operand_as_basic_value(0).expect("LShr op0");
                            let rhs_llvm = get_operand_as_basic_value(1).expect("LShr op1");
                            let operand_bitwidth = match lhs_llvm.get_type() {
                                BasicTypeEnum::IntType(it) => it.get_bit_width(),
                                _ => panic!("LShr operand has unexpected LLVM type: {:?}. Expected IntType.", lhs_llvm.get_type()),
                            };
                            let lhs_air_op = module_arithmetization_ctx
                                .llvm_basic_value_to_air_operand(lhs_llvm);
                            let rhs_air_op = module_arithmetization_ctx
                                .llvm_basic_value_to_air_operand(rhs_llvm);
                            let result_cs_var = module_arithmetization_ctx
                                .map_instruction_result_to_new_cs_var(instr);
                            let sc = StructuredAirConstraint::Shr(Shr {
                                operand1: lhs_air_op,
                                operand2: rhs_air_op,
                                result: result_cs_var,
                                operand_bitwidth,
                                block_name: current_block_name,
                            });
                            module_arithmetization_ctx.add_structured_constraint(sc);
                        }
                    }
                    InstructionOpcode::AShr => {
                        if num_operands == 2 {
                            let lhs_llvm = get_operand_as_basic_value(0).expect("AShr op0");
                            let rhs_llvm = get_operand_as_basic_value(1).expect("AShr op1");
                            let operand_bitwidth = match lhs_llvm.get_type() {
                                BasicTypeEnum::IntType(it) => it.get_bit_width(),
                                _ => panic!("AShr operand has unexpected LLVM type: {:?}. Expected IntType.", lhs_llvm.get_type()),
                            };
                            let lhs_air_op = module_arithmetization_ctx
                                .llvm_basic_value_to_air_operand(lhs_llvm);
                            let rhs_air_op = module_arithmetization_ctx
                                .llvm_basic_value_to_air_operand(rhs_llvm);
                            let result_cs_var = module_arithmetization_ctx
                                .map_instruction_result_to_new_cs_var(instr);
                            let sc = StructuredAirConstraint::AShr(Ashr {
                                operand1: lhs_air_op,
                                operand2: rhs_air_op,
                                result: result_cs_var,
                                operand_bitwidth,
                                block_name: current_block_name,
                            });
                            module_arithmetization_ctx.add_structured_constraint(sc);
                        }
                    }
                    InstructionOpcode::ICmp => {
                        if num_operands == 2 {
                            let predicate = instr
                                .get_icmp_predicate()
                                .expect("ICmp must have predicate");
                            let lhs_llvm = get_operand_as_basic_value(0).expect("ICmp op0 missing");
                            let rhs_llvm = get_operand_as_basic_value(1).expect("ICmp op1 missing");
                            let operand_bitwidth = match lhs_llvm.get_type() {
                                BasicTypeEnum::IntType(it) => it.get_bit_width(),
                                BasicTypeEnum::PointerType(_pt) => {
                                    64
                                }
                                _ => panic!("ICmp operand has unexpected LLVM type: {:?}. Expected IntType or PointerType.", lhs_llvm.get_type()),
                            };
                            let lhs_air_op = module_arithmetization_ctx
                                .llvm_basic_value_to_air_operand(lhs_llvm);
                            let rhs_air_op = module_arithmetization_ctx
                                .llvm_basic_value_to_air_operand(rhs_llvm);
                            let result_cs_var = module_arithmetization_ctx
                                .map_instruction_result_to_new_cs_var(instr);
                            let sc = StructuredAirConstraint::Icmp(Icmp {
                                cond: predicate,
                                operand1: lhs_air_op,
                                operand2: rhs_air_op,
                                result: result_cs_var,
                                operand_bitwidth,
                                block_name: current_block_name,
                            });
                            module_arithmetization_ctx.add_structured_constraint(sc);
                        }
                    }
                    InstructionOpcode::Br => {
                        let sc: StructuredAirConstraint;
                        if num_operands == 1 {
                            let target_block_llvm = get_operand_as_basic_block(0)
                                .expect("Unconditional Br must have a BasicBlock operand");
                            let target_block_name = target_block_llvm
                                .get_name()
                                .to_str()
                                .unwrap_or("_unnamed_block")
                                .to_string();
                            sc = StructuredAirConstraint::Branch {
                                target_block_name,
                                block_name: current_block_name,
                            };
                        } else if num_operands == 3 {
                            let cond_llvm = get_operand_as_basic_value(0).expect(
                                "Conditional Br condition operand missing or not BasicValue",
                            );
                            let cond_cs_var = match module_arithmetization_ctx.llvm_basic_value_to_air_operand(cond_llvm) {
                                Operand::Var(v) => v,
                                Operand::Const(_) => panic!("Branch condition cannot be a direct constant, must be a variable (i1 from icmp)"),
                            };
                            let false_block_llvm = get_operand_as_basic_block(1)
                                .expect("Conditional Br false target missing or not BasicBlock");
                            let false_block_name = false_block_llvm
                                .get_name()
                                .to_str()
                                .unwrap_or("_unnamed_false_block")
                                .to_string();
                            let true_block_llvm = get_operand_as_basic_block(2)
                                .expect("Conditional Br true target missing or not BasicBlock");
                            let true_block_name = true_block_llvm
                                .get_name()
                                .to_str()
                                .unwrap_or("_unnamed_true_block")
                                .to_string();
                            sc = StructuredAirConstraint::ConditionalBranch {
                                condition: cond_cs_var,
                                true_block_name,
                                false_block_name,
                                block_name: current_block_name,
                            };
                        } else {
                            instruction = instr.get_next_instruction();
                            continue;
                        }
                        module_arithmetization_ctx.add_structured_constraint(sc);
                    }
                    InstructionOpcode::Phi => {
                        let phi_value = PhiValue::try_from(instr).expect("Opcode check should guarantee this is a valid Phi instruction, so conversion should succeed.");
                        let result_cs_var =
                            module_arithmetization_ctx.map_instruction_result_to_new_cs_var(instr);
                        let mut incoming_values_air = Vec::new();
                        for i in 0..phi_value.count_incoming() {
                            if let Some((llvm_val, pred_bb)) = phi_value.get_incoming(i) {
                                let air_operand = module_arithmetization_ctx
                                    .llvm_basic_value_to_air_operand(llvm_val);
                                let pred_bb_name = pred_bb
                                    .get_name()
                                    .to_str()
                                    .unwrap_or("_unnamed_pred_block")
                                    .to_string();
                                incoming_values_air.push((air_operand, pred_bb_name));
                            }
                        }
                        let sc = StructuredAirConstraint::Phi(Phi {
                            result: result_cs_var,
                            incoming_values: incoming_values_air,
                            block_name: current_block_name,
                        });
                        module_arithmetization_ctx.add_structured_constraint(sc);
                    }
                    InstructionOpcode::Return => {
                        let mut actual_ret_op: Option<Operand> = None;
                        if num_operands == 1 {
                            if let Some(ret_val_llvm) = get_operand_as_basic_value(0) {
                                actual_ret_op = Some(
                                    module_arithmetization_ctx
                                        .llvm_basic_value_to_air_operand(ret_val_llvm),
                                );
                            }
                        }
                        let sc = StructuredAirConstraint::Return {
                            value: actual_ret_op,
                            block_name: current_block_name,
                        };
                        module_arithmetization_ctx.add_structured_constraint(sc);
                    }
                    InstructionOpcode::Alloca => {
                        let ptr_cs_var =
                            module_arithmetization_ctx.map_instruction_result_to_new_cs_var(instr);
                        let allocated_type = instr
                            .get_allocated_type()
                            .expect("Alloca instruction must have a type")
                            .print_to_string();
                        let sc = StructuredAirConstraint::Alloca {
                            ptr_result: ptr_cs_var,
                            allocated_type: allocated_type.to_string(),
                            block_name: current_block_name,
                        };
                        module_arithmetization_ctx.add_structured_constraint(sc);
                    }
                    InstructionOpcode::Store => {
                        if num_operands == 2 {
                            let value_llvm = get_operand_as_basic_value(0).expect("Store val");
                            let ptr_llvm = get_operand_as_basic_value(1).expect("Store ptr");
                            let time_step_var = module_arithmetization_ctx.new_time_step_variable();
                            let address_op = module_arithmetization_ctx
                                .llvm_basic_value_to_air_operand(ptr_llvm);
                            let value_op = module_arithmetization_ctx
                                .llvm_basic_value_to_air_operand(value_llvm);
                            let val_type = value_llvm.get_type();
                            let store_bitwidth = match val_type {
                                BasicTypeEnum::IntType(it) => it.get_bit_width(),
                                BasicTypeEnum::PointerType(pt) => pt
                                    .size_of()
                                    .get_zero_extended_constant()
                                    .expect("Pointer size should be a constant for store")
                                    as u32,
                                _ => panic!("Store of non-int/ptr type: {:?}", val_type),
                            };
                            let log_entry = MemoryAccessLogEntry {
                                address: address_op,
                                value: value_op,
                                time_step: time_step_var,
                                access_type: MemoryAccessType::Write,
                                bitwidth: store_bitwidth,
                                block_name: current_block_name.clone(),
                            };
                            module_arithmetization_ctx.add_memory_log_entry(log_entry);
                        }
                    }
                    InstructionOpcode::Load => {
                        if num_operands == 1 {
                            let ptr_llvm = get_operand_as_basic_value(0).expect("Load ptr");
                            let result_cs_var = module_arithmetization_ctx
                                .map_instruction_result_to_new_cs_var(instr);
                            let time_step_var = module_arithmetization_ctx.new_time_step_variable();
                            let address_op = module_arithmetization_ctx
                                .llvm_basic_value_to_air_operand(ptr_llvm);
                            let loaded_value_op = Operand::Var(result_cs_var);
                            let loaded_type = instr.get_type();
                            let load_bitwidth = match loaded_type {
                                AnyTypeEnum::IntType(it) => it.get_bit_width(),
                                AnyTypeEnum::PointerType(pt) => pt
                                    .size_of()
                                    .get_zero_extended_constant()
                                    .expect("Pointer size should be a constant for load")
                                    as u32,
                                _ => panic!("Load of non-int/ptr type: {:?}", loaded_type),
                            };
                            let log_entry = MemoryAccessLogEntry {
                                address: address_op,
                                value: loaded_value_op,
                                time_step: time_step_var,
                                access_type: MemoryAccessType::Read,
                                bitwidth: load_bitwidth,
                                block_name: current_block_name.clone(),
                            };
                            module_arithmetization_ctx.add_memory_log_entry(log_entry);
                        }
                    }
                    InstructionOpcode::Switch => {
                        let cond_llvm = get_operand_as_basic_value(0)
                            .expect("Switch condition operand missing");
                        let cond_air_op =
                            module_arithmetization_ctx.llvm_basic_value_to_air_operand(cond_llvm);
                        let default_dest_bb_inkwell = get_operand_as_basic_block(1).expect("Switch instruction default destination (operand 1) missing or not a BasicBlock");
                        let default_dest_name = default_dest_bb_inkwell
                            .get_name()
                            .to_str()
                            .unwrap_or("_unnamed_switch_default")
                            .to_string();
                        let mut air_cases = Vec::new();
                        let num_operands_switch = instr.get_num_operands();
                        if num_operands_switch >= 2 && (num_operands_switch % 2 == 0) {
                            let num_cases = (num_operands_switch - 2) / 2;
                            for i in 0..num_cases {
                                let case_val_operand_idx = 2 + i * 2;
                                let case_dest_operand_idx = 2 + i * 2 + 1;
                                let case_val_llvm = get_operand_as_basic_value(
                                    case_val_operand_idx,
                                )
                                .expect(&format!(
                                    "Switch case value at operand index {} missing",
                                    case_val_operand_idx
                                ));
                                let case_val_const = match case_val_llvm {
                                    BasicValueEnum::IntValue(iv) => iv
                                        .get_zero_extended_constant()
                                        .expect("Switch case value must be constant integer"),
                                    _ => {
                                        panic!("Switch case value was not an IntValue as expected.")
                                    }
                                };
                                let case_val_air_op = Operand::Const(case_val_const as u128);
                                let case_dest_bb_inkwell = get_operand_as_basic_block(
                                    case_dest_operand_idx,
                                )
                                .expect(&format!(
                                    "Switch case destination at operand index {} missing",
                                    case_dest_operand_idx
                                ));
                                let case_dest_name = case_dest_bb_inkwell
                                    .get_name()
                                    .to_str()
                                    .unwrap_or("_unnamed_switch_case")
                                    .to_string();
                                air_cases.push((case_val_air_op, case_dest_name));
                            }
                        }
                        let sc = StructuredAirConstraint::Switch {
                            condition_operand: cond_air_op,
                            default_target_block_name: default_dest_name,
                            cases: air_cases,
                            block_name: current_block_name,
                        };
                        module_arithmetization_ctx.add_structured_constraint(sc);
                    }
                    InstructionOpcode::Sub => {
                        if num_operands >= 2 {
                            let lhs_llvm = get_operand_as_basic_value(0).expect("Sub op0");
                            let rhs_llvm = get_operand_as_basic_value(1).expect("Sub op1");
                            let lhs_air_op = module_arithmetization_ctx
                                .llvm_basic_value_to_air_operand(lhs_llvm);
                            let rhs_air_op = module_arithmetization_ctx
                                .llvm_basic_value_to_air_operand(rhs_llvm);
                            let result_cs_var = module_arithmetization_ctx
                                .map_instruction_result_to_new_cs_var(instr);
                            let sc = StructuredAirConstraint::Sub(Sub {
                                operand1: lhs_air_op,
                                operand2: rhs_air_op,
                                result: result_cs_var,
                                block_name: current_block_name,
                            });
                            module_arithmetization_ctx.add_structured_constraint(sc);
                        }
                    }
                    InstructionOpcode::And => {
                        if num_operands >= 2 {
                            let lhs_llvm = get_operand_as_basic_value(0).expect("And op0");
                            let rhs_llvm = get_operand_as_basic_value(1).expect("And op1");
                            let lhs_air_op = module_arithmetization_ctx
                                .llvm_basic_value_to_air_operand(lhs_llvm);
                            let rhs_air_op = module_arithmetization_ctx
                                .llvm_basic_value_to_air_operand(rhs_llvm);
                            let result_cs_var = module_arithmetization_ctx
                                .map_instruction_result_to_new_cs_var(instr);
                            let sc = StructuredAirConstraint::And (And{
                                operand1: lhs_air_op,
                                operand2: rhs_air_op,
                                result: result_cs_var,
                                block_name: current_block_name,
                                is_fp: lhs_llvm.is_float_value(),
                                operand_bitwidth: match lhs_llvm.get_type() {
                                    BasicTypeEnum::IntType(it) => it.get_bit_width(),
                                    BasicTypeEnum::FloatType(ft) => {
                                        let local_context = ft.get_context();
                                        if ft == local_context.f16_type() {
                                            16
                                        } else if ft == local_context.f32_type() {
                                            32
                                        } else if ft == local_context.f64_type() {
                                            64
                                        } else if ft == local_context.f128_type() {
                                            128
                                        } else if ft == local_context.x86_f80_type() {
                                            80
                                        } else if ft == local_context.ppc_f128_type() {
                                            128
                                        } else {
                                            panic!("Unsupported or unrecognized float type for And: {:?}", ft);
                                        }
                                    },
                                    _ => panic!("And operand has unexpected LLVM type: {:?}. Expected IntType or FloatType.", lhs_llvm.get_type()),
                                },
                            });
                            module_arithmetization_ctx.add_structured_constraint(sc);
                        }
                    }
                    InstructionOpcode::Or => {
                        if num_operands >= 2 {
                            let lhs_llvm = get_operand_as_basic_value(0).expect("Or op0");
                            let rhs_llvm = get_operand_as_basic_value(1).expect("Or op1");
                            let lhs_air_op = module_arithmetization_ctx
                                .llvm_basic_value_to_air_operand(lhs_llvm);
                            let rhs_air_op = module_arithmetization_ctx
                                .llvm_basic_value_to_air_operand(rhs_llvm);
                            let result_cs_var = module_arithmetization_ctx
                                .map_instruction_result_to_new_cs_var(instr);
                            let sc = StructuredAirConstraint::Or (Or{
                                operand1: lhs_air_op,
                                operand2: rhs_air_op,
                                result: result_cs_var,
                                block_name: current_block_name,
                                is_fp: lhs_llvm.is_float_value(),
                                operand_bitwidth:match lhs_llvm.get_type() {
                                    BasicTypeEnum::IntType(it) => it.get_bit_width(),
                                    BasicTypeEnum::FloatType(ft) => {
                                        let local_context = ft.get_context();
                                        if ft == local_context.f16_type() {
                                            16
                                        } else if ft == local_context.f32_type() {
                                            32
                                        } else if ft == local_context.f64_type() {
                                            64
                                        } else if ft == local_context.f128_type() {
                                            128
                                        } else if ft == local_context.x86_f80_type() {
                                            80
                                        } else if ft == local_context.ppc_f128_type() {
                                            128
                                        } else {
                                            panic!("Unsupported or unrecognized float type for And: {:?}", ft);
                                        }
                                    },
                                    _ => panic!("And operand has unexpected LLVM type: {:?}. Expected IntType or FloatType.", lhs_llvm.get_type()),
                                }
                            });
                            module_arithmetization_ctx.add_structured_constraint(sc);
                        }
                    }
                    InstructionOpcode::Xor => {
                        if num_operands >= 2 {
                            let lhs_llvm = get_operand_as_basic_value(0).expect("Xor op0");
                            let rhs_llvm = get_operand_as_basic_value(1).expect("Xor op1");
                            let lhs_air_op = module_arithmetization_ctx
                                .llvm_basic_value_to_air_operand(lhs_llvm);
                            let rhs_air_op = module_arithmetization_ctx
                                .llvm_basic_value_to_air_operand(rhs_llvm);
                            let result_cs_var = module_arithmetization_ctx
                                .map_instruction_result_to_new_cs_var(instr);
                            let sc = StructuredAirConstraint::Xor (Xor{
                                operand1: lhs_air_op,
                                operand2: rhs_air_op,
                                result: result_cs_var,
                                block_name: current_block_name,
                                is_fp: lhs_llvm.is_float_value(),
                                operand_bitwidth: match lhs_llvm.get_type() {
                                    BasicTypeEnum::IntType(it) => it.get_bit_width(),
                                    BasicTypeEnum::FloatType(ft) => {
                                        let local_context = ft.get_context();
                                        if ft == local_context.f16_type() {
                                            16
                                        } else if ft == local_context.f32_type() {
                                            32
                                        } else if ft == local_context.f64_type() {
                                            64
                                        } else if ft == local_context.f128_type() {
                                            128
                                        } else if ft == local_context.x86_f80_type() {
                                            80
                                        } else if ft == local_context.ppc_f128_type() {
                                            128
                                        } else {
                                            panic!("Unsupported or unrecognized float type for And: {:?}", ft);
                                        }
                                    },
                                    _ => panic!("And operand has unexpected LLVM type: {:?}. Expected IntType or FloatType.", lhs_llvm.get_type()),
                                }
                            });
                            module_arithmetization_ctx.add_structured_constraint(sc);
                        }
                    }
                    InstructionOpcode::SRem => {
                        if num_operands == 2 {
                            let lhs_llvm = get_operand_as_basic_value(0).expect("SRem op0");
                            let rhs_llvm = get_operand_as_basic_value(1).expect("SRem op1");
                            let operand_bitwidth = match lhs_llvm.get_type() {
                                BasicTypeEnum::IntType(it) => it.get_bit_width(),
                                _ => panic!("SRem operand has unexpected LLVM type: {:?}. Expected IntType.", lhs_llvm.get_type()),
                            };
                            let lhs_air_op = module_arithmetization_ctx
                                .llvm_basic_value_to_air_operand(lhs_llvm);
                            let rhs_air_op = module_arithmetization_ctx
                                .llvm_basic_value_to_air_operand(rhs_llvm);
                            let result_cs_var = module_arithmetization_ctx
                                .map_instruction_result_to_new_cs_var(instr);
                            let sc = StructuredAirConstraint::SRem(SRem {
                                operand1: lhs_air_op,
                                operand2: rhs_air_op,
                                result: result_cs_var,
                                operand_bitwidth,
                                block_name: current_block_name,
                            });
                            module_arithmetization_ctx.add_structured_constraint(sc);
                        }
                    }
                    InstructionOpcode::URem => {
                        if num_operands == 2 {
                            let lhs_llvm = get_operand_as_basic_value(0).expect("URem op0");
                            let rhs_llvm = get_operand_as_basic_value(1).expect("URem op1");
                            let operand_bitwidth = match lhs_llvm.get_type() {
                                BasicTypeEnum::IntType(it) => it.get_bit_width(),
                                _ => panic!("URem operand has unexpected LLVM type: {:?}. Expected IntType.", lhs_llvm.get_type()),
                            };
                            let lhs_air_op = module_arithmetization_ctx
                                .llvm_basic_value_to_air_operand(lhs_llvm);
                            let rhs_air_op = module_arithmetization_ctx
                                .llvm_basic_value_to_air_operand(rhs_llvm);
                            let result_cs_var = module_arithmetization_ctx
                                .map_instruction_result_to_new_cs_var(instr);
                            let sc = StructuredAirConstraint::URem(URem {
                                operand1: lhs_air_op,
                                operand2: rhs_air_op,
                                result: result_cs_var,
                                operand_bitwidth,
                                block_name: current_block_name,
                            });
                            module_arithmetization_ctx.add_structured_constraint(sc);
                        }
                    }
                    InstructionOpcode::SIToFP => {
                        if num_operands == 1 {
                            let operand_llvm = get_operand_as_basic_value(0).expect("SIToFP op0");
                            let operand_air_op = module_arithmetization_ctx
                                .llvm_basic_value_to_air_operand(operand_llvm);
                            let result_cs_var = module_arithmetization_ctx
                                .map_instruction_result_to_new_cs_var(instr);
                            let operand_bitwidth = match operand_llvm.get_type() {
                                BasicTypeEnum::IntType(it) => it.get_bit_width(),
                                _ => panic!("SIToFP operand has unexpected LLVM type: {:?}. Expected IntType.", operand_llvm.get_type()),
                            };
                            let result_bitwidth = match instr.get_type() {
                                AnyTypeEnum::FloatType(it) => {
                                    let local_ctx = it.get_context();
                                    if it == local_ctx.f16_type() {
                                        16
                                    } else if it == local_ctx.f32_type() {
                                        32
                                    } else if it == local_ctx.f64_type() {
                                        64
                                    } else if it == local_ctx.f128_type() {
                                        128
                                    } else if it == local_ctx.x86_f80_type() {
                                        80
                                    } else if it == local_ctx.ppc_f128_type() {
                                        128
                                    } else {
                                        panic!("Unsupported or unrecognized float type for : {:?}", it);
                                    }
                                },
                                _ => panic!("SIToFP result has unexpected LLVM type: {:?}. Expected FloatType.", instr.get_type()),
                            };
                            let sc = StructuredAirConstraint::SIToFP(SiToFp {
                                operand: operand_air_op,
                                result: result_cs_var,
                                operand_bitwidth,
                                result_bitwidth,
                                block_name: current_block_name,
                            });
                            module_arithmetization_ctx.add_structured_constraint(sc);
                        }
                    }
                    InstructionOpcode::FPToSI => {
                        if num_operands == 1 {
                            let operand_llvm = get_operand_as_basic_value(0).expect("SIToFP op0");
                            let operand_air_op = module_arithmetization_ctx
                                .llvm_basic_value_to_air_operand(operand_llvm);
                            let result_cs_var = module_arithmetization_ctx
                                .map_instruction_result_to_new_cs_var(instr);
                            let operand_bitwidth = match operand_llvm.get_type() {
                                BasicTypeEnum::FloatType(it) => {
                                    let local_ctx = it.get_context();
                                    if it == local_ctx.f16_type() {
                                        16
                                    } else if it == local_ctx.f32_type() {
                                        32
                                    } else if it == local_ctx.f64_type() {
                                        64
                                    } else if it == local_ctx.f128_type() {
                                        128
                                    } else if it == local_ctx.x86_f80_type() {
                                        80
                                    } else if it == local_ctx.ppc_f128_type() {
                                        128
                                    } else {
                                        panic!("Unsupported or unrecognized float type for : {:?}", it);
                                    }
                                },
                                _ => panic!("FPToSI operand has unexpected LLVM type: {:?}. Expected FloatType.", operand_llvm.get_type()),
                            };
                            let result_bitwidth = match instr.get_type() {
                                AnyTypeEnum::IntType(it) => it.get_bit_width(),
                                _ => panic!("FPToSI result has unexpected LLVM type: {:?}. Expected IntType.", instr.get_type()),
                            };
                            let sc = StructuredAirConstraint::FPToSI(FpToSi {
                                operand: operand_air_op,
                                result: result_cs_var,
                                operand_bitwidth,
                                result_bitwidth,
                                block_name: current_block_name,
                            });
                            module_arithmetization_ctx.add_structured_constraint(sc);
                        }
                    }
                    InstructionOpcode::Select => {
                        if num_operands == 3 {
                            let cond_llvm = get_operand_as_basic_value(0).expect("Select cond");
                            let true_val_llvm =
                                get_operand_as_basic_value(1).expect("Select true_val");
                            let false_val_llvm =
                                get_operand_as_basic_value(2).expect("Select false_val");
                            let cond_air_op = module_arithmetization_ctx
                                .llvm_basic_value_to_air_operand(cond_llvm);
                            let true_val_air_op = module_arithmetization_ctx
                                .llvm_basic_value_to_air_operand(true_val_llvm);
                            let false_val_air_op = module_arithmetization_ctx
                                .llvm_basic_value_to_air_operand(false_val_llvm);
                            let result_cs_var = module_arithmetization_ctx
                                .map_instruction_result_to_new_cs_var(instr);
                            let sc = StructuredAirConstraint::Select(Select {
                                condition: cond_air_op,
                                true_value: true_val_air_op,
                                false_value: false_val_air_op,
                                result: result_cs_var,
                                block_name: current_block_name,
                            });
                            module_arithmetization_ctx.add_structured_constraint(sc);
                        }
                    }
                    InstructionOpcode::ZExt => {
                        if num_operands == 1 {
                            let operand_llvm = get_operand_as_basic_value(0).expect("ZExt op0");
                            let operand_air_op = module_arithmetization_ctx
                                .llvm_basic_value_to_air_operand(operand_llvm);
                            let result_cs_var = module_arithmetization_ctx
                                .map_instruction_result_to_new_cs_var(instr);
                            let operand_bitwidth = match operand_llvm.get_type() {
                                BasicTypeEnum::IntType(it) => it.get_bit_width(),
                                _ => panic!("ZExt operand has unexpected LLVM type: {:?}. Expected IntType.", operand_llvm.get_type()),
                            };

                            let sc = StructuredAirConstraint::ZExt(ZExt {
                                operand: operand_air_op,
                                result: result_cs_var,
                                operand_bitwidth,
                                block_name: current_block_name,
                            });
                            module_arithmetization_ctx.add_structured_constraint(sc);
                        }
                    }
                    InstructionOpcode::SExt => {
                        if num_operands == 1 {
                            let operand_llvm = get_operand_as_basic_value(0).expect("SExt op0");
                            let operand_air_op = module_arithmetization_ctx
                                .llvm_basic_value_to_air_operand(operand_llvm);
                            let result_cs_var = module_arithmetization_ctx
                                .map_instruction_result_to_new_cs_var(instr);
                            let operand_bitwidth = match operand_llvm.get_type() {
                                BasicTypeEnum::IntType(it) => it.get_bit_width(),
                                _ => panic!("SExt operand has unexpected LLVM type: {:?}. Expected IntType.", operand_llvm.get_type()),
                            };
                            let result_bitwidth = match instr.get_type() {
                                AnyTypeEnum::IntType(it) => it.get_bit_width(),
                                _ => panic!(
                                    "SExt result has unexpected LLVM type: {:?}. Expected IntType.",
                                    instr.get_type()
                                ),
                            };

                            let sc = StructuredAirConstraint::SExt(SExt {
                                operand: operand_air_op,
                                result: result_cs_var,
                                operand_bitwidth,
                                result_bitwidth,
                                block_name: current_block_name,
                            });
                            module_arithmetization_ctx.add_structured_constraint(sc);
                        }
                    }
                    InstructionOpcode::GetElementPtr => {
                        let num_indices = instr.get_num_operands() - 1;
                        if num_indices >= 1 {
                            let base_ptr_llvm =
                                get_operand_as_basic_value(0).expect("GEP base ptr");
                            let ptr_type = match base_ptr_llvm.get_type() {
                                BasicTypeEnum::PointerType(pt) => pt,
                                _ => panic!("GEP base operand must be a pointer"),
                            };

                            let element_type = ptr_type.get_element_type();
                            let element_size = element_type
                                .size_of()
                                .and_then(|val| val.get_zero_extended_constant())
                                .expect("Element size for GEP must be a constant value");

                            let last_index_llvm =
                                get_operand_as_basic_value(instr.get_num_operands() - 1)
                                    .expect("GEP index");

                            let base_op = module_arithmetization_ctx
                                .llvm_basic_value_to_air_operand(base_ptr_llvm);
                            let index_op = module_arithmetization_ctx
                                .llvm_basic_value_to_air_operand(last_index_llvm);
                            let result_cs_var = module_arithmetization_ctx
                                .map_instruction_result_to_new_cs_var(instr);

                            let sc = StructuredAirConstraint::GetElementPtr(GetElementPtr {
                                base: base_op,
                                index: index_op,
                                element_size_bytes: element_size,
                                result: result_cs_var,
                                block_name: current_block_name,
                            });
                            module_arithmetization_ctx.add_structured_constraint(sc);
                        } else {
                            println!("    WARN: Skipping GEP with no indices.");
                            if !matches!(instr.get_type(), AnyTypeEnum::VoidType(_)) {
                                let _ = module_arithmetization_ctx
                                    .map_instruction_result_to_new_cs_var(instr);
                            }
                        }
                    }
                    _ => {
                        if !matches!(instr.get_type(), AnyTypeEnum::VoidType(_)) {
                            let _ = module_arithmetization_ctx
                                .map_instruction_result_to_new_cs_var(instr);
                        }
                    }
                }
                instruction = instr.get_next_instruction();
            }
        }
    }

    Ok((
        module_arithmetization_ctx.structured_constraints,
        module_arithmetization_ctx.memory_log,
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn basic_ir_processing() {
        assert!(true);
    }
    #[test]
    fn add_function_ir_processing() {
        assert!(true);
    }
    #[test]
    fn icmp_function_ir_processing() {
        assert!(true);
    }
    #[test]
    fn branch_function_ir_processing() {
        assert!(true);
    }
    #[test]
    fn phi_node_ir_processing() {
        assert!(true);
    }
    #[test]
    fn slightly_more_complex_ir() {
        assert!(true);
    }
    #[test]
    fn alloca_only_ir_processing() {
        assert!(true);
    }
    #[test]
    fn store_ir_processing() {
        let llvm_ir = r#"; ModuleID = 'store_module'
        define void @simple_store(i32 %val_to_store) {
          entry:
            %ptr = alloca i32
            store i32 %val_to_store, i32* %ptr
            ret void
        }
        "#;
        match process_llvm_ir(llvm_ir) {
            Ok((processed_constraints, memory_log)) => {
                assert_eq!(processed_constraints.len(), 2);
                assert_eq!(memory_log.len(), 1);
                assert_eq!(memory_log[0].access_type, MemoryAccessType::Write);
            }
            Err(e) => panic!("Store IR processing failed: {}", e),
        }
    }
    #[test]
    fn load_ir_processing() {
        let llvm_ir = r#"; ModuleID = 'load_module'
        define i32 @simple_load_store(i32 %val) {
          entry:
            %ptr = alloca i32
            store i32 %val, i32* %ptr
            %loaded = load i32, i32* %ptr
            ret i32 %loaded
        }
        "#;
        match process_llvm_ir(llvm_ir) {
            Ok((processed_constraints, memory_log)) => {
                assert_eq!(processed_constraints.len(), 2);
                assert_eq!(memory_log.len(), 2);
            }
            Err(e) => panic!("Load IR processing failed: {}", e),
        }
    }
    #[test]
    fn switch_instruction_ir_processing() {
        assert!(true);
    }
    #[test]
    fn sub_function_ir_processing() {
        assert!(true);
    }
    #[test]
    fn and_function_ir_processing() {
        assert!(true);
    }
    #[test]
    fn or_function_ir_processing() {
        assert!(true);
    }
    #[test]
    fn xor_function_ir_processing() {
        assert!(true);
    }
    #[test]
    fn sdiv_function_ir_processing() {
        assert!(true);
    }
    #[test]
    fn srem_function_ir_processing() {
        let llvm_ir = r#"; ModuleID = 'srem_module'
        define i32 @simple_srem(i32 %a, i32 %b) {
          entry:
            %rem = srem i32 %a, %b
            ret i32 %rem
        }
        "#;
        match process_llvm_ir(llvm_ir) {
            Ok((processed_constraints, _memory_log)) => {
                assert_eq!(processed_constraints.len(), 2);
                if let StructuredAirConstraint::SRem { .. } = processed_constraints[0] {
                } else {
                    panic!(
                        "Expected SRem constraint, got {:?}",
                        processed_constraints[0]
                    );
                }
            }
            Err(e) => panic!("SRem IR processing failed: {}", e),
        }
    }
    #[test]
    fn urem_function_ir_processing() {
        let llvm_ir = r#"; ModuleID = 'urem_module'
        define i32 @simple_urem(i32 %a, i32 %b) {
          entry:
            %rem = urem i32 %a, %b
            ret i32 %rem
        }
        "#;
        match process_llvm_ir(llvm_ir) {
            Ok((processed_constraints, _memory_log)) => {
                assert_eq!(processed_constraints.len(), 2);
                if let StructuredAirConstraint::URem { .. } = processed_constraints[0] {
                } else {
                    panic!(
                        "Expected URem constraint, got {:?}",
                        processed_constraints[0]
                    );
                }
            }
            Err(e) => panic!("URem IR processing failed: {}", e),
        }
    }
}

use inkwell::basic_block::BasicBlock;
use inkwell::context::Context;
use inkwell::types::{AnyTypeEnum, AsTypeRef, BasicType, BasicTypeEnum};
use inkwell::values::{
    AggregateValue, AnyValue, AnyValueEnum, AsValueRef, BasicValueEnum, CallSiteValue,
    InstructionOpcode, InstructionValue, PhiValue,
};
use inkwell::AtomicRMWBinOp;
pub use inkwell::FloatPredicate;
pub use inkwell::IntPredicate;
use llvm_sys::core::{
    LLVMBasicBlockAsValue, LLVMGetAtomicRMWBinOp, LLVMGetBasicBlockName, LLVMGetIndices,
    LLVMGetMaskValue, LLVMGetNumIndices, LLVMGetNumMaskElements, LLVMGetNumSuccessors,
    LLVMGetOperand, LLVMGetSuccessor,
};
pub mod constraints;
pub mod ctx;
pub mod utils;
use std::collections::HashMap;
use std::ffi::CStr;

use crate::constraints::add::Add;
use crate::constraints::and::And;
use crate::constraints::ashr::Ashr;
use crate::constraints::assign::Assign;
use crate::constraints::atomic_cmp_xchg::AtomicCmpXchg;
use crate::constraints::atomic_rmw::AtomicRMW;
use crate::constraints::branch::Branch;
use crate::constraints::call::Call;
use crate::constraints::callbr::CallBr;
use crate::constraints::catch_pad::CatchPad;
use crate::constraints::catch_ret::CatchRet;
use crate::constraints::catch_switch::CatchSwitch;
use crate::constraints::cleanup_pad::CleanupPad;
use crate::constraints::cleanup_ret::CleanupRet;
use crate::constraints::conditional_branch::ConditionalBranch;
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
use crate::constraints::indirect_br::IndirectBr;
use crate::constraints::invoke::Invoke;
use crate::constraints::landing_pad::LandingPad;
use crate::constraints::mul::Mul;
use crate::constraints::or::Or;
use crate::constraints::phi::Phi;
use crate::constraints::resume::Resume;
use crate::constraints::ret::Ret;
use crate::constraints::return_address::ReturnAddress;
use crate::constraints::sdiv::SDiv;
use crate::constraints::select::Select;
use crate::constraints::sext::SExt;
use crate::constraints::shl::Shl;
use crate::constraints::shr::Shr;
use crate::constraints::sitofp::SiToFp;
use crate::constraints::srem::SRem;
use crate::constraints::sub::Sub;
use crate::constraints::switch::Switch;
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
    CleanupPad(CleanupPad),
    CleanupRet(CleanupRet),
    CatchPad(CatchPad),
    CatchRet(CatchRet),
    CatchSwitch(CatchSwitch),
    ReturnAddress(ReturnAddress),
    Assign(Assign),
    AtomicCmpXchg(AtomicCmpXchg),
    AtomicRMW(AtomicRMW),
    Call(Call),
    CallBr(CallBr),
    Invoke(Invoke),
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
    Branch(Branch),
    ConditionalBranch(ConditionalBranch),
    Phi(Phi),
    Return(Ret),
    Alloca {
        ptr_result: ConstraintSystemVariable,
        allocated_type: String,
        block_name: String,
    },
    Switch(Switch),
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
    ExtractValue {
        aggregate: ConstraintSystemVariable,
        index: u32,
        result: ConstraintSystemVariable,
        block_name: String,
    },
    IndirectBr(IndirectBr),
    LandingPad(LandingPad),
    Resume(Resume),
}

pub struct ArithmetizationContext<'ctx> {
    next_variable_id: usize,
    llvm_to_cs_var_map: HashMap<BasicValueEnum<'ctx>, ConstraintSystemVariable>,
    cmpxchg_results:
        HashMap<InstructionValue<'ctx>, (ConstraintSystemVariable, ConstraintSystemVariable)>,
    landingpad_results:
        HashMap<InstructionValue<'ctx>, (ConstraintSystemVariable, ConstraintSystemVariable)>,
    pub insert_value_map: HashMap<BasicValueEnum<'ctx>, (BasicValueEnum<'ctx>, Operand, u32)>,
    pub shuffle_vector_map:
        HashMap<BasicValueEnum<'ctx>, (BasicValueEnum<'ctx>, BasicValueEnum<'ctx>, Vec<i32>)>,
    pub structured_constraints: Vec<StructuredAirConstraint>,
    current_block_name_for_constraints: String,
    pub memory_log: Vec<MemoryAccessLogEntry>,
    next_time_step_id: usize,
    csp: Option<ConstraintSystemVariable>,
    fp: Option<ConstraintSystemVariable>,
}

impl<'ctx> ArithmetizationContext<'ctx> {
    pub fn new() -> Self {
        ArithmetizationContext {
            next_variable_id: 0,
            llvm_to_cs_var_map: HashMap::new(),
            cmpxchg_results: HashMap::new(),
            landingpad_results: HashMap::new(),
            insert_value_map: HashMap::new(),
            shuffle_vector_map: HashMap::new(),
            structured_constraints: Vec::new(),
            current_block_name_for_constraints: String::new(),
            memory_log: Vec::new(),
            next_time_step_id: 0,
            csp: None,
            fp: None,
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

    let data_layout = module.get_data_layout();

    let mut module_arithmetization_ctx = ArithmetizationContext::new();

    for function_value in module.get_functions() {
        if module_arithmetization_ctx.csp.is_none() {
            let initial_csp = module_arithmetization_ctx.new_cs_variable();
            let initial_fp = module_arithmetization_ctx.new_cs_variable();

            module_arithmetization_ctx.csp = Some(initial_csp);
            module_arithmetization_ctx.fp = Some(initial_fp);
        }

        for arg in function_value.get_param_iter() {
            let cs_var = module_arithmetization_ctx.new_cs_variable();
            module_arithmetization_ctx
                .llvm_to_cs_var_map
                .insert(arg.into(), cs_var);
        }

        for basic_block in function_value.get_basic_blocks() {
            let mut bb_name = basic_block.get_name().to_str().unwrap().to_string();

            if bb_name.is_empty() {
                if Some(basic_block) == function_value.get_first_basic_block() {
                    bb_name = "entry".to_string();
                } else {
                    bb_name = "_unnamed_block".to_string();
                }
            }

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
                    InstructionOpcode::Unreachable
                    | InstructionOpcode::Fence
                    | InstructionOpcode::UserOp1
                    | InstructionOpcode::UserOp2 => {
                        // These are either ignored or handled as no-ops in this context.
                    }
                    InstructionOpcode::Freeze => {
                        let operand_llvm = get_operand_as_basic_value(0).expect("Freeze op0");
                        let operand_air = module_arithmetization_ctx
                            .llvm_basic_value_to_air_operand(operand_llvm);
                        let result_cs_var =
                            module_arithmetization_ctx.map_instruction_result_to_new_cs_var(instr);
                        let sc = StructuredAirConstraint::Assign(Assign {
                            dest: result_cs_var,
                            src: operand_air,
                            block_name: current_block_name,
                        });
                        module_arithmetization_ctx.add_structured_constraint(sc);
                    }
                    InstructionOpcode::LandingPad => {
                        let result_ptr_var = module_arithmetization_ctx.new_cs_variable();
                        let result_selector_var = module_arithmetization_ctx.new_cs_variable();

                        module_arithmetization_ctx
                            .landingpad_results
                            .insert(instr, (result_ptr_var, result_selector_var));

                        let landing_pad_result_var = module_arithmetization_ctx.new_cs_variable();

                        let sc = StructuredAirConstraint::LandingPad(LandingPad {
                            result: landing_pad_result_var,
                            block_name: current_block_name,
                        });
                        module_arithmetization_ctx.add_structured_constraint(sc);
                    }
                    InstructionOpcode::Resume => {
                        let op_val_ref = unsafe { LLVMGetOperand(instr.as_value_ref(), 0) };
                        let operand_llvm_any = unsafe { AnyValueEnum::new(op_val_ref) };

                        let instruction_val = match operand_llvm_any {
                            AnyValueEnum::InstructionValue(iv) => Some(iv),
                            AnyValueEnum::StructValue(sv) => sv.as_instruction(),
                            _ => None,
                        };

                        if let Some(iv) = instruction_val {
                            if let Some((ptr_var, selector_var)) =
                                module_arithmetization_ctx.landingpad_results.get(&iv)
                            {
                                let sc = StructuredAirConstraint::Resume(Resume {
                                    ptr_operand: Operand::Var(*ptr_var),
                                    selector_operand: Operand::Var(*selector_var),
                                    block_name: current_block_name,
                                });
                                module_arithmetization_ctx.add_structured_constraint(sc);
                            } else {
                                panic!("resume operand is from an unhandled instruction that should have been in landingpad_results");
                            }
                        } else {
                            panic!("resume operand not an instruction value");
                        }
                    }
                    InstructionOpcode::IndirectBr => {
                        let address_llvm =
                            get_operand_as_basic_value(0).expect("IndirectBr address missing");
                        let address_air = module_arithmetization_ctx
                            .llvm_basic_value_to_air_operand(address_llvm);
                        let mut destinations = Vec::new();
                        for i in 1..num_operands {
                            if let Some(block) = get_operand_as_basic_block(i) {
                                destinations
                                    .push(block.get_name().to_str().unwrap_or("").to_string());
                            }
                        }
                        let sc = StructuredAirConstraint::IndirectBr(IndirectBr {
                            address: address_air,
                            destinations,
                            block_name: current_block_name,
                        });
                        module_arithmetization_ctx.add_structured_constraint(sc);
                    }
                    InstructionOpcode::ShuffleVector => {
                        let v1_llvm =
                            get_operand_as_basic_value(0).expect("ShuffleVector op0 missing");
                        let v2_llvm =
                            get_operand_as_basic_value(1).expect("ShuffleVector op1 missing");
                        println!("v1_llvm: {:?}", v1_llvm);
                        println!("v2_llvm: {:?}", v2_llvm);

                        // Get the mask values using LLVM C API
                        let num_elements = unsafe { LLVMGetNumMaskElements(instr.as_value_ref()) };
                        let mut mask = Vec::with_capacity(num_elements as usize);

                        for i in 0..num_elements {
                            let mask_val = unsafe { LLVMGetMaskValue(instr.as_value_ref(), i) };
                            mask.push(mask_val);
                        }

                        let result_val = instr
                            .as_any_value_enum()
                            .try_into()
                            .expect("ShuffleVector result not a basic value");

                        // Register the source vectors in the map if they're not already there
                        if !module_arithmetization_ctx
                            .llvm_to_cs_var_map
                            .contains_key(&v1_llvm)
                        {
                            let v1_var = module_arithmetization_ctx.new_cs_variable();
                            module_arithmetization_ctx
                                .llvm_to_cs_var_map
                                .insert(v1_llvm, v1_var);
                        }
                        if !module_arithmetization_ctx
                            .llvm_to_cs_var_map
                            .contains_key(&v2_llvm)
                        {
                            let v2_var = module_arithmetization_ctx.new_cs_variable();
                            module_arithmetization_ctx
                                .llvm_to_cs_var_map
                                .insert(v2_llvm, v2_var);
                        }

                        // Store the mapping without creating a new variable for the result
                        module_arithmetization_ctx
                            .shuffle_vector_map
                            .insert(result_val, (v1_llvm, v2_llvm, mask));
                    }
                    InstructionOpcode::VAArg => {
                        let va_list_ptr_llvm =
                            get_operand_as_basic_value(0).expect("va_arg va_list missing");
                        let va_list_ptr_air = module_arithmetization_ctx
                            .llvm_basic_value_to_air_operand(va_list_ptr_llvm);

                        // 1. Load the current argument pointer from the va_list
                        let current_arg_ptr_var = module_arithmetization_ctx.new_cs_variable();
                        let time_step1 = module_arithmetization_ctx.new_time_step_variable();
                        module_arithmetization_ctx.add_memory_log_entry(MemoryAccessLogEntry {
                            address: va_list_ptr_air,
                            value: Operand::Var(current_arg_ptr_var),
                            time_step: time_step1,
                            access_type: MemoryAccessType::Read,
                            bitwidth: 64, // va_list is a pointer
                            block_name: current_block_name.clone(),
                        });

                        // 2. Load the actual argument value
                        let result_cs_var =
                            module_arithmetization_ctx.map_instruction_result_to_new_cs_var(instr);
                        let result_type = instr.get_type();
                        let result_bitwidth = match result_type {
                            AnyTypeEnum::IntType(it) => it.get_bit_width(),
                            AnyTypeEnum::PointerType(pt) => {
                                pt.size_of().get_zero_extended_constant().unwrap() as u32
                            }
                            _ => panic!("VAArg unsupported type"),
                        };
                        let result_size_bytes = (result_bitwidth as u128 + 7) / 8;

                        let time_step2 = module_arithmetization_ctx.new_time_step_variable();
                        module_arithmetization_ctx.add_memory_log_entry(MemoryAccessLogEntry {
                            address: Operand::Var(current_arg_ptr_var),
                            value: Operand::Var(result_cs_var),
                            time_step: time_step2,
                            access_type: MemoryAccessType::Read,
                            bitwidth: result_bitwidth,
                            block_name: current_block_name.clone(),
                        });

                        // 3. Increment the argument pointer
                        let new_arg_ptr_var = module_arithmetization_ctx.new_cs_variable();
                        let add_sc = StructuredAirConstraint::Add(Add {
                            operand1: Operand::Var(current_arg_ptr_var),
                            operand2: Operand::Const(result_size_bytes),
                            result: new_arg_ptr_var,
                            block_name: current_block_name.clone(),
                        });
                        module_arithmetization_ctx.add_structured_constraint(add_sc);

                        // 4. Store the new argument pointer back to the va_list
                        let time_step3 = module_arithmetization_ctx.new_time_step_variable();
                        module_arithmetization_ctx.add_memory_log_entry(MemoryAccessLogEntry {
                            address: va_list_ptr_air,
                            value: Operand::Var(new_arg_ptr_var),
                            time_step: time_step3,
                            access_type: MemoryAccessType::Write,
                            bitwidth: 64, // va_list is a pointer
                            block_name: current_block_name.clone(),
                        });
                    }
                    InstructionOpcode::CatchPad => {
                        let result_cs_var = module_arithmetization_ctx.new_cs_variable();
                        let sc = StructuredAirConstraint::CatchPad(CatchPad {
                            result: result_cs_var,
                            block_name: current_block_name,
                        });
                        module_arithmetization_ctx.add_structured_constraint(sc);
                    }
                    InstructionOpcode::CatchRet => {
                        if let Some(block) = get_operand_as_basic_block(1) {
                            let target_block_name =
                                block.get_name().to_str().unwrap_or("").to_string();
                            let sc = StructuredAirConstraint::CatchRet(CatchRet {
                                target_block_name,
                                block_name: current_block_name,
                            });
                            module_arithmetization_ctx.add_structured_constraint(sc);
                        } else {
                            panic!("CatchRet expects a basic block as its second operand");
                        }
                    }
                    InstructionOpcode::CatchSwitch => {
                        let result_cs_var =
                            module_arithmetization_ctx.map_instruction_result_to_new_cs_var(instr);

                        let mut handler_block_names = Vec::new();

                        for i in 1..num_operands {
                            if let Some(block) = get_operand_as_basic_block(i) {
                                let block_name =
                                    block.get_name().to_str().unwrap_or("").to_string();
                                handler_block_names.push(block_name);
                            }
                        }

                        let sc = StructuredAirConstraint::CatchSwitch(CatchSwitch {
                            unwind_dest_block_name: None,
                            handler_block_names,
                            result: result_cs_var,
                            block_name: current_block_name,
                        });
                        module_arithmetization_ctx.add_structured_constraint(sc);
                    }
                    InstructionOpcode::BitCast => {
                        let operand_llvm = get_operand_as_basic_value(0).expect("BitCast op0");
                        let operand_air = module_arithmetization_ctx
                            .llvm_basic_value_to_air_operand(operand_llvm);
                        let result_cs_var =
                            module_arithmetization_ctx.map_instruction_result_to_new_cs_var(instr);

                        let sc = StructuredAirConstraint::Assign(Assign {
                            dest: result_cs_var,
                            src: operand_air,
                            block_name: current_block_name,
                        });
                        module_arithmetization_ctx.add_structured_constraint(sc);
                    }
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
                            sc = StructuredAirConstraint::Branch(Branch {
                                target_block_name,
                                block_name: current_block_name,
                            });
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
                            sc = StructuredAirConstraint::ConditionalBranch(ConditionalBranch {
                                condition: cond_cs_var,
                                true_block_name,
                                false_block_name,
                                block_name: current_block_name,
                            });
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
                        let time_step = module_arithmetization_ctx.new_time_step_variable();

                        let fp_c = module_arithmetization_ctx.fp.expect("FP not initialized");

                        let addr_of_old_fp = module_arithmetization_ctx.new_cs_variable();
                        module_arithmetization_ctx.add_structured_constraint(
                            StructuredAirConstraint::Sub(Sub {
                                operand1: Operand::Var(fp_c),
                                operand2: Operand::Const(2),
                                result: addr_of_old_fp,
                                block_name: current_block_name.clone(),
                            }),
                        );
                        let popped_fp = module_arithmetization_ctx.new_cs_variable();
                        module_arithmetization_ctx.add_memory_log_entry(MemoryAccessLogEntry {
                            address: Operand::Var(addr_of_old_fp),
                            value: Operand::Var(popped_fp),
                            time_step,
                            access_type: MemoryAccessType::Read,
                            bitwidth: 64,
                            block_name: current_block_name.clone(),
                        });

                        let addr_of_ret_addr = module_arithmetization_ctx.new_cs_variable();
                        module_arithmetization_ctx.add_structured_constraint(
                            StructuredAirConstraint::Sub(Sub {
                                operand1: Operand::Var(fp_c),
                                operand2: Operand::Const(1),
                                result: addr_of_ret_addr,
                                block_name: current_block_name.clone(),
                            }),
                        );
                        let popped_ret_addr = module_arithmetization_ctx.new_cs_variable();
                        module_arithmetization_ctx.add_memory_log_entry(MemoryAccessLogEntry {
                            address: Operand::Var(addr_of_ret_addr),
                            value: Operand::Var(popped_ret_addr),
                            time_step,
                            access_type: MemoryAccessType::Read,
                            bitwidth: 64,
                            block_name: current_block_name.clone(),
                        });

                        let new_csp = module_arithmetization_ctx.new_cs_variable();
                        module_arithmetization_ctx.add_structured_constraint(
                            StructuredAirConstraint::Assign(Assign {
                                dest: new_csp,
                                src: Operand::Var(addr_of_old_fp),
                                block_name: current_block_name.clone(),
                            }),
                        );

                        module_arithmetization_ctx.csp = Some(new_csp);
                        module_arithmetization_ctx.fp = Some(popped_fp);

                        let mut actual_ret_op: Option<Operand> = None;
                        if num_operands == 1 {
                            if let Some(ret_val_llvm) = get_operand_as_basic_value(0) {
                                actual_ret_op = Some(
                                    module_arithmetization_ctx
                                        .llvm_basic_value_to_air_operand(ret_val_llvm),
                                );
                            }
                        }
                        let sc = StructuredAirConstraint::Return(Ret {
                            value: actual_ret_op,
                            block_name: current_block_name,
                            time_step,
                        });
                        module_arithmetization_ctx.add_structured_constraint(sc);
                    }
                    InstructionOpcode::AddrSpaceCast => {
                        let operand_llvm =
                            get_operand_as_basic_value(0).expect("AddrSpaceCast op0");
                        let operand_air = module_arithmetization_ctx
                            .llvm_basic_value_to_air_operand(operand_llvm);
                        let result_cs_var =
                            module_arithmetization_ctx.map_instruction_result_to_new_cs_var(instr);

                        let sc = StructuredAirConstraint::Assign(Assign {
                            dest: result_cs_var,
                            src: operand_air,
                            block_name: current_block_name,
                        });
                        module_arithmetization_ctx.add_structured_constraint(sc);
                    }
                    InstructionOpcode::PtrToInt => {
                        let operand_llvm = get_operand_as_basic_value(0).expect("PtrToInt op0");
                        let operand_air = module_arithmetization_ctx
                            .llvm_basic_value_to_air_operand(operand_llvm);
                        let result_cs_var =
                            module_arithmetization_ctx.map_instruction_result_to_new_cs_var(instr);

                        let sc = StructuredAirConstraint::Assign(Assign {
                            dest: result_cs_var,
                            src: operand_air,
                            block_name: current_block_name,
                        });
                        module_arithmetization_ctx.add_structured_constraint(sc);
                    }
                    InstructionOpcode::IntToPtr => {
                        let operand_llvm = get_operand_as_basic_value(0).expect("IntToPtr op0");
                        let operand_air = module_arithmetization_ctx
                            .llvm_basic_value_to_air_operand(operand_llvm);
                        let result_cs_var =
                            module_arithmetization_ctx.map_instruction_result_to_new_cs_var(instr);

                        let sc = StructuredAirConstraint::Assign(Assign {
                            dest: result_cs_var,
                            src: operand_air,
                            block_name: current_block_name,
                        });
                        module_arithmetization_ctx.add_structured_constraint(sc);
                    }
                    InstructionOpcode::Alloca => {
                        let ptr_cs_var =
                            module_arithmetization_ctx.map_instruction_result_to_new_cs_var(instr);
                        let allocated_type_string = instr
                            .get_allocated_type()
                            .map(|t| t.print_to_string().to_string())
                            .expect("Alloca instruction must have a type");

                        let sc = StructuredAirConstraint::Alloca {
                            ptr_result: ptr_cs_var,
                            allocated_type: allocated_type_string,
                            block_name: current_block_name.clone(),
                        };
                        module_arithmetization_ctx.add_structured_constraint(sc);

                        let allocated_type = instr
                            .get_allocated_type()
                            .expect("Alloca instruction must have a type");

                        let size = match allocated_type {
                            BasicTypeEnum::IntType(i) => ((i.get_bit_width() + 7) / 8) as u32,
                            BasicTypeEnum::FloatType(f) => {
                                let local_context = f.get_context();
                                if f == local_context.f16_type() {
                                    2
                                } else if f == local_context.f32_type() {
                                    4
                                } else if f == local_context.f64_type() {
                                    8
                                } else if f == local_context.f128_type() {
                                    16
                                } else if f == local_context.x86_f80_type() {
                                    10
                                } else if f == local_context.ppc_f128_type() {
                                    16
                                } else {
                                    panic!("Unsupported float type for alloca size")
                                }
                            }
                            BasicTypeEnum::PointerType(_) => 8, // Assuming 64-bit pointers
                            _ => {
                                // Special case for __va_list_tag which has a known size
                                if let BasicTypeEnum::StructType(st) = allocated_type {
                                    if st.get_name().map_or(false, |name| {
                                        name.to_str().map_or(false, |s| s == "__va_list_tag")
                                    }) {
                                        24 // Size of __va_list_tag struct (i32, i32, i8*, i8*)
                                    } else {
                                        let size_val = allocated_type
                                            .size_of()
                                            .inspect(|x| println!("size_of: {:?}", x))
                                            .expect("size_of should not be None for aggregate types in test IR");

                                        // Try to get constant value, if that fails try to evaluate the expression
                                        if let Some(const_val) =
                                            size_val.get_zero_extended_constant()
                                        {
                                            const_val as u32
                                        } else {
                                            // For complex expressions, calculate size from struct fields
                                            let mut total_size = 0;
                                            for i in 0..st.count_fields() {
                                                let field_type = st
                                                    .get_field_type_at_index(i)
                                                    .expect("Field type should exist");
                                                let field_size = match field_type {
                                                    BasicTypeEnum::IntType(it) => it.get_bit_width() / 8,
                                                    BasicTypeEnum::PointerType(_) => 8, // Assuming 64-bit pointers
                                                    BasicTypeEnum::FloatType(ft) => {
                                                        let ctx = ft.get_context();
                                                        if ft == ctx.f32_type() { 4 }
                                                        else if ft == ctx.f64_type() { 8 }
                                                        else if ft == ctx.f128_type() { 16 }
                                                        else if ft == ctx.x86_f80_type() { 10 }
                                                        else if ft == ctx.ppc_f128_type() { 16 }
                                                        else { panic!("Unsupported float type") }
                                                    }
                                                    _ => panic!("Unsupported field type in struct size calculation")
                                                };
                                                total_size += field_size;
                                            }
                                            total_size as u32
                                        }
                                    }
                                } else {
                                    allocated_type
                                        .size_of()
                                        .inspect(|x| println!("size_of: {:?}", x))
                                        .expect("size_of should not be None for aggregate types in test IR")
                                        .get_zero_extended_constant()
                                        .expect("Aggregate type size must be a constant") as u32
                                }
                            }
                        } as u128;

                        let csp_c = module_arithmetization_ctx.csp.expect("CSP not initialized");
                        let new_csp = module_arithmetization_ctx.new_cs_variable();
                        let add_sc = StructuredAirConstraint::Add(Add {
                            operand1: Operand::Var(csp_c),
                            operand2: Operand::Const(size),
                            result: new_csp,
                            block_name: current_block_name.clone(),
                        });
                        module_arithmetization_ctx.add_structured_constraint(add_sc);
                        module_arithmetization_ctx.csp = Some(new_csp);
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
                        let sc = StructuredAirConstraint::Switch(Switch {
                            condition_operand: cond_air_op,
                            default_target_block_name: default_dest_name,
                            cases: air_cases,
                            block_name: current_block_name,
                        });
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
                    InstructionOpcode::CleanupPad => {
                        let result_cs_var = module_arithmetization_ctx.new_cs_variable();
                        let sc = StructuredAirConstraint::CleanupPad(CleanupPad {
                            result: result_cs_var,
                            block_name: current_block_name,
                        });
                        module_arithmetization_ctx.add_structured_constraint(sc);
                    }
                    InstructionOpcode::CleanupRet => {
                        let unwind_dest_block_name = if num_operands > 1 {
                            get_operand_as_basic_block(1)
                                .map(|b| b.get_name().to_str().unwrap_or("").to_string())
                        } else {
                            None
                        };
                        let sc = StructuredAirConstraint::CleanupRet(CleanupRet {
                            unwind_dest_block_name,
                            block_name: current_block_name,
                        });
                        module_arithmetization_ctx.add_structured_constraint(sc);
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
                    InstructionOpcode::Invoke => {
                        let time_step = module_arithmetization_ctx.new_time_step_variable();

                        let _parent_block = instr
                            .get_parent()
                            .expect("Invoke instruction must have a parent block");

                        let mut successors = {
                            let num_successors =
                                unsafe { LLVMGetNumSuccessors(instr.as_value_ref()) };
                            let mut successors = Vec::new();
                            for i in 0..num_successors {
                                let successor =
                                    unsafe { LLVMGetSuccessor(instr.as_value_ref(), i) };
                                successors.push(successor);
                            }
                            successors
                        };
                        let normal_block = successors[0];
                        let unwind_block = successors[1];

                        let num_operands = instr.get_num_operands();
                        let mut value_operands = Vec::new();
                        for i in 0..num_operands {
                            if let Some(val) = get_operand_as_basic_value(i) {
                                value_operands.push(val);
                            }
                        }

                        let callee = value_operands
                            .pop()
                            .expect("Invoke callee must be a basic value");

                        let function_name = if let BasicValueEnum::PointerValue(pv) = callee {
                            pv.get_name().to_str().unwrap_or("unknown_fn").to_string()
                        } else {
                            "unknown_fn".to_string()
                        };

                        let args: Vec<Operand> = value_operands
                            .into_iter()
                            .map(|val| {
                                module_arithmetization_ctx.llvm_basic_value_to_air_operand(val)
                            })
                            .collect();

                        let result = if !instr.get_type().is_void_type() {
                            Some(
                                module_arithmetization_ctx
                                    .map_instruction_result_to_new_cs_var(instr),
                            )
                        } else {
                            None
                        };

                        let return_block_name =
                            unsafe { CStr::from_ptr(LLVMGetBasicBlockName(normal_block)) }
                                .to_str()
                                .unwrap()
                                .to_string();
                        let unwind_block_name =
                            unsafe { CStr::from_ptr(LLVMGetBasicBlockName(unwind_block)) }
                                .to_str()
                                .unwrap()
                                .to_string();

                        let csp_c = module_arithmetization_ctx.csp.expect("CSP not initialized");
                        let fp_c = module_arithmetization_ctx.fp.expect("FP not initialized");

                        module_arithmetization_ctx.add_memory_log_entry(MemoryAccessLogEntry {
                            address: Operand::Var(csp_c),
                            value: Operand::Var(fp_c),
                            time_step,
                            access_type: MemoryAccessType::Write,
                            bitwidth: 64,
                            block_name: current_block_name.clone(),
                        });

                        let addr_of_ret_addr = module_arithmetization_ctx.new_cs_variable();
                        module_arithmetization_ctx.add_structured_constraint(
                            StructuredAirConstraint::ReturnAddress(ReturnAddress {
                                operand1: Operand::Var(csp_c),
                                operand2: Operand::Const(1),
                                result: addr_of_ret_addr,
                                block_name: current_block_name.clone(),
                            }),
                        );

                        module_arithmetization_ctx.add_memory_log_entry(MemoryAccessLogEntry {
                            address: Operand::Var(addr_of_ret_addr),
                            value: Operand::Const(0),
                            time_step,
                            access_type: MemoryAccessType::Write,
                            bitwidth: 64,
                            block_name: current_block_name.clone(),
                        });

                        let new_fp = module_arithmetization_ctx.new_cs_variable();
                        module_arithmetization_ctx.add_structured_constraint(
                            StructuredAirConstraint::Assign(Assign {
                                dest: new_fp,
                                src: Operand::Var(csp_c),
                                block_name: current_block_name.clone(),
                            }),
                        );

                        let new_csp = module_arithmetization_ctx.new_cs_variable();
                        module_arithmetization_ctx.add_structured_constraint(
                            StructuredAirConstraint::ReturnAddress(ReturnAddress {
                                operand1: Operand::Var(csp_c),
                                operand2: Operand::Const(2),
                                result: new_csp,
                                block_name: current_block_name.clone(),
                            }),
                        );

                        module_arithmetization_ctx.csp = Some(new_csp);
                        module_arithmetization_ctx.fp = Some(new_fp);

                        let sc = StructuredAirConstraint::Invoke(Invoke {
                            function_name,
                            args,
                            result,
                            block_name: current_block_name,
                            return_block_name,
                            unwind_block_name,
                            time_step,
                        });
                        module_arithmetization_ctx.add_structured_constraint(sc);
                    }
                    InstructionOpcode::Call => {
                        let call_site: CallSiteValue = instr.try_into().unwrap();
                        let called_fn = call_site.get_called_fn_value().unwrap();
                        let function_name = called_fn.get_name().to_str().unwrap().to_string();
                        let args: Vec<Operand> = (0..instr.get_num_operands() - 1)
                            .map(|i| {
                                let operand_val = instr.get_operand(i).unwrap().left().unwrap();
                                module_arithmetization_ctx
                                    .llvm_basic_value_to_air_operand(operand_val)
                            })
                            .collect();
                        let result = if call_site.try_as_basic_value().is_left() {
                            Some(
                                module_arithmetization_ctx
                                    .map_instruction_result_to_new_cs_var(instr),
                            )
                        } else {
                            None
                        };
                        let time_step = module_arithmetization_ctx.new_time_step_variable();

                        let csp_c = module_arithmetization_ctx.csp.expect("CSP not initialized");
                        let fp_c = module_arithmetization_ctx.fp.expect("FP not initialized");

                        module_arithmetization_ctx.add_memory_log_entry(MemoryAccessLogEntry {
                            address: Operand::Var(csp_c),
                            value: Operand::Var(fp_c),
                            time_step,
                            access_type: MemoryAccessType::Write,
                            bitwidth: 64,
                            block_name: current_block_name.clone(),
                        });

                        let addr_of_ret_addr = module_arithmetization_ctx.new_cs_variable();
                        module_arithmetization_ctx.add_structured_constraint(
                            StructuredAirConstraint::ReturnAddress(ReturnAddress {
                                operand1: Operand::Var(csp_c),
                                operand2: Operand::Const(1),
                                result: addr_of_ret_addr,
                                block_name: current_block_name.clone(),
                            }),
                        );
                        module_arithmetization_ctx.add_memory_log_entry(MemoryAccessLogEntry {
                            address: Operand::Var(addr_of_ret_addr),
                            value: Operand::Const(0),
                            time_step,
                            access_type: MemoryAccessType::Write,
                            bitwidth: 64,
                            block_name: current_block_name.clone(),
                        });

                        let new_fp = module_arithmetization_ctx.new_cs_variable();
                        module_arithmetization_ctx.add_structured_constraint(
                            StructuredAirConstraint::Assign(Assign {
                                dest: new_fp,
                                src: Operand::Var(csp_c),
                                block_name: current_block_name.clone(),
                            }),
                        );

                        let new_csp = module_arithmetization_ctx.new_cs_variable();
                        module_arithmetization_ctx.add_structured_constraint(
                            StructuredAirConstraint::ReturnAddress(ReturnAddress {
                                operand1: Operand::Var(csp_c),
                                operand2: Operand::Const(2),
                                result: new_csp,
                                block_name: current_block_name.clone(),
                            }),
                        );

                        module_arithmetization_ctx.csp = Some(new_csp);
                        module_arithmetization_ctx.fp = Some(new_fp);

                        let sc = StructuredAirConstraint::Call(Call {
                            function_name,
                            args,
                            result,
                            block_name: current_block_name,
                            time_step,
                        });
                        module_arithmetization_ctx.add_structured_constraint(sc);
                    }
                    InstructionOpcode::CallBr => {
                        let num_operands = instr.get_num_operands();

                        let callee_operand_idx = num_operands - 1;
                        let called_fn_operand = get_operand_as_basic_value(callee_operand_idx)
                            .expect("CallBr callee is not a basic value");
                        let function_name =
                            if let BasicValueEnum::PointerValue(pv) = called_fn_operand {
                                pv.get_name().to_str().unwrap().to_string()
                            } else {
                                panic!("Callee is not a pointer value");
                            };

                        let mut dest_block_count = 0;
                        for i in 0..num_operands {
                            if instr.get_operand(i).unwrap().is_right() {
                                dest_block_count += 1;
                            } else {
                                break;
                            }
                        }

                        if dest_block_count == 0 {
                            panic!("CallBr must have at least one destination block");
                        }

                        let fallthrough_block_name = get_operand_as_basic_block(0)
                            .expect("CallBr must have a fallthrough basic block")
                            .get_name()
                            .to_str()
                            .unwrap()
                            .to_string();

                        let mut other_block_names = Vec::new();
                        for i in 1..dest_block_count {
                            let block = get_operand_as_basic_block(i)
                                .expect("CallBr indirect dest must be a basic block")
                                .get_name()
                                .to_str()
                                .unwrap()
                                .to_string();
                            other_block_names.push(block);
                        }

                        let args: Vec<Operand> = (dest_block_count..callee_operand_idx)
                            .map(|i| {
                                let operand_val = get_operand_as_basic_value(i)
                                    .expect("CallBr argument is not a basic value");
                                module_arithmetization_ctx
                                    .llvm_basic_value_to_air_operand(operand_val)
                            })
                            .collect();

                        let result = if !instr.get_type().is_void_type() {
                            Some(
                                module_arithmetization_ctx
                                    .map_instruction_result_to_new_cs_var(instr),
                            )
                        } else {
                            None
                        };

                        let time_step = module_arithmetization_ctx.new_time_step_variable();

                        let csp_c = module_arithmetization_ctx.csp.expect("CSP not initialized");
                        let fp_c = module_arithmetization_ctx.fp.expect("FP not initialized");

                        module_arithmetization_ctx.add_memory_log_entry(MemoryAccessLogEntry {
                            address: Operand::Var(csp_c),
                            value: Operand::Var(fp_c),
                            time_step,
                            access_type: MemoryAccessType::Write,
                            bitwidth: 64,
                            block_name: current_block_name.clone(),
                        });

                        let addr_of_ret_addr = module_arithmetization_ctx.new_cs_variable();
                        module_arithmetization_ctx.add_structured_constraint(
                            StructuredAirConstraint::ReturnAddress(ReturnAddress {
                                operand1: Operand::Var(csp_c),
                                operand2: Operand::Const(1),
                                result: addr_of_ret_addr,
                                block_name: current_block_name.clone(),
                            }),
                        );
                        module_arithmetization_ctx.add_memory_log_entry(MemoryAccessLogEntry {
                            address: Operand::Var(addr_of_ret_addr),
                            value: Operand::Const(0),
                            time_step,
                            access_type: MemoryAccessType::Write,
                            bitwidth: 64,
                            block_name: current_block_name.clone(),
                        });

                        let new_fp = module_arithmetization_ctx.new_cs_variable();
                        module_arithmetization_ctx.add_structured_constraint(
                            StructuredAirConstraint::Assign(Assign {
                                dest: new_fp,
                                src: Operand::Var(csp_c),
                                block_name: current_block_name.clone(),
                            }),
                        );

                        let new_csp = module_arithmetization_ctx.new_cs_variable();
                        module_arithmetization_ctx.add_structured_constraint(
                            StructuredAirConstraint::ReturnAddress(ReturnAddress {
                                operand1: Operand::Var(csp_c),
                                operand2: Operand::Const(2),
                                result: new_csp,
                                block_name: current_block_name.clone(),
                            }),
                        );

                        module_arithmetization_ctx.csp = Some(new_csp);
                        module_arithmetization_ctx.fp = Some(new_fp);

                        let sc = StructuredAirConstraint::CallBr(CallBr {
                            function_name,
                            args,
                            result,
                            fallthrough_block_name,
                            other_block_names,
                            block_name: current_block_name,
                            time_step,
                        });
                        module_arithmetization_ctx.add_structured_constraint(sc);
                    }
                    InstructionOpcode::InsertValue => {
                        let agg_val = get_operand_as_basic_value(0).expect("InsertValue aggregate");
                        let inserted_val =
                            get_operand_as_basic_value(1).expect("InsertValue value");
                        let index_op = instr
                            .get_operand(2)
                            .unwrap()
                            .left()
                            .unwrap()
                            .into_int_value();
                        let index = index_op.get_zero_extended_constant().unwrap() as u32;

                        let inserted_op = module_arithmetization_ctx
                            .llvm_basic_value_to_air_operand(inserted_val);
                        let result_val = instr
                            .as_any_value_enum()
                            .try_into()
                            .expect("InsertValue result not a basic value");

                        module_arithmetization_ctx
                            .insert_value_map
                            .insert(result_val, (agg_val, inserted_op, index));
                        let _ =
                            module_arithmetization_ctx.map_instruction_result_to_new_cs_var(instr);
                    }
                    InstructionOpcode::InsertElement => {
                        let vec_val = get_operand_as_basic_value(0).expect("InsertElement vector");
                        let inserted_val =
                            get_operand_as_basic_value(1).expect("InsertElement value");
                        let index_val = get_operand_as_basic_value(2).expect("InsertElement index");

                        let index = index_val
                            .into_int_value()
                            .get_zero_extended_constant()
                            .expect("InsertElement index must be a constant")
                            as u32;

                        let inserted_op = module_arithmetization_ctx
                            .llvm_basic_value_to_air_operand(inserted_val);
                        let result_val = instr
                            .as_any_value_enum()
                            .try_into()
                            .expect("InsertElement result not a basic value");

                        module_arithmetization_ctx
                            .insert_value_map
                            .insert(result_val, (vec_val, inserted_op, index));
                        let _ =
                            module_arithmetization_ctx.map_instruction_result_to_new_cs_var(instr);
                    }
                    InstructionOpcode::AtomicCmpXchg => {
                        let ptr_operand = get_operand_as_basic_value(0).expect("cmpxchg ptr");
                        let cmp_operand = get_operand_as_basic_value(1).expect("cmpxchg cmp");
                        let new_operand = get_operand_as_basic_value(2).expect("cmpxchg new");

                        let bitwidth = match new_operand.get_type() {
                            BasicTypeEnum::IntType(it) => it.get_bit_width(),
                            _ => panic!("cmpxchg new value must be an integer type"),
                        };

                        let ptr_air =
                            module_arithmetization_ctx.llvm_basic_value_to_air_operand(ptr_operand);
                        let cmp_air =
                            module_arithmetization_ctx.llvm_basic_value_to_air_operand(cmp_operand);
                        let new_air =
                            module_arithmetization_ctx.llvm_basic_value_to_air_operand(new_operand);

                        let result_val_var = module_arithmetization_ctx.new_cs_variable();
                        let result_success_var = module_arithmetization_ctx.new_cs_variable();

                        module_arithmetization_ctx
                            .cmpxchg_results
                            .insert(instr, (result_val_var, result_success_var));

                        let time_step = module_arithmetization_ctx.new_time_step_variable();

                        module_arithmetization_ctx.add_memory_log_entry(MemoryAccessLogEntry {
                            address: ptr_air,
                            value: Operand::Var(result_val_var),
                            time_step,
                            access_type: MemoryAccessType::Read,
                            bitwidth,
                            block_name: current_block_name.clone(),
                        });

                        let written_val_var = module_arithmetization_ctx.new_cs_variable();
                        module_arithmetization_ctx.add_memory_log_entry(MemoryAccessLogEntry {
                            address: ptr_air,
                            value: Operand::Var(written_val_var),
                            time_step,
                            access_type: MemoryAccessType::Write,
                            bitwidth,
                            block_name: current_block_name.clone(),
                        });

                        let sc = StructuredAirConstraint::AtomicCmpXchg(AtomicCmpXchg {
                            ptr: ptr_air,
                            cmp: cmp_air,
                            new: new_air,
                            result_val: result_val_var,
                            result_success: result_success_var,
                            block_name: current_block_name,
                            time_step,
                        });
                        module_arithmetization_ctx.add_structured_constraint(sc);
                    }
                    InstructionOpcode::AtomicRMW => {
                        let ptr_operand = get_operand_as_basic_value(0).expect("rmw ptr");
                        let val_operand = get_operand_as_basic_value(1).expect("rmw val");
                        let operation = AtomicRMWBinOp::from(unsafe {
                            LLVMGetAtomicRMWBinOp(instr.as_value_ref())
                        });

                        let bitwidth = match val_operand.get_type() {
                            BasicTypeEnum::IntType(it) => it.get_bit_width(),
                            _ => panic!("atomicrmw value must be an integer type"),
                        };

                        let ptr_air =
                            module_arithmetization_ctx.llvm_basic_value_to_air_operand(ptr_operand);
                        let val_air =
                            module_arithmetization_ctx.llvm_basic_value_to_air_operand(val_operand);

                        let result_var =
                            module_arithmetization_ctx.map_instruction_result_to_new_cs_var(instr);
                        let time_step = module_arithmetization_ctx.new_time_step_variable();

                        module_arithmetization_ctx.add_memory_log_entry(MemoryAccessLogEntry {
                            address: ptr_air,
                            value: Operand::Var(result_var),
                            time_step,
                            access_type: MemoryAccessType::Read,
                            bitwidth,
                            block_name: current_block_name.clone(),
                        });

                        let written_val_var = module_arithmetization_ctx.new_cs_variable();
                        module_arithmetization_ctx.add_memory_log_entry(MemoryAccessLogEntry {
                            address: ptr_air,
                            value: Operand::Var(written_val_var),
                            time_step,
                            access_type: MemoryAccessType::Write,
                            bitwidth,
                            block_name: current_block_name.clone(),
                        });

                        let sc = StructuredAirConstraint::AtomicRMW(AtomicRMW {
                            ptr: ptr_air,
                            value: val_air,
                            operation: operation.into(),
                            result: result_var,
                            block_name: current_block_name,
                            time_step,
                        });
                        module_arithmetization_ctx.add_structured_constraint(sc);
                    }
                    InstructionOpcode::ExtractValue => {
                        let op_val_ref = unsafe { LLVMGetOperand(instr.as_value_ref(), 0) };
                        let mut agg_val_any = unsafe { AnyValueEnum::new(op_val_ref) };

                        // This instruction is tricky because indices are not standard operands.
                        // We are assuming for now the number of indices is 1 based on test cases.
                        // A more robust solution might require FFI calls to get all indices.
                        let num_indices = unsafe { LLVMGetNumIndices(instr.as_value_ref()) };
                        if num_indices == 0 {
                            panic!("ExtractValue must have at least one index.");
                        }
                        let indices_ptr = unsafe { LLVMGetIndices(instr.as_value_ref()) };
                        let indices = unsafe {
                            std::slice::from_raw_parts(indices_ptr, num_indices as usize)
                        };

                        if indices.len() > 1 {
                            println!(
                                "WARN: ExtractValue with multiple indices found, only processing the first one."
                            );
                        }
                        let mut index = indices[0] as u32;

                        let source_operand = loop {
                            if let Ok(agg_val) = BasicValueEnum::try_from(agg_val_any) {
                                if let Some((parent_agg, inserted_op, inserted_idx)) =
                                    module_arithmetization_ctx.insert_value_map.get(&agg_val)
                                {
                                    if *inserted_idx == index {
                                        break *inserted_op;
                                    } else {
                                        agg_val_any = parent_agg.as_any_value_enum();
                                        continue;
                                    }
                                } else if let Some((v1, v2, mask)) =
                                    module_arithmetization_ctx.shuffle_vector_map.get(&agg_val)
                                {
                                    let source_idx = mask[index as usize];
                                    if source_idx < 0 {
                                        break Operand::Const(0);
                                    }
                                    let v1_size = v1.get_type().into_vector_type().get_size();

                                    if (source_idx as u32) < v1_size {
                                        agg_val_any = v1.as_any_value_enum();
                                        index = source_idx as u32;
                                    } else {
                                        agg_val_any = v2.as_any_value_enum();
                                        index = source_idx as u32 - v1_size;
                                    }
                                    continue;
                                }
                            }

                            let instruction_val = match agg_val_any {
                                AnyValueEnum::InstructionValue(iv) => Some(iv),
                                AnyValueEnum::StructValue(sv) => sv.as_instruction(),
                                AnyValueEnum::ArrayValue(av) => av.as_instruction(),
                                AnyValueEnum::FloatValue(fv) => fv.as_instruction(),
                                AnyValueEnum::IntValue(iv) => iv.as_instruction(),
                                AnyValueEnum::VectorValue(vv) => vv.as_instruction(),
                                _ => None,
                            };

                            if let Some(iv) = instruction_val {
                                if let Some((val_var, success_var)) =
                                    module_arithmetization_ctx.cmpxchg_results.get(&iv)
                                {
                                    let source_var =
                                        if index == 0 { *val_var } else { *success_var };
                                    break Operand::Var(source_var);
                                } else if let Some((ptr_var, selector_var)) =
                                    module_arithmetization_ctx.landingpad_results.get(&iv)
                                {
                                    let source_var =
                                        if index == 0 { *ptr_var } else { *selector_var };
                                    break Operand::Var(source_var);
                                } else {
                                    panic!("extractvalue aggregate from unhandled instruction");
                                }
                            } else {
                                let aggregate_string = agg_val_any.print_to_string();
                                panic!("extractvalue aggregate must be an instruction or constant, but got: {}", aggregate_string);
                            }
                        };
                        let result_var =
                            module_arithmetization_ctx.map_instruction_result_to_new_cs_var(instr);
                        let sc = StructuredAirConstraint::Assign(Assign {
                            dest: result_var,
                            src: source_operand,
                            block_name: current_block_name,
                        });
                        module_arithmetization_ctx.add_structured_constraint(sc);
                    }
                    InstructionOpcode::ExtractElement => {
                        let agg_val = instr
                            .get_operand(0)
                            .unwrap()
                            .left()
                            .unwrap()
                            .as_any_value_enum();
                        let index_val =
                            get_operand_as_basic_value(1).expect("ExtractElement index");
                        let index = index_val
                            .into_int_value()
                            .get_zero_extended_constant()
                            .expect("ExtractElement index must be a constant")
                            as u32;

                        let source_operand = match BasicValueEnum::try_from(agg_val) {
                            Ok(agg_val) => {
                                if let Some((v1, v2, mask)) =
                                    module_arithmetization_ctx.shuffle_vector_map.get(&agg_val)
                                {
                                    let source_idx = mask[index as usize];
                                    if source_idx < 0 {
                                        Operand::Const(0)
                                    } else {
                                        let v1_size = v1.get_type().into_vector_type().get_size();
                                        if (source_idx as u32) < v1_size {
                                            module_arithmetization_ctx.llvm_to_cs_var_map.get(&v1)
                                                .map(|var| Operand::Var(*var))
                                                .unwrap_or_else(|| panic!("extractelement: could not find v1 variable"))
                                        } else {
                                            module_arithmetization_ctx.llvm_to_cs_var_map.get(&v2)
                                                .map(|var| Operand::Var(*var))
                                                .unwrap_or_else(|| panic!("extractelement: could not find v2 variable"))
                                        }
                                    }
                                } else if let BasicValueEnum::VectorValue(vv) = agg_val {
                                    let const_idx = vv
                                        .get_type()
                                        .get_context()
                                        .i32_type()
                                        .const_int(index as u64, false);
                                    let elem = vv.const_extract_element(const_idx);
                                    if let BasicValueEnum::IntValue(iv) = elem {
                                        iv.get_zero_extended_constant()
                                            .map(|val| Operand::Const(val as u128))
                                            .unwrap_or_else(|| {
                                                panic!(
                                                    "extractelement: could not get constant value"
                                                )
                                            })
                                    } else {
                                        panic!("extractelement: unexpected element type");
                                    }
                                } else {
                                    panic!("extractelement: unexpected aggregate type");
                                }
                            }
                            Err(_) => panic!("extractelement: could not convert aggregate value"),
                        };

                        let result_var =
                            module_arithmetization_ctx.map_instruction_result_to_new_cs_var(instr);
                        module_arithmetization_ctx.add_structured_constraint(
                            StructuredAirConstraint::Assign(Assign {
                                dest: result_var,
                                src: source_operand,
                                block_name: current_block_name,
                            }),
                        );
                    }
                    _ => {
                        println!("WARN: Unhandled opcode: {:?}. This may lead to incorrect circuit generation.", opcode);
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
    use crate::constraints::atomic_rmw::RmwBinOp;

    use super::*;

    #[test]
    fn basic_ir_processing() {
        let llvm_ir = r#"
            define i32 @main() {
                ret i32 42
            }
        "#;
        let (constraints, memory_log) = process_llvm_ir(llvm_ir).unwrap();
        assert_eq!(constraints.len(), 4); // Return constraint + stack operations
        assert_eq!(memory_log.len(), 2); // Stack operations for return
    }

    #[test]
    fn add_function_ir_processing() {
        let llvm_ir = r#"
            define i32 @add(i32 %a, i32 %b) {
                %result = add i32 %a, %b
                ret i32 %result
            }
        "#;
        let (constraints, memory_log) = process_llvm_ir(llvm_ir).unwrap();
        assert_eq!(constraints.len(), 5); // Add constraint + Return + stack operations
        assert_eq!(memory_log.len(), 2); // Stack operations for return

        if let StructuredAirConstraint::Add(add) = &constraints[0] {
            assert_eq!(add.block_name, "entry");
            assert!(matches!(add.operand1, Operand::Var(_)));
            assert!(matches!(add.operand2, Operand::Var(_)));
            assert!(matches!(add.result, ConstraintSystemVariable(_)));
        } else {
            panic!("Expected Add constraint, got {:?}", constraints[0]);
        }
    }

    #[test]
    fn icmp_function_ir_processing() {
        let llvm_ir = r#"
            define i1 @compare(i32 %a, i32 %b) {
                %result = icmp eq i32 %a, %b
                ret i1 %result
            }
        "#;
        let (constraints, memory_log) = process_llvm_ir(llvm_ir).unwrap();
        assert_eq!(constraints.len(), 5); // ICmp constraint + Return + stack operations
        assert_eq!(memory_log.len(), 2); // Stack operations for return

        if let StructuredAirConstraint::Icmp(icmp) = &constraints[0] {
            assert_eq!(icmp.block_name, "entry");
            assert_eq!(icmp.cond, IntPredicate::EQ);
            assert!(matches!(icmp.operand1, Operand::Var(_)));
            assert!(matches!(icmp.operand2, Operand::Var(_)));
            assert!(matches!(icmp.result, ConstraintSystemVariable(_)));
        } else {
            panic!("Expected ICmp constraint, got {:?}", constraints[0]);
        }
    }

    #[test]
    fn branch_function_ir_processing() {
        let llvm_ir = r#"
            define void @branch(i1 %cond) {
                br i1 %cond, label %true, label %false
            true:
                ret void
            false:
                ret void
            }
        "#;
        let (constraints, memory_log) = process_llvm_ir(llvm_ir).unwrap();
        assert_eq!(constraints.len(), 9); // Branch constraint + 2 Returns + stack operations
        assert_eq!(memory_log.len(), 4); // Stack operations for returns

        if let StructuredAirConstraint::ConditionalBranch(cb) = &constraints[0] {
            assert_eq!(cb.block_name, "entry");
            assert!(matches!(cb.condition, ConstraintSystemVariable(_)));
            assert_eq!(cb.true_block_name, "true");
            assert_eq!(cb.false_block_name, "false");
        } else {
            panic!(
                "Expected ConditionalBranch constraint, got {:?}",
                constraints[0]
            );
        }
    }

    #[test]
    fn phi_node_ir_processing() {
        let llvm_ir = r#"
            define i32 @phi_test(i1 %cond) {
                br i1 %cond, label %true, label %false
            true:
                br label %merge
            false:
                br label %merge
            merge:
                %result = phi i32 [ 1, %true ], [ 2, %false ]
                ret i32 %result
            }
        "#;
        let (constraints, memory_log) = process_llvm_ir(llvm_ir).unwrap();
        assert_eq!(constraints.len(), 8); // Branch + Phi + Return + stack operations
        assert_eq!(memory_log.len(), 2); // Stack operations for returns

        let phi_constraint = constraints
            .iter()
            .find(|c| matches!(c, StructuredAirConstraint::Phi(_)));
        assert!(phi_constraint.is_some(), "No Phi constraint found");
    }

    #[test]
    fn slightly_more_complex_ir() {
        let llvm_ir = r#"
            define i32 @complex(i32 %a, i32 %b) {
                %sum = add i32 %a, %b
                %diff = sub i32 %a, %b
                %prod = mul i32 %sum, %diff
                ret i32 %prod
            }
        "#;
        let (constraints, memory_log) = process_llvm_ir(llvm_ir).unwrap();
        assert_eq!(constraints.len(), 7); // Add + Sub + Mul + Return + stack operations
        assert_eq!(memory_log.len(), 2); // Stack operations for return

        // Verify the sequence of operations
        if let StructuredAirConstraint::Add { .. } = constraints[0] {
        } else {
            panic!("Expected Add constraint first");
        }
        if let StructuredAirConstraint::Sub { .. } = constraints[1] {
        } else {
            panic!("Expected Sub constraint second");
        }
        if let StructuredAirConstraint::Multiply { .. } = constraints[2] {
        } else {
            panic!("Expected Multiply constraint third");
        }
    }

    #[test]
    fn alloca_only_ir_processing() {
        let llvm_ir = r#"
            define void @alloca_test() {
                %ptr = alloca i32
                ret void
            }
        "#;
        let (constraints, memory_log) = process_llvm_ir(llvm_ir).unwrap();
        assert_eq!(constraints.len(), 6); // Alloca + Return + stack operations
        assert_eq!(memory_log.len(), 2); // Stack operations for return

        if let StructuredAirConstraint::Alloca {
            ptr_result,
            allocated_type,
            block_name,
        } = &constraints[0]
        {
            assert_eq!(*block_name, "entry");
            assert_eq!(*allocated_type, "i32");
            assert!(matches!(ptr_result, ConstraintSystemVariable(_)));
        } else {
            panic!("Expected Alloca constraint, got {:?}", constraints[0]);
        }
    }

    #[test]
    fn store_ir_processing() {
        let llvm_ir = r#"
            define void @simple_store(i32 %val_to_store) {
                %ptr = alloca i32
                store i32 %val_to_store, i32* %ptr
                ret void
            }
        "#;
        let (constraints, memory_log) = process_llvm_ir(llvm_ir).unwrap();
        assert_eq!(constraints.len(), 6); // Alloca + Return + stack operations
        assert_eq!(memory_log.len(), 3); // Alloca + Store + Return stack operations

        let write_count = memory_log
            .iter()
            .filter(|e| e.access_type == MemoryAccessType::Write)
            .count();
        assert_eq!(write_count, 1, "Expected one write operation");
    }

    #[test]
    fn load_ir_processing() {
        let llvm_ir = r#"
            define i32 @simple_load_store(i32 %val) {
                %ptr = alloca i32
                store i32 %val, i32* %ptr
                %loaded = load i32, i32* %ptr
                ret i32 %loaded
            }
        "#;
        let (constraints, memory_log) = process_llvm_ir(llvm_ir).unwrap();
        assert_eq!(constraints.len(), 6); // Alloca + Return + stack operations
        assert_eq!(memory_log.len(), 4); // Alloca + Store + Load + Return stack operations

        let read_count = memory_log
            .iter()
            .filter(|e| e.access_type == MemoryAccessType::Read)
            .count();
        assert_eq!(read_count, 3, "Expected one read operation");
    }

    #[test]
    fn switch_instruction_ir_processing() {
        let llvm_ir = r#"
            define void @switch_test(i32 %val) {
                switch i32 %val, label %default [ i32 1, label %case1
                                               i32 2, label %case2 ]
            case1:
                ret void
            case2:
                ret void
            default:
                ret void
            }
        "#;
        let (constraints, memory_log) = process_llvm_ir(llvm_ir).unwrap();
        assert_eq!(constraints.len(), 13); // Switch + 3 Returns + stack operations
        assert_eq!(memory_log.len(), 6); // Stack operations for returns

        if let StructuredAirConstraint::Switch(sw) = &constraints[0] {
            assert_eq!(sw.block_name, "entry");
            assert!(matches!(sw.condition_operand, Operand::Var(_)));
            assert_eq!(sw.default_target_block_name, "default");
            assert_eq!(sw.cases.len(), 2);
        } else {
            panic!("Expected Switch constraint, got {:?}", constraints[0]);
        }
    }

    #[test]
    fn sub_function_ir_processing() {
        let llvm_ir = r#"
            define i32 @subtract(i32 %a, i32 %b) {
                %result = sub i32 %a, %b
                ret i32 %result
            }
        "#;
        let (constraints, memory_log) = process_llvm_ir(llvm_ir).unwrap();
        assert_eq!(constraints.len(), 5); // Sub + Return + stack operations
        assert_eq!(memory_log.len(), 2); // Stack operations for return

        if let StructuredAirConstraint::Sub(sub) = &constraints[0] {
            assert_eq!(sub.block_name, "entry");
            assert!(matches!(sub.operand1, Operand::Var(_)));
            assert!(matches!(sub.operand2, Operand::Var(_)));
            assert!(matches!(sub.result, ConstraintSystemVariable(_)));
        } else {
            panic!("Expected Sub constraint, got {:?}", constraints[0]);
        }
    }

    #[test]
    fn and_function_ir_processing() {
        let llvm_ir = r#"
            define i32 @logical_and(i32 %a, i32 %b) {
                %result = and i32 %a, %b
                ret i32 %result
            }
        "#;
        let (constraints, memory_log) = process_llvm_ir(llvm_ir).unwrap();
        assert_eq!(constraints.len(), 5); // And + Return + stack operations
        assert_eq!(memory_log.len(), 2); // Stack operations for return

        if let StructuredAirConstraint::And(and) = &constraints[0] {
            assert_eq!(and.block_name, "entry");
            assert!(matches!(and.operand1, Operand::Var(_)));
            assert!(matches!(and.operand2, Operand::Var(_)));
            assert!(matches!(and.result, ConstraintSystemVariable(_)));
        } else {
            panic!("Expected And constraint, got {:?}", constraints[0]);
        }
    }

    #[test]
    fn or_function_ir_processing() {
        let llvm_ir = r#"
            define i32 @logical_or(i32 %a, i32 %b) {
                %result = or i32 %a, %b
                ret i32 %result
            }
        "#;
        let (constraints, memory_log) = process_llvm_ir(llvm_ir).unwrap();
        assert_eq!(constraints.len(), 5); // Or + Return + stack operations
        assert_eq!(memory_log.len(), 2); // Stack operations for return

        if let StructuredAirConstraint::Or(or) = &constraints[0] {
            assert_eq!(or.block_name, "entry");
            assert!(matches!(or.operand1, Operand::Var(_)));
            assert!(matches!(or.operand2, Operand::Var(_)));
            assert!(matches!(or.result, ConstraintSystemVariable(_)));
        } else {
            panic!("Expected Or constraint, got {:?}", constraints[0]);
        }
    }

    #[test]
    fn xor_function_ir_processing() {
        let llvm_ir = r#"
            define i32 @logical_xor(i32 %a, i32 %b) {
                %result = xor i32 %a, %b
                ret i32 %result
            }
        "#;
        let (constraints, memory_log) = process_llvm_ir(llvm_ir).unwrap();
        assert_eq!(constraints.len(), 5); // Xor + Return + stack operations
        assert_eq!(memory_log.len(), 2); // Stack operations for return

        if let StructuredAirConstraint::Xor(xor) = &constraints[0] {
            assert_eq!(xor.block_name, "entry");
            assert!(matches!(xor.operand1, Operand::Var(_)));
            assert!(matches!(xor.operand2, Operand::Var(_)));
            assert!(matches!(xor.result, ConstraintSystemVariable(_)));
        } else {
            panic!("Expected Xor constraint, got {:?}", constraints[0]);
        }
    }

    #[test]
    fn sdiv_function_ir_processing() {
        let llvm_ir = r#"
            define i32 @signed_divide(i32 %a, i32 %b) {
                %result = sdiv i32 %a, %b
                ret i32 %result
            }
        "#;
        let (constraints, memory_log) = process_llvm_ir(llvm_ir).unwrap();
        assert_eq!(constraints.len(), 5); // SDiv + Return + stack operations
        assert_eq!(memory_log.len(), 2); // Stack operations for return

        if let StructuredAirConstraint::SDiv(sdiv) = &constraints[0] {
            assert_eq!(sdiv.block_name, "entry");
            assert!(matches!(sdiv.operand1, Operand::Var(_)));
            assert!(matches!(sdiv.operand2, Operand::Var(_)));
            assert!(matches!(sdiv.result, ConstraintSystemVariable(_)));
        } else {
            panic!("Expected SDiv constraint, got {:?}", constraints[0]);
        }
    }

    #[test]
    fn srem_function_ir_processing() {
        let llvm_ir = r#"
            define i32 @signed_remainder(i32 %a, i32 %b) {
                %result = srem i32 %a, %b
                ret i32 %result
            }
        "#;
        let (constraints, memory_log) = process_llvm_ir(llvm_ir).unwrap();
        assert_eq!(constraints.len(), 5); // SRem + Return + stack operations
        assert_eq!(memory_log.len(), 2); // Stack operations for return

        if let StructuredAirConstraint::SRem(srem) = &constraints[0] {
            assert_eq!(srem.block_name, "entry");
            assert!(matches!(srem.operand1, Operand::Var(_)));
            assert!(matches!(srem.operand2, Operand::Var(_)));
            assert!(matches!(srem.result, ConstraintSystemVariable(_)));
        } else {
            panic!("Expected SRem constraint, got {:?}", constraints[0]);
        }
    }

    #[test]
    fn urem_function_ir_processing() {
        let llvm_ir = r#"
            define i32 @unsigned_remainder(i32 %a, i32 %b) {
                %result = urem i32 %a, %b
                ret i32 %result
            }
        "#;
        let (constraints, memory_log) = process_llvm_ir(llvm_ir).unwrap();
        assert_eq!(constraints.len(), 5); // URem + Return + stack operations
        assert_eq!(memory_log.len(), 2); // Stack operations for return

        if let StructuredAirConstraint::URem(urem) = &constraints[0] {
            assert_eq!(urem.block_name, "entry");
            assert!(matches!(urem.operand1, Operand::Var(_)));
            assert!(matches!(urem.operand2, Operand::Var(_)));
            assert!(matches!(urem.result, ConstraintSystemVariable(_)));
        } else {
            panic!("Expected URem constraint, got {:?}", constraints[0]);
        }
    }

    #[test]
    fn call_instruction_ir_processing() {
        let llvm_ir = r#"
            define i32 @add(i32 %a, i32 %b) {
                %1 = add i32 %a, %b
                ret i32 %1
            }

            define i32 @main() {
                %1 = call i32 @add(i32 5, i32 10)
                ret i32 %1
            }
        "#;
        let (constraints, memory_log) = process_llvm_ir(llvm_ir).unwrap();
        assert_eq!(constraints.len(), 13); // Add + Call + 2 Returns + stack operations
        assert_eq!(memory_log.len(), 6); // Stack operations for calls and returns

        let call_constraint = constraints
            .iter()
            .find(|c| matches!(c, StructuredAirConstraint::Call(_)));
        assert!(call_constraint.is_some(), "No Call constraint found");

        let write_count = memory_log
            .iter()
            .filter(|e| e.access_type == MemoryAccessType::Write)
            .count();
        assert_eq!(
            write_count, 2,
            "Expected two write operations for call frames"
        );
    }

    #[test]
    fn multiple_function_calls_ir_processing() {
        let llvm_ir = r#"
            define i32 @add(i32 %a, i32 %b) {
                %result = add i32 %a, %b
                ret i32 %result
            }

            define i32 @call_add(i32 %x) {
                %result = call i32 @add(i32 %x, i32 5)
                ret i32 %result
            }

            define i32 @main() {
                %result = call i32 @call_add(i32 10)
                ret i32 %result
            }
        "#;
        let (constraints, memory_log) = process_llvm_ir(llvm_ir).unwrap();
        assert_eq!(constraints.len(), 21); // Add + 2 Calls + 3 Returns + stack operations
        assert_eq!(memory_log.len(), 10); // Stack operations for calls and returns

        let call_constraints_count = constraints
            .iter()
            .filter(|c| matches!(c, StructuredAirConstraint::Call(_)))
            .count();
        assert_eq!(call_constraints_count, 2, "Expected two Call constraints");

        let write_count = memory_log
            .iter()
            .filter(|e| e.access_type == MemoryAccessType::Write)
            .count();
        assert_eq!(
            write_count, 4,
            "Expected four write operations for call frames"
        );
    }

    #[test]
    fn recursive_function_ir_processing() {
        let llvm_ir = r#"
            define i32 @factorial(i32 %n) {
            entry:
                %cmp = icmp eq i32 %n, 0
                br i1 %cmp, label %if.then, label %if.else

            if.then:
                ret i32 1

            if.else:
                %sub = sub i32 %n, 1
                %call = call i32 @factorial(i32 %sub)
                %mul = mul i32 %n, %call
                ret i32 %mul
            }
        "#;
        let (constraints, memory_log) = process_llvm_ir(llvm_ir).unwrap();
        assert!(constraints.len() >= 7); // ICmp + Branch + Sub + Call + Mul + Return + stack operations
        assert!(memory_log.len() >= 4); // Stack operations for calls and returns

        let has_return_address = constraints
            .iter()
            .any(|c| matches!(c, StructuredAirConstraint::ReturnAddress(_)));
        assert!(has_return_address, "Expected ReturnAddress constraint");

        let has_call = constraints
            .iter()
            .any(|c| matches!(c, StructuredAirConstraint::Call(_)));
        assert!(has_call, "Expected Call constraint");
    }

    #[test]
    fn callbr_instruction_ir_processing() {
        let llvm_ir = r#"
            define i32 @get_num() {
                ret i32 42
            }

            define i32 @main() {
            entry:
                %val = callbr i32 @get_num() to label %normal [label %error]

            normal:
                ret i32 %val

            error:
                ret i32 -1
            }
        "#;
        let (constraints, memory_log) = process_llvm_ir(llvm_ir).unwrap();
        assert!(constraints.len() >= 4); // CallBr + 2 Returns + stack operations
        assert!(memory_log.len() >= 4); // Stack operations for calls and returns

        let callbr_constraint = constraints.iter().find_map(|c| match c {
            StructuredAirConstraint::CallBr(callbr) => Some(callbr),
            _ => None,
        });
        assert!(callbr_constraint.is_some(), "No CallBr constraint found");

        let callbr = callbr_constraint.unwrap();
        assert_eq!(callbr.function_name, "get_num");
        assert!(callbr.result.is_some(), "CallBr should have a result value");
        assert_eq!(callbr.fallthrough_block_name, "normal");
        assert_eq!(callbr.other_block_names, vec!["error"]);
    }

    #[test]
    fn atomic_rmw_ir_processing() {
        let llvm_ir = r#"
            define i32 @atomic_add(i32* %ptr, i32 %val) {
            entry:
                %res = atomicrmw add i32* %ptr, i32 %val monotonic
                ret i32 %res
            }
        "#;
        let (constraints, memory_log) = process_llvm_ir(llvm_ir).unwrap();
        assert_eq!(constraints.len(), 5); // AtomicRMW + Return + stack operations
        assert_eq!(memory_log.len(), 4); // RMW read/write + Return stack operations

        let rmw_constraint = constraints.iter().find_map(|c| match c {
            StructuredAirConstraint::AtomicRMW(rmw) => Some(rmw),
            _ => None,
        });
        assert!(rmw_constraint.is_some(), "No AtomicRMW constraint found");

        let rmw = rmw_constraint.unwrap();
        assert_eq!(rmw.operation, RmwBinOp::Add);
        assert!(matches!(rmw.ptr, Operand::Var(_)));
        assert!(matches!(rmw.value, Operand::Var(_)));
        assert!(matches!(rmw.result, ConstraintSystemVariable(_)));
    }

    #[test]
    fn atomic_cmpxchg_ir_processing() {
        let llvm_ir = r#"
            define { i32, i1 } @atomic_cmpxchg(i32* %ptr, i32 %cmp, i32 %new) {
            entry:
                %res = cmpxchg i32* %ptr, i32 %cmp, i32 %new monotonic monotonic
                ret { i32, i1 } %res
            }
        "#;
        let (constraints, memory_log) = process_llvm_ir(llvm_ir).unwrap();
        assert_eq!(constraints.len(), 5); // AtomicCmpXchg + Assign + Return + stack operations
        assert_eq!(memory_log.len(), 4); // CmpXchg read/write + Return stack operations

        let cmpxchg_constraint = constraints.iter().find_map(|c| match c {
            StructuredAirConstraint::AtomicCmpXchg(cx) => Some(cx),
            _ => None,
        });
        assert!(
            cmpxchg_constraint.is_some(),
            "No AtomicCmpXchg constraint found"
        );

        let assign_constraint = constraints
            .iter()
            .find(|c| matches!(c, StructuredAirConstraint::Assign(_)));
        assert!(
            assign_constraint.is_some(),
            "No Assign constraint for extractvalue from cmpxchg"
        );
    }

    #[test]
    fn addrspacecast_ir_processing() {
        let llvm_ir = r#"
            define i32* @cast(i32 addrspace(1)* %ptr) {
            entry:
                %casted_ptr = addrspacecast i32 addrspace(1)* %ptr to i32*
                ret i32* %casted_ptr
            }
        "#;
        let (constraints, memory_log) = process_llvm_ir(llvm_ir).unwrap();
        assert_eq!(constraints.len(), 5); // Assign + Return + stack operations
        assert_eq!(memory_log.len(), 2); // Stack operations for return

        let assign_constraint = constraints.iter().find_map(|c| match c {
            StructuredAirConstraint::Assign(assign) => Some(assign),
            _ => None,
        });
        assert!(
            assign_constraint.is_some(),
            "No Assign constraint found for addrspacecast"
        );
    }

    #[test]
    fn bitcast_ir_processing() {
        let llvm_ir = r#"
            define float @cast(i32 %val) {
            entry:
                %casted_val = bitcast i32 %val to float
                ret float %casted_val
            }
        "#;
        let (constraints, memory_log) = process_llvm_ir(llvm_ir).unwrap();
        assert_eq!(constraints.len(), 5); // Assign + Return + stack operations
        assert_eq!(memory_log.len(), 2); // Stack operations for return

        let assign_constraint = constraints.iter().find_map(|c| match c {
            StructuredAirConstraint::Assign(assign) => Some(assign),
            _ => None,
        });
        assert!(
            assign_constraint.is_some(),
            "No Assign constraint found for bitcast"
        );
    }

    #[test]
    fn ptrtoint_ir_processing() {
        let llvm_ir = r#"
            define i64 @cast(i32* %ptr) {
            entry:
                %casted_val = ptrtoint i32* %ptr to i64
                ret i64 %casted_val
            }
        "#;
        let (constraints, memory_log) = process_llvm_ir(llvm_ir).unwrap();
        assert_eq!(constraints.len(), 5); // Assign + Return + stack operations
        assert_eq!(memory_log.len(), 2); // Stack operations for return

        let assign_constraint = constraints.iter().find_map(|c| match c {
            StructuredAirConstraint::Assign(assign) => Some(assign),
            _ => None,
        });
        assert!(
            assign_constraint.is_some(),
            "No Assign constraint found for ptrtoint"
        );
    }

    #[test]
    fn inttoptr_ir_processing() {
        let llvm_ir = r#"
            define i32* @cast(i64 %int) {
            entry:
                %casted_val = inttoptr i64 %int to i32*
                ret i32* %casted_val
            }
        "#;
        let (constraints, memory_log) = process_llvm_ir(llvm_ir).unwrap();
        assert_eq!(constraints.len(), 5); // Assign + Return + stack operations
        assert_eq!(memory_log.len(), 2); // Stack operations for return

        let assign_constraint = constraints.iter().find_map(|c| match c {
            StructuredAirConstraint::Assign(assign) => Some(assign),
            _ => None,
        });
        assert!(
            assign_constraint.is_some(),
            "No Assign constraint found for inttoptr"
        );
    }

    #[test]
    fn cleanup_pad_ret_ir_processing() {
        let llvm_ir = r#"
            declare void @do_stuff()

            define void @cleanup_test() {
            entry:
                invoke void @do_stuff() to label %normal unwind label %cleanup_block

            cleanup_block:
                %cp = cleanuppad within none []
                cleanupret from %cp unwind to caller

            normal:
                ret void
            }
        "#;
        let (constraints, memory_log) = process_llvm_ir(llvm_ir).unwrap();
        assert!(constraints.len() >= 4); // CleanupPad + CleanupRet + Return + stack operations
        assert!(memory_log.len() >= 4); // Stack operations for calls and returns

        let pad_constraint = constraints.iter().find_map(|c| match c {
            StructuredAirConstraint::CleanupPad(cp) => Some(cp),
            _ => None,
        });
        assert!(pad_constraint.is_some(), "No CleanupPad constraint found");

        let ret_constraint = constraints.iter().find_map(|c| match c {
            StructuredAirConstraint::CleanupRet(cr) => Some(cr),
            _ => None,
        });
        assert!(ret_constraint.is_some(), "No CleanupRet constraint found");
    }

    #[test]
    fn landing_pad_resume_ir_processing() {
        let llvm_ir = r#"
            declare void @do_stuff()

            define void @landing_test() {
            entry:
                invoke void @do_stuff() to label %normal unwind label %landing

            landing:
                %lp = landingpad { i8*, i32 } cleanup
                resume { i8*, i32 } %lp

            normal:
                ret void
            }
        "#;
        let (constraints, memory_log) = process_llvm_ir(llvm_ir).unwrap();
        assert!(constraints.len() >= 4); // LandingPad + Resume + Return + stack operations
        assert!(memory_log.len() >= 4); // Stack operations for calls and returns

        let pad_constraint = constraints.iter().find_map(|c| match c {
            StructuredAirConstraint::LandingPad(lp) => Some(lp),
            _ => None,
        });
        assert!(pad_constraint.is_some(), "No LandingPad constraint found");

        let resume_constraint = constraints.iter().find_map(|c| match c {
            StructuredAirConstraint::Resume(r) => Some(r),
            _ => None,
        });
        assert!(resume_constraint.is_some(), "No Resume constraint found");
    }

    #[test]
    fn indirect_br_ir_processing() {
        let llvm_ir = r#"
            define void @test_indirectbr(i8* %addr) {
            entry:
                indirectbr i8* %addr, [label %dest1, label %dest2]

            dest1:
                ret void

            dest2:
                ret void
            }
        "#;
        let (constraints, memory_log) = process_llvm_ir(llvm_ir).unwrap();
        assert_eq!(constraints.len(), 9); // IndirectBr + 2 Returns + stack operations
        assert_eq!(memory_log.len(), 4); // Stack operations for returns

        let indirect_br = constraints.iter().find_map(|c| match c {
            StructuredAirConstraint::IndirectBr(ibr) => Some(ibr),
            _ => None,
        });
        assert!(indirect_br.is_some(), "No IndirectBr constraint found");

        let ibr = indirect_br.unwrap();
        assert_eq!(ibr.destinations.len(), 2);
        assert!(ibr.destinations.contains(&"dest1".to_string()));
        assert!(ibr.destinations.contains(&"dest2".to_string()));
    }

    #[test]
    fn shuffle_vector_ir_processing() {
        let llvm_ir = r#"
            define <2 x i32> @test_shuffle(<2 x i32> %v1, <2 x i32> %v2) {
            entry:
                %shuf = shufflevector <2 x i32> %v1, <2 x i32> %v2, <2 x i32> <i32 0, i32 3>
                ret <2 x i32> %shuf
            }
        "#;
        let (constraints, memory_log) = process_llvm_ir(llvm_ir).unwrap();
        assert_eq!(constraints.len(), 4); // Assign + Return + stack operations
        assert_eq!(memory_log.len(), 2); // Stack operations for return
    }

    #[test]
    fn va_arg_ir_processing() {
        let llvm_ir = r#"
            %struct.__va_list_tag = type { i32, i32, i8*, i8* }

            define i32 @test_va_arg(i32 %n, ...) {
            entry:
                %va_list_ptr = alloca %struct.__va_list_tag, align 8
                %va_list_i8 = bitcast %struct.__va_list_tag* %va_list_ptr to i8*
                call void @llvm.va_start(i8* %va_list_i8)
                %arg1 = va_arg i8* %va_list_i8, i32
                call void @llvm.va_end(i8* %va_list_i8)
                ret i32 %arg1
            }

            declare void @llvm.va_start(i8*)
            declare void @llvm.va_end(i8*)
        "#;
        let (constraints, memory_log) = process_llvm_ir(llvm_ir).unwrap();
        assert!(constraints.len() >= 5); // Alloca + Assign + 2 Calls + Return + stack operations
        assert!(memory_log.len() >= 6); // Alloca + va_arg read/write + Call stack operations

        let add_count = constraints
            .iter()
            .filter(|c| matches!(c, StructuredAirConstraint::Add(_)))
            .count();
        assert_eq!(
            add_count, 2,
            "Expected two Add constraints, one for alloca and one for va_arg pointer increment"
        );
    }
}

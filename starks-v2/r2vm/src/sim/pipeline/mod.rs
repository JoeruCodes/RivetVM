use crate::emu::dbt::DbtCompiler;
use riscv::Op;

mod in_order;
pub use in_order::InOrderModel;

pub trait PipelineModel {
    fn can_fuse_cond_op(&self) -> bool {
        true
    }

    fn begin_block(&mut self, _compiler: &mut DbtCompiler, _pc: u64) {}

    fn before_instruction(&mut self, _compiler: &mut DbtCompiler, _op: &Op, _compressed: bool) {}

    fn after_instruction(&mut self, _compiler: &mut DbtCompiler, _op: &Op, _compressed: bool) {}

    fn after_taken_branch(&mut self, _compiler: &mut DbtCompiler, _op: &Op, _compressed: bool) {}
}

#[derive(Default)]
pub struct AtomicModel;

impl PipelineModel for AtomicModel {}

#[derive(Default)]
pub struct SimpleModel;

impl PipelineModel for SimpleModel {
    fn after_instruction(&mut self, compiler: &mut DbtCompiler, _op: &Op, _compressed: bool) {
        compiler.insert_cycle_count(1);
    }

    fn after_taken_branch(&mut self, compiler: &mut DbtCompiler, _op: &Op, _compressed: bool) {
        compiler.insert_cycle_count(1);
    }
}

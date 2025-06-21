use crate::emu::interp::Context;
use riscv::mmu::AccessType;

pub mod cache;
pub mod cache_set;
pub mod replacement_policy;
pub mod tlb;

pub use cache::SimpleCacheModel;
pub use tlb::TLBModel;

pub trait MemoryModel: Sync {
    fn cache_line_size_log2(&self) -> u32 {
        6
    }

    fn instruction_access(&self, ctx: &mut Context, addr: u64) -> Result<u64, ()> {
        let paddr = ctx.translate_vaddr(addr, AccessType::Execute)?;
        ctx.insert_instruction_cache_line(addr, paddr);
        Ok(paddr)
    }

    fn data_access(&self, ctx: &mut Context, addr: u64, write: bool) -> Result<u64, ()> {
        let paddr =
            ctx.translate_vaddr(addr, if write { AccessType::Write } else { AccessType::Read })?;
        ctx.insert_data_cache_line(addr, paddr, write);
        Ok(paddr)
    }

    fn before_fence_i(&self, _ctx: &mut Context, _mask: u64) {}

    fn before_sfence_vma(
        &self,
        _ctx: &mut Context,
        _mask: u64,
        _asid: Option<u16>,
        _vaddr: Option<u64>,
    ) {
    }

    fn before_satp_change(&self, ctx: &mut Context, new_satp: u64) {
        let _ = (ctx, new_satp);
    }

    fn reset_stats(&self) {}

    fn print_stats(&self, _writer: &mut dyn std::io::Write) -> std::io::Result<()> {
        Ok(())
    }
}

#[derive(Default)]
pub struct AtomicModel;

impl MemoryModel for AtomicModel {
    fn cache_line_size_log2(&self) -> u32 {
        12
    }
}

#[derive(Default)]
pub struct SimpleModel;

impl MemoryModel for SimpleModel {}

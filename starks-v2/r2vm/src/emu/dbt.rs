use super::interp::{Context, SharedContext};
use crate::sim::{PipelineModel, get_memory_model, new_pipeline_model};
use fiber::raw::{fiber_sleep_raw, fiber_yield_raw};
use riscv::{Csr, Op};
use std::convert::TryFrom;
use x86::builder::*;
use x86::{ConditionCode, Op as X86Op, Op::*, Register, Size};

const PAGE_CROSS_RESERVATION: usize = 256;

macro_rules! memory_of {
    ($e:ident) => {
        Register::RBP + offset_of!(Context, $e) as i32
    };
}

#[inline]
fn loc_of_register(reg: u8) -> x86::Location {
    Mem(Register::RBP + reg as i32 * 8)
}

#[inline]
fn same_page(a: u64, b: u64) -> bool {
    a >> 12 == b >> 12
}

#[inline]
fn same_cache_line(a: u64, b: u64) -> bool {
    let cache_line_size_log2 = get_memory_model().cache_line_size_log2();
    a >> cache_line_size_log2 == b >> cache_line_size_log2
}

extern "C" {
    fn read_csr();
    fn write_csr();
    fn riscv_step();
    fn helper_trap();
    fn helper_misalign();
    fn translate_cache_miss();
    fn insn_translate_cache_miss();
    fn helper_icache_cross_miss();
    fn helper_patch_direct_jump();
    fn helper_check_interrupt();
    fn helper_san_fail();
    fn helper_pred_miss();
}

pub struct DbtCompiler<'a> {
    pub buffer: &'a mut [u8],
    pub len: usize,
    slow_path: Vec<SlowPath>,

    pc_start: u64,

    pc_cur: i64,

    pc_end: i64,

    instret: i32,

    minstret: u32,

    cycles: usize,

    pub(super) model: Option<Box<dyn PipelineModel>>,

    pub speculative_len: usize,
}

#[derive(Clone, Copy)]
struct Label(usize);
enum PlaceHolder {
    Byte(usize),
    Dword(usize),
}

impl Drop for PlaceHolder {
    fn drop(&mut self) {
        panic!("placeholder left unpatched");
    }
}

enum SlowPath {
    DCache {
        ebx: u32,
        write: bool,
        jcc_misalign: Option<PlaceHolder>,
        jcc_miss: PlaceHolder,
        label_fin: Label,
    },

    ICache(u32, PlaceHolder, Label),
    Trap(u32, PlaceHolder),
}

impl<'a> DbtCompiler<'a> {
    pub fn new(ctx: &'a mut Context, code: &'a mut [u8]) -> Self {
        DbtCompiler {
            buffer: code,
            len: 0,
            slow_path: Vec::new(),
            minstret: 0,
            pc_start: 0,
            pc_end: 0,
            pc_cur: 0,
            instret: 0,
            cycles: 0,
            model: Some(new_pipeline_model(ctx.hartid as usize)),
            speculative_len: 0,
        }
    }

    fn with_model<R>(&mut self, f: impl FnOnce(&mut Self, &mut dyn PipelineModel) -> R) -> R {
        let mut model = self.model.take().unwrap();
        let ret = f(self, &mut *model);
        self.model = Some(model);
        ret
    }

    pub fn insert_cycle_count(&mut self, count: usize) {
        self.cycles += count;
    }

    fn emit(&mut self, op: X86Op) {
        x86::encode(op, &mut |x| {
            self.buffer[self.len] = x;
            self.len += 1;
        });
    }

    fn emit_jcc_short(&mut self, cc: ConditionCode) -> PlaceHolder {
        self.emit(Jcc(0, cc));
        PlaceHolder::Byte(self.len)
    }

    fn emit_jcc_long(&mut self, cc: ConditionCode) -> PlaceHolder {
        self.emit(Jcc(0x80, cc));
        PlaceHolder::Dword(self.len)
    }

    #[allow(dead_code)]
    fn emit_jmp_short(&mut self) -> PlaceHolder {
        self.emit(Jmp(Imm(0)));
        PlaceHolder::Byte(self.len)
    }

    fn emit_jmp_long(&mut self) -> PlaceHolder {
        self.emit(Jmp(Imm(0x77777777)));
        PlaceHolder::Dword(self.len)
    }

    fn label(&mut self) -> Label {
        Label(self.len)
    }

    fn patch(&mut self, place: PlaceHolder, label: Label) {
        match place {
            PlaceHolder::Byte(ptr) => {
                let offset = label.0 as isize - ptr as isize;
                self.buffer[ptr - 1] = i8::try_from(offset).unwrap() as u8
            }
            PlaceHolder::Dword(ptr) => {
                let offset = i32::try_from(label.0 as isize - ptr as isize).unwrap();
                self.buffer[ptr - 4..ptr].copy_from_slice(&offset.to_le_bytes());
            }
        }
        std::mem::forget(place)
    }

    fn patch_absolute(&mut self, place: PlaceHolder, target: usize) {
        match place {
            PlaceHolder::Byte(_) => unimplemented!(),
            PlaceHolder::Dword(ptr) => {
                let offset =
                    i32::try_from(target as isize - (self.buffer.as_ptr() as usize + ptr) as isize)
                        .unwrap();
                self.buffer[ptr - 4..ptr].copy_from_slice(&offset.to_le_bytes());
            }
        }
        std::mem::forget(place)
    }

    #[allow(dead_code)]
    fn patch_number(&mut self, place: PlaceHolder, target: usize) {
        match place {
            PlaceHolder::Byte(ptr) => {
                self.buffer[ptr - 1] = target as u8;
            }
            PlaceHolder::Dword(ptr) => {
                self.buffer[ptr - 4..ptr].copy_from_slice(&(target as u32).to_le_bytes());
            }
        }
        std::mem::forget(place)
    }

    fn load_reg(&mut self, reg: Register, rs: u8) {
        if rs == 0 {
            let reg = reg.resize(Size::Dword);
            self.emit(Xor(reg.into(), reg.into()));
            return;
        }
        self.emit(Mov(reg.into(), loc_of_register(rs).resize(reg.size()).into()));
    }

    fn store_reg(&mut self, rd: u8, reg: Register) {
        if rd == 0 {
            return;
        }
        let qreg = reg.resize(Size::Qword);
        match reg.size() {
            Size::Qword => (),
            Size::Dword => {
                if reg == Register::EAX {
                    self.emit(Cdqe);
                } else {
                    self.emit(Movsx(qreg, reg.into()));
                }
            }
            _ => unreachable!(),
        }
        self.emit(Mov(loc_of_register(rd), qreg.into()));
    }

    fn emit_move(&mut self, rd: u8, rs: u8) {
        if rd == 0 || rd == rs {
            return;
        }
        if rs == 0 {
            return self.emit_load_imm(rd, 0);
        }

        self.emit(Mov(Reg(Register::RAX), loc_of_register(rs).into()));
        self.emit(Mov(loc_of_register(rd), OpReg(Register::RAX)));
    }

    fn emit_move32(&mut self, rd: u8, rs: u8) {
        if rd == 0 {
            return;
        }
        if rs == 0 {
            return self.emit_load_imm(rd, 0);
        }

        self.emit(Movsx(Register::RAX, loc_of_register(rs).resize(Size::Dword)));
        self.emit(Mov(loc_of_register(rd), OpReg(Register::RAX)));
    }

    fn emit_load_imm(&mut self, rd: u8, imm: i32) {
        if rd == 0 {
            return;
        }
        self.emit(Mov(loc_of_register(rd), Imm(imm as i64)));
    }

    fn get_ebx(&mut self) -> u32 {
        let pc_rel = self.pc_cur as i16;
        let instret_rel = self.instret as i16;

        (instret_rel as u16 as u32) << 16 | pc_rel as u16 as u32
    }

    fn emit_helper_call(&mut self, helper: unsafe extern "C" fn()) {
        self.emit(Call(Imm(0x77777777)));
        let placeholder = PlaceHolder::Dword(self.len);
        self.patch_absolute(placeholder, helper as usize);
    }

    fn emit_helper_jmp(&mut self, helper: unsafe extern "C" fn()) {
        self.emit(Jmp(Imm(0x77777777)));
        let placeholder = PlaceHolder::Dword(self.len);
        self.patch_absolute(placeholder, helper as usize);
    }

    fn emit_helper_jcc(&mut self, cc: ConditionCode, helper: unsafe extern "C" fn()) {
        let placeholder = self.emit_jcc_long(cc);
        self.patch_absolute(placeholder, helper as usize);
    }

    fn emit_step_call(&mut self, op: &Op) {
        self.before_side_effect();

        self.emit(Mov(Reg(Register::RDI), OpReg(Register::RBP)));

        let op: i64 = unsafe { std::mem::transmute(*op) };
        self.emit(Mov(Reg(Register::RSI), Imm(op)));
        self.emit_helper_call(riscv_step);
        self.emit(Test(Reg(Register::AL), OpReg(Register::AL)));
        let jcc_trap = self.emit_jcc_long(ConditionCode::NotEqual);

        let ebx = self.get_ebx();
        self.slow_path.push(SlowPath::Trap(ebx, jcc_trap));
    }

    fn before_side_effect(&mut self) {
        if self.cycles == 0 {
            return;
        }
        if crate::threaded() {
            self.emit(Add(memory_of!(cycle_offset).into(), Imm(self.cycles as i64)));
        } else {
            if self.cycles == 1 {
                self.emit_helper_call(fiber_yield_raw);
            } else {
                self.emit(Mov(Register::RDI.into(), Imm((self.cycles - 1) as i64)));
                self.emit_helper_call(fiber_sleep_raw);
            }
        }
        self.cycles = 0;
    }

    fn emit_branch(
        &mut self,
        rs1: u8,
        rs2: u8,
        imm: i32,
        mut cc: ConditionCode,
        op: &Op,
        compressed: bool,
    ) {
        if rs2 == 0 {
            self.emit(Cmp(loc_of_register(rs1), Imm(0)));
        } else if rs1 == 0 {
            cc = cc.swap();
            self.emit(Cmp(loc_of_register(rs2), Imm(0)));
        } else {
            self.emit(Mov(Reg(Register::RDX), loc_of_register(rs1).into()));
            self.emit(Cmp(Reg(Register::RDX), loc_of_register(rs2).into()));
        }

        let jcc_not = self.emit_jcc_long(!cc);

        let pre_pc_offset = self.pc_end.wrapping_sub(if compressed { 2 } else { 4 });

        let pc_offset = pre_pc_offset.wrapping_add(imm as i64);
        self.emit(Add(Mem(memory_of!(pc)), Imm(pc_offset)));
        self.pre_adjust_instret();

        let old_cycles = self.cycles;
        self.with_model(|this, model| model.after_taken_branch(this, op, compressed));
        self.emit_interrupt_check();

        let target = self.pc_start.wrapping_add(pc_offset as u64);

        let old_pc_cur = self.pc_cur;
        self.pc_cur = 0;
        let old_instret = self.instret;
        self.instret = 0;

        if same_page(self.pc_start, target) {
            if !same_cache_line(self.pc_start.wrapping_add(self.pc_end as u64) - 1, target) {
                assert_eq!(self.get_ebx(), 0);
                self.emit_icache_access(0, false);
            }
            self.emit_helper_call(helper_patch_direct_jump);
        } else {
            self.emit_chain_tail();
        }

        self.pc_cur = old_pc_cur;
        self.instret = old_instret;
        self.cycles = old_cycles;

        let label_not = self.label();
        self.patch(jcc_not, label_not);
    }

    fn emit_jalr(&mut self, rd: u8, rs1: u8, imm: i32, op: &Op, compressed: bool) {
        self.pre_adjust_instret();

        self.load_reg(Register::RAX, rs1);
        if imm != 0 {
            self.emit(Add(Reg(Register::RAX), Imm(imm as i64)));
        }
        self.emit(And(Reg(Register::RAX), Imm(!(1 as i64))));

        if rd != 0 {
            self.emit(Mov(Reg(Register::RDX), OpMem(memory_of!(pc))));
            self.emit(Add(Register::RDX.into(), Imm(self.pc_cur + if compressed { 2 } else { 4 })));
            self.emit(Mov(loc_of_register(rd), OpReg(Register::RDX)));
        }

        self.emit(Mov(Mem(memory_of!(pc)), OpReg(Register::RAX)));

        self.with_model(|this, model| model.after_instruction(this, op, compressed));
        self.emit_interrupt_check();
        self.emit_chain_tail();
    }

    fn emit_jal(&mut self, rd: u8, imm: i32, op: &Op, compressed: bool) {
        self.pre_adjust_instret();
        let pc_offset = self.pc_cur + if compressed { 2 } else { 4 };
        let imm_from_end = (imm as i64).wrapping_sub(if compressed { 2 } else { 4 });

        if rd != 0 {
            self.emit(Mov(Register::RAX.into(), memory_of!(pc).into()));
            self.emit(Lea(Register::RDX, Register::RAX + (pc_offset as i32)));
            self.store_reg(rd, Register::RDX);
            self.emit(Add(Register::RAX.into(), Imm(imm_from_end.wrapping_add(pc_offset))));
            self.emit(Mov(memory_of!(pc).into(), Register::RAX.into()));
        } else {
            self.emit(Add(memory_of!(pc).into(), Imm(imm_from_end.wrapping_add(pc_offset))));
        }

        self.with_model(|this, model| model.after_instruction(this, op, compressed));
        self.emit_interrupt_check();

        let pc_end = self.pc_start.wrapping_add(self.pc_end as u64);
        let target = pc_end.wrapping_add(imm_from_end as u64);
        if same_cache_line(pc_end, target) {
            self.emit_helper_call(helper_patch_direct_jump);
        } else {
            self.emit_chain_tail();
        }
    }

    fn emit_icache_access(&mut self, pc_offset: i64, set_rsi: bool) {
        self.before_side_effect();

        self.emit(Mov(Reg(Register::RSI), OpMem(memory_of!(pc))));
        if pc_offset != 0 {
            self.emit(Add(Reg(Register::RSI), Imm(pc_offset)));
        }

        if cfg!(feature = "direct") && crate::get_flags().prv == 0 {
            return;
        }

        let offset = offset_of!(Context, shared) + offset_of!(SharedContext, i_line);

        self.emit(Mov(Reg(Register::RCX), OpReg(Register::RSI)));
        self.emit(Shr(Reg(Register::RCX), Imm(get_memory_model().cache_line_size_log2() as i64)));

        self.emit(Mov(Reg(Register::EAX), OpReg(Register::ECX)));
        self.emit(And(Reg(Register::EAX), Imm(1023)));
        self.emit(Shl(Reg(Register::EAX), Imm(4)));

        self.emit(Cmp(Reg(Register::RCX), OpMem(Register::RBP + Register::RAX + offset as i32)));

        let jcc_miss = self.emit_jcc_long(ConditionCode::NotEqual);
        if set_rsi {
            self.emit(Xor(
                Reg(Register::RSI),
                OpMem(Register::RBP + Register::RAX + (offset + 8) as i32),
            ));
        }
        let label_fin = self.label();

        let ebx = self.get_ebx();
        self.slow_path.push(SlowPath::ICache(ebx, jcc_miss, label_fin));
    }

    fn emit_icache_slow(&mut self, ebx: u32, jcc_miss: PlaceHolder, label_fin: Label) {
        let label_miss = self.label();
        self.patch(jcc_miss, label_miss);

        self.emit(Mov(Reg(Register::RDI), OpReg(Register::RBP)));
        self.emit_helper_call(insn_translate_cache_miss);
        self.emit(Mov(Reg(Register::RSI), OpReg(Register::RDX)));
        self.emit(Test(Reg(Register::AL), OpReg(Register::AL)));
        let jcc_fin = self.emit_jcc_long(ConditionCode::Equal);
        self.patch(jcc_fin, label_fin);

        self.emit(Mov(Reg(Register::EBX), Imm(ebx as i64)));
        self.emit_helper_jmp(helper_trap);
    }

    fn emit_chain_tail(&mut self) {
        assert_eq!(self.cycles, 0);

        self.emit(Lea(Register::RBX, Register::RIP + 5));

        self.emit_helper_jmp(helper_pred_miss);
    }

    fn emit_interrupt_check(&mut self) {
        self.before_side_effect();

        let offset = offset_of!(Context, shared) + offset_of!(SharedContext, alarm);
        self.emit(Cmp(Mem(Register::RBP + offset as i32), Imm(0)));
        self.emit_helper_jcc(ConditionCode::NotEqual, helper_check_interrupt);
    }

    fn emit_trap(&mut self, ebx: u32, jcc_trap: PlaceHolder) {
        let label_trap = self.label();
        self.patch(jcc_trap, label_trap);

        self.emit(Mov(Reg(Register::EBX), Imm(ebx as i64)));
        self.emit_helper_jmp(helper_trap);
    }

    fn dcache_access(&mut self, size: Size, write: bool) {
        if cfg!(feature = "direct") && crate::get_flags().prv == 0 {
            return;
        }

        let jcc_misalign = if size != Size::Byte {
            self.emit(Test(Reg(Register::ESI), Imm(size.bytes() as i64 - 1)));
            Some(self.emit_jcc_long(ConditionCode::NotEqual))
        } else {
            None
        };

        let offset = offset_of!(Context, shared) + offset_of!(SharedContext, line);

        self.emit(Mov(Reg(Register::RCX), OpReg(Register::RSI)));
        self.emit(Shr(Reg(Register::RCX), Imm(get_memory_model().cache_line_size_log2() as i64)));

        self.emit(Mov(Reg(Register::EAX), OpReg(Register::ECX)));
        self.emit(And(Reg(Register::EAX), Imm(1023)));
        self.emit(Shl(Reg(Register::EAX), Imm(4)));

        if write {
            self.emit(Add(Reg(Register::RCX), OpReg(Register::RCX)));
            self.emit(Cmp(
                Reg(Register::RCX),
                OpMem(Register::RBP + Register::RAX + offset as i32),
            ));
        } else {
            self.emit(Mov(
                Reg(Register::RDX),
                OpMem(Register::RBP + Register::RAX + offset as i32),
            ));
            self.emit(Shr(Reg(Register::RDX), Imm(1)));
            self.emit(Cmp(Reg(Register::RDX), OpReg(Register::RCX)));
        }
        let jcc_miss = self.emit_jcc_long(ConditionCode::NotEqual);

        self.emit(Xor(
            Reg(Register::RSI),
            OpMem(Register::RBP + Register::RAX + (offset + 8) as i32),
        ));
        let label_fin = self.label();

        let ebx = self.get_ebx();
        self.slow_path.push(SlowPath::DCache { ebx, write, jcc_misalign, jcc_miss, label_fin });
    }

    fn dcache_access_slow(
        &mut self,
        ebx: u32,
        write: bool,
        jcc_misalign: Option<PlaceHolder>,
        jcc_miss: PlaceHolder,
        label_fin: Label,
    ) {
        if let Some(jcc_misalign) = jcc_misalign {
            let label_misalign = self.label();
            self.patch(jcc_misalign, label_misalign);

            self.emit(Mov(Reg(Register::EBX), Imm(ebx as i64)));
            self.emit_helper_jmp(helper_misalign);
        }

        let label_miss = self.label();
        self.patch(jcc_miss, label_miss);

        self.emit(Mov(Reg(Register::RDI), OpReg(Register::RBP)));
        if write {
            self.emit(Mov(Reg(Register::EDX), Imm(1)));
        } else {
            self.emit(Xor(Reg(Register::EDX), OpReg(Register::EDX)));
        }
        self.emit_helper_call(translate_cache_miss);
        self.emit(Mov(Reg(Register::RSI), OpReg(Register::RDX)));
        self.emit(Test(Reg(Register::AL), OpReg(Register::AL)));

        let jcc_fin = self.emit_jcc_long(ConditionCode::Equal);
        self.patch(jcc_fin, label_fin);

        self.emit(Mov(Reg(Register::EBX), Imm(ebx as i64)));
        self.emit_helper_jmp(helper_trap);
    }

    fn emit_load(&mut self, rs1: u8, imm: i32, size: Size) {
        self.before_side_effect();

        self.minstret += 1;

        self.emit(Mov(Reg(Register::RSI), loc_of_register(rs1).into()));
        if imm != 0 {
            self.emit(Add(Reg(Register::RSI), Imm(imm as i64)));
        }

        self.dcache_access(size, false);
    }

    fn emit_store(&mut self, rs1: u8, rs2: u8, imm: i32, size: Size) {
        self.before_side_effect();

        self.minstret += 1;

        self.emit(Mov(Reg(Register::RSI), loc_of_register(rs1).into()));
        if imm != 0 {
            self.emit(Add(Reg(Register::RSI), Imm(imm as i64)));
        }

        self.dcache_access(size, true);

        let reg = Register::RDX.resize(size);
        self.emit(Mov(Reg(reg), loc_of_register(rs2).resize(size).into()));
        self.emit(Mov((Register::RSI + 0).resize(size).into(), reg.into()));
    }

    fn emit_addi(&mut self, rd: u8, rs1: u8, imm: i32) {
        if rd == 0 {
            return;
        }
        if rs1 == 0 {
            return self.emit_load_imm(rd, imm);
        }
        if imm == 0 {
            return self.emit_move(rd, rs1);
        }

        if rd == rs1 {
            return self.emit(Add(loc_of_register(rd), Imm(imm as i64)));
        }

        self.emit(Mov(Reg(Register::RAX), loc_of_register(rs1).into()));
        self.emit(Add(Reg(Register::RAX), Imm(imm as i64)));
        self.emit(Mov(loc_of_register(rd), OpReg(Register::RAX)));
    }

    fn emit_slli(&mut self, rd: u8, rs1: u8, imm: i32) {
        if rd == 0 {
            return;
        }
        if rs1 == 0 {
            return self.emit_load_imm(rd, 0);
        }
        if imm == 0 {
            return self.emit_move(rd, rs1);
        }

        if rd == rs1 {
            return self.emit(Shl(loc_of_register(rd), Imm(imm as i64)));
        }

        self.emit(Mov(Reg(Register::RAX), loc_of_register(rs1).into()));

        if imm == 1 {
            self.emit(Add(Reg(Register::RAX), OpReg(Register::RAX)))
        } else {
            self.emit(Shl(Reg(Register::RAX), Imm(imm as i64)))
        }

        self.emit(Mov(loc_of_register(rd), OpReg(Register::RAX)));
    }

    fn emit_slti(&mut self, rd: u8, rs1: u8, mut imm: i32) {
        if rd == 0 {
            return;
        }
        if rs1 == 0 {
            self.emit_load_imm(rd, (imm > 0) as i32)
        }

        if imm == 0 {
            if rd == rs1 {
                self.emit(Shr(loc_of_register(rd), Imm(63)));
            } else {
                self.load_reg(Register::RAX, rs1);
                self.emit(Shr(Reg(Register::RAX), Imm(63)));
                self.store_reg(rd, Register::RAX);
            }
        } else {
            let cc = if imm > 0 {
                imm -= 1;
                ConditionCode::LessEqual
            } else {
                ConditionCode::Less
            };

            self.emit(Xor(Reg(Register::EAX), OpReg(Register::EAX)));
            self.emit(Cmp(loc_of_register(rs1), Imm(imm as i64)));
            self.emit(Setcc(Reg(Register::AL), cc));
            self.store_reg(rd, Register::RAX);
        }
    }

    fn emit_sltiu(&mut self, rd: u8, rs1: u8, mut imm: i32) {
        if rd == 0 {
            return;
        }
        if rs1 == 0 {
            self.emit_load_imm(rd, (imm != 0) as i32)
        }
        if imm == 0 {
            self.emit_load_imm(rd, 0)
        }

        let cc = if imm > 0 {
            imm -= 1;
            if imm == 0 { ConditionCode::Equal } else { ConditionCode::BelowEqual }
        } else {
            if imm == -1 { ConditionCode::NotEqual } else { ConditionCode::Below }
        };

        self.emit(Xor(Reg(Register::EAX), OpReg(Register::EAX)));
        self.emit(Cmp(loc_of_register(rs1), Imm(imm as i64)));
        self.emit(Setcc(Reg(Register::AL), cc));
        self.store_reg(rd, Register::RAX);
    }

    fn emit_xori(&mut self, rd: u8, rs1: u8, imm: i32) {
        if rd == 0 {
            return;
        }
        if rs1 == 0 {
            return self.emit_load_imm(rd, imm);
        }
        if imm == 0 {
            return self.emit_move(rd, rs1);
        }

        if imm == -1 {
            if rd == rs1 {
                self.emit(Not(loc_of_register(rd)));
            } else {
                self.load_reg(Register::RAX, rs1);
                self.emit(Not(Reg(Register::RAX)));
                self.store_reg(rd, Register::RAX);
            }
        } else {
            if rd == rs1 {
                self.emit(Xor(loc_of_register(rd), Imm(imm as i64)));
            } else {
                self.load_reg(Register::RAX, rs1);
                self.emit(Xor(Reg(Register::RAX), Imm(imm as i64)));
                self.store_reg(rd, Register::RAX);
            }
        }
    }

    fn emit_srli(&mut self, rd: u8, rs1: u8, imm: i32) {
        if rd == 0 {
            return;
        }
        if rs1 == 0 {
            return self.emit_load_imm(rd, 0);
        }
        if imm == 0 {
            return self.emit_move(rd, rs1);
        }

        if rd == rs1 {
            return self.emit(Shr(loc_of_register(rd), Imm(imm as i64)));
        }

        self.emit(Mov(Reg(Register::RAX), loc_of_register(rs1).into()));
        self.emit(Shr(Reg(Register::RAX), Imm(imm as i64)));
        self.emit(Mov(loc_of_register(rd), OpReg(Register::RAX)));
    }

    fn emit_srai(&mut self, rd: u8, rs1: u8, imm: i32) {
        if rd == 0 {
            return;
        }
        if rs1 == 0 {
            return self.emit_load_imm(rd, 0);
        }
        if imm == 0 {
            return self.emit_move(rd, rs1);
        }

        if rd == rs1 {
            return self.emit(Sar(loc_of_register(rd), Imm(imm as i64)));
        }

        self.emit(Mov(Reg(Register::RAX), loc_of_register(rs1).into()));
        self.emit(Sar(Reg(Register::RAX), Imm(imm as i64)));
        self.emit(Mov(loc_of_register(rd), OpReg(Register::RAX)));
    }

    fn emit_ori(&mut self, rd: u8, rs1: u8, imm: i32) {
        if rd == 0 {
            return;
        }
        if rs1 == 0 {
            return self.emit_load_imm(rd, imm);
        }
        if imm == 0 {
            return self.emit_move(rd, rs1);
        }
        if imm == -1 {
            return self.emit_load_imm(rd, -1);
        }

        if rd == rs1 {
            self.emit(Or(loc_of_register(rd), Imm(imm as i64)));
        } else {
            self.load_reg(Register::RAX, rs1);
            self.emit(Or(Reg(Register::RAX), Imm(imm as i64)));
            self.store_reg(rd, Register::RAX);
        }
    }

    fn emit_andi(&mut self, rd: u8, rs1: u8, imm: i32) {
        if rd == 0 {
            return;
        }
        if rs1 == 0 {
            return self.emit_load_imm(rd, 0);
        }
        if imm == 0 {
            return self.emit_load_imm(rd, 0);
        }
        if imm == -1 {
            return self.emit_move(rd, rs1);
        }

        if rd == rs1 {
            self.emit(And(loc_of_register(rd), Imm(imm as i64)));
        } else {
            self.load_reg(Register::RAX, rs1);
            self.emit(And(Reg(Register::RAX), Imm(imm as i64)));
            self.store_reg(rd, Register::RAX);
        }
    }

    fn emit_addiw(&mut self, rd: u8, rs1: u8, imm: i32) {
        if rd == 0 {
            return;
        }
        if rs1 == 0 {
            return self.emit_load_imm(rd, imm);
        }
        if imm == 0 {
            return self.emit_move32(rd, rs1);
        }

        self.load_reg(Register::EAX, rs1);
        self.emit(Add(Reg(Register::EAX), Imm(imm as i64)));
        self.store_reg(rd, Register::EAX);
    }

    fn emit_slliw(&mut self, rd: u8, rs1: u8, imm: i32) {
        if rd == 0 {
            return;
        }
        if rs1 == 0 {
            return self.emit_load_imm(rd, 0);
        }
        if imm == 0 {
            return self.emit_move32(rd, rs1);
        }

        self.load_reg(Register::EAX, rs1);

        if imm == 1 {
            self.emit(Add(Reg(Register::EAX), OpReg(Register::EAX)))
        } else {
            self.emit(Shl(Reg(Register::EAX), Imm(imm as i64)))
        }
        self.store_reg(rd, Register::EAX);
    }

    fn emit_srliw(&mut self, rd: u8, rs1: u8, imm: i32) {
        if rd == 0 {
            return;
        }
        if rs1 == 0 {
            return self.emit_load_imm(rd, 0);
        }
        if imm == 0 {
            return self.emit_move32(rd, rs1);
        }

        self.load_reg(Register::EAX, rs1);
        self.emit(Shr(Reg(Register::EAX), Imm(imm as i64)));
        self.store_reg(rd, Register::EAX);
    }

    fn emit_sraiw(&mut self, rd: u8, rs1: u8, imm: i32) {
        if rd == 0 {
            return;
        }
        if rs1 == 0 {
            return self.emit_load_imm(rd, 0);
        }
        if imm == 0 {
            return self.emit_move32(rd, rs1);
        }

        self.load_reg(Register::EAX, rs1);
        self.emit(Sar(Reg(Register::EAX), Imm(imm as i64)));
        self.store_reg(rd, Register::EAX);
    }

    fn emit_add(&mut self, rd: u8, rs1: u8, rs2: u8) {
        if rd == 0 {
            return;
        }
        if rs1 == 0 {
            return self.emit_move(rd, rs2);
        }
        if rs2 == 0 {
            return self.emit_move(rd, rs1);
        }

        if rd == rs1 && rd == rs2 {
            return self.emit(Shl(loc_of_register(rd), Imm(1)));
        }

        if rd == rs1 {
            self.load_reg(Register::RAX, rs2);
            self.emit(Add(loc_of_register(rd), OpReg(Register::RAX)));
            return;
        }

        if rd == rs2 {
            self.load_reg(Register::RAX, rs1);
            self.emit(Add(loc_of_register(rd), OpReg(Register::RAX)));
            return;
        }

        if rs1 == rs2 {
            self.load_reg(Register::RAX, rs1);
            self.emit(Add(Reg(Register::RAX), OpReg(Register::RAX)));
            self.store_reg(rd, Register::RAX);
            return;
        }

        self.load_reg(Register::RAX, rs1);
        self.emit(Add(Reg(Register::RAX), loc_of_register(rs2).into()));
        self.store_reg(rd, Register::RAX);
    }

    fn emit_sub(&mut self, rd: u8, rs1: u8, rs2: u8) {
        if rd == 0 {
            return;
        }
        if rs2 == 0 {
            return self.emit_move(rd, rs1);
        }
        if rs1 == rs2 {
            return self.emit_load_imm(rd, 0);
        }

        if rd == rs1 {
            self.load_reg(Register::RAX, rs2);
            self.emit(Sub(loc_of_register(rd), OpReg(Register::RAX)));
            return;
        }

        if rd == rs2 && rs1 == 0 {
            self.emit(Neg(loc_of_register(rd)));
            return;
        }

        if rs1 == 0 {
            self.load_reg(Register::RAX, rs2);
            self.emit(Neg(Reg(Register::RAX)));
            self.store_reg(rd, Register::RAX);
            return;
        }

        self.load_reg(Register::RAX, rs1);
        self.emit(Sub(Reg(Register::RAX), loc_of_register(rs2).into()));
        self.store_reg(rd, Register::RAX);
    }

    fn emit_sll(&mut self, rd: u8, rs1: u8, rs2: u8) {
        if rd == 0 {
            return;
        }
        if rs1 == 0 {
            return self.emit_load_imm(rd, 0);
        }
        if rs2 == 0 {
            return self.emit_move(rd, rs1);
        }

        if rd == rs1 {
            self.emit(Mov(Reg(Register::CL), loc_of_register(rs2).resize(Size::Byte).into()));
            self.emit(Shl(loc_of_register(rd), OpReg(Register::CL)));
            return;
        }

        self.load_reg(Register::RAX, rs1);
        self.emit(Mov(Reg(Register::CL), loc_of_register(rs2).resize(Size::Byte).into()));
        self.emit(Shl(Reg(Register::RAX), OpReg(Register::CL)));
        self.store_reg(rd, Register::RAX);
    }

    fn emit_slt(&mut self, rd: u8, rs1: u8, rs2: u8) {
        if rd == 0 {
            return;
        }
        if rs1 == rs2 {
            return self.emit_load_imm(rd, 0);
        }
        if rs1 == 0 {
            self.emit(Xor(Reg(Register::EAX), OpReg(Register::EAX)));
            self.emit(Cmp(loc_of_register(rs2), Imm(0)));
            self.emit(Setcc(Reg(Register::AL), ConditionCode::Greater));
            self.store_reg(rd, Register::RAX);
            return;
        }

        if rs2 == 0 {
            if rd == rs1 {
                self.emit(Shr(loc_of_register(rd), Imm(63)));
                return;
            }

            self.load_reg(Register::RAX, rs1);
            self.emit(Shr(Reg(Register::RAX), Imm(63)));
            self.store_reg(rd, Register::RAX);
            return;
        }

        self.load_reg(Register::RAX, rs1);
        self.emit(Cmp(Reg(Register::RAX), loc_of_register(rs2).into()));
        self.emit(Setcc(Reg(Register::AL), ConditionCode::Less));
        self.emit(Movzx(Register::EAX, Reg(Register::AL)));
        self.store_reg(rd, Register::RAX);
    }

    fn emit_sltu(&mut self, rd: u8, rs1: u8, rs2: u8) {
        if rd == 0 {
            return;
        }
        if rs2 == 0 || rs1 == rs2 {
            return self.emit_load_imm(rd, 0);
        }

        if rs1 == 0 {
            self.emit(Xor(Reg(Register::EAX), OpReg(Register::EAX)));
            self.emit(Cmp(loc_of_register(rs2), Imm(0)));
            self.emit(Setcc(Reg(Register::AL), ConditionCode::NotEqual));
            self.store_reg(rd, Register::RAX);
            return;
        }

        self.load_reg(Register::RAX, rs1);
        self.emit(Cmp(Reg(Register::RAX), loc_of_register(rs2).into()));
        self.emit(Setcc(Reg(Register::AL), ConditionCode::Below));
        self.emit(Movzx(Register::EAX, Reg(Register::AL)));
        self.store_reg(rd, Register::RAX);
    }

    fn emit_xor(&mut self, rd: u8, rs1: u8, rs2: u8) {
        if rd == 0 {
            return;
        }
        if rs1 == 0 {
            return self.emit_move(rd, rs2);
        }
        if rs2 == 0 {
            return self.emit_move(rd, rs1);
        }
        if rs1 == rs2 {
            return self.emit_load_imm(rd, 0);
        }

        if rd == rs1 {
            self.load_reg(Register::RAX, rs2);
            self.emit(Xor(loc_of_register(rd), OpReg(Register::RAX)));
            return;
        }

        if rd == rs2 {
            self.load_reg(Register::RAX, rs1);
            self.emit(Xor(loc_of_register(rd), OpReg(Register::RAX)));
            return;
        }

        self.load_reg(Register::RAX, rs1);
        self.emit(Xor(Reg(Register::RAX), loc_of_register(rs2).into()));
        self.store_reg(rd, Register::RAX);
    }

    fn emit_srl(&mut self, rd: u8, rs1: u8, rs2: u8) {
        if rd == 0 {
            return;
        }
        if rs1 == 0 {
            return self.emit_load_imm(rd, 0);
        }
        if rs2 == 0 {
            return self.emit_move(rd, rs1);
        }

        if rd == rs1 {
            self.emit(Mov(Reg(Register::CL), loc_of_register(rs2).resize(Size::Byte).into()));
            self.emit(Shr(loc_of_register(rd), OpReg(Register::CL)));
            return;
        }

        self.load_reg(Register::RAX, rs1);
        self.emit(Mov(Reg(Register::CL), loc_of_register(rs2).resize(Size::Byte).into()));
        self.emit(Shr(Reg(Register::RAX), OpReg(Register::CL)));
        self.store_reg(rd, Register::RAX);
    }

    fn emit_sra(&mut self, rd: u8, rs1: u8, rs2: u8) {
        if rd == 0 {
            return;
        }
        if rs1 == 0 {
            return self.emit_load_imm(rd, 0);
        }
        if rs2 == 0 {
            return self.emit_move(rd, rs1);
        }

        if rd == rs1 {
            self.emit(Mov(Reg(Register::CL), loc_of_register(rs2).resize(Size::Byte).into()));
            self.emit(Sar(loc_of_register(rd), OpReg(Register::CL)));
            return;
        }

        self.load_reg(Register::RAX, rs1);
        self.emit(Mov(Reg(Register::CL), loc_of_register(rs2).resize(Size::Byte).into()));
        self.emit(Sar(Reg(Register::RAX), OpReg(Register::CL)));
        self.store_reg(rd, Register::RAX);
    }

    fn emit_or(&mut self, rd: u8, rs1: u8, rs2: u8) {
        if rd == 0 {
            return;
        }
        if rs1 == 0 {
            return self.emit_move(rd, rs2);
        }
        if rs2 == 0 {
            return self.emit_move(rd, rs1);
        }
        if rs1 == rs2 {
            return self.emit_move(rd, rs1);
        }

        if rd == rs1 {
            self.load_reg(Register::RAX, rs2);
            self.emit(Or(loc_of_register(rd), OpReg(Register::RAX)));
            return;
        }

        if rd == rs2 {
            self.load_reg(Register::RAX, rs1);
            self.emit(Or(loc_of_register(rd), OpReg(Register::RAX)));
            return;
        }

        self.load_reg(Register::RAX, rs1);
        self.emit(Or(Reg(Register::RAX), loc_of_register(rs2).into()));
        self.store_reg(rd, Register::RAX);
    }

    fn emit_and(&mut self, rd: u8, rs1: u8, rs2: u8) {
        if rd == 0 {
            return;
        }
        if rs1 == 0 || rs2 == 0 {
            return self.emit_load_imm(rd, 0);
        }
        if rs1 == rs2 {
            return self.emit_move(rd, rs1);
        }

        if rd == rs1 {
            self.load_reg(Register::RAX, rs2);
            self.emit(And(loc_of_register(rd), OpReg(Register::RAX)));
            return;
        }

        if rd == rs2 {
            self.load_reg(Register::RAX, rs1);
            self.emit(And(loc_of_register(rd), OpReg(Register::RAX)));
            return;
        }

        self.load_reg(Register::RAX, rs1);
        self.emit(And(Reg(Register::RAX), loc_of_register(rs2).into()));
        self.store_reg(rd, Register::RAX);
    }

    fn emit_addw(&mut self, rd: u8, rs1: u8, rs2: u8) {
        if rd == 0 {
            return;
        }
        if rs1 == 0 {
            return self.emit_move32(rd, rs2);
        }
        if rs2 == 0 {
            return self.emit_move32(rd, rs1);
        }

        self.load_reg(Register::EAX, rs1);
        if rs1 == rs2 {
            self.emit(Add(Reg(Register::EAX), OpReg(Register::EAX)));
        } else {
            self.emit(Add(Reg(Register::EAX), loc_of_register(rs2).resize(Size::Dword).into()));
        }
        self.store_reg(rd, Register::EAX);
    }

    fn emit_subw(&mut self, rd: u8, rs1: u8, rs2: u8) {
        if rd == 0 {
            return;
        }
        if rs2 == 0 {
            return self.emit_move32(rd, rs1);
        }
        if rs1 == rs2 {
            return self.emit_load_imm(rd, 0);
        }

        if rs1 == 0 {
            self.load_reg(Register::EAX, rs2);
            self.emit(Neg(Reg(Register::EAX)));
        } else {
            self.load_reg(Register::EAX, rs1);
            self.emit(Sub(Reg(Register::EAX), loc_of_register(rs2).resize(Size::Dword).into()));
        }
        self.store_reg(rd, Register::EAX);
    }

    fn emit_sllw(&mut self, rd: u8, rs1: u8, rs2: u8) {
        if rd == 0 {
            return;
        }
        if rs1 == 0 {
            return self.emit_load_imm(rd, 0);
        }
        if rs2 == 0 {
            return self.emit_move32(rd, rs1);
        }

        self.load_reg(Register::EAX, rs1);
        self.emit(Mov(Reg(Register::CL), loc_of_register(rs2).resize(Size::Byte).into()));
        self.emit(Shl(Reg(Register::EAX), OpReg(Register::CL)));
        self.store_reg(rd, Register::EAX);
    }

    fn emit_srlw(&mut self, rd: u8, rs1: u8, rs2: u8) {
        if rd == 0 {
            return;
        }
        if rs1 == 0 {
            return self.emit_load_imm(rd, 0);
        }
        if rs2 == 0 {
            return self.emit_move32(rd, rs1);
        }

        self.load_reg(Register::EAX, rs1);
        self.emit(Mov(Reg(Register::CL), loc_of_register(rs2).resize(Size::Byte).into()));
        self.emit(Shr(Reg(Register::EAX), OpReg(Register::CL)));
        self.store_reg(rd, Register::EAX);
    }

    fn emit_sraw(&mut self, rd: u8, rs1: u8, rs2: u8) {
        if rd == 0 {
            return;
        }
        if rs1 == 0 {
            return self.emit_load_imm(rd, 0);
        }
        if rs2 == 0 {
            return self.emit_move32(rd, rs1);
        }

        self.load_reg(Register::EAX, rs1);
        self.emit(Mov(Reg(Register::CL), loc_of_register(rs2).resize(Size::Byte).into()));
        self.emit(Sar(Reg(Register::EAX), OpReg(Register::CL)));
        self.store_reg(rd, Register::EAX);
    }

    fn emit_mul(&mut self, rd: u8, rs1: u8, rs2: u8) {
        if rd == 0 {
            return;
        }
        if rs1 == 0 || rs2 == 0 {
            return self.emit_load_imm(rd, 0);
        }

        self.load_reg(Register::RAX, rs1);
        if rs1 == rs2 {
            self.emit(Imul2(Register::RAX, Reg(Register::RAX)));
        } else {
            self.emit(Imul2(Register::RAX, loc_of_register(rs2)));
        }
        self.store_reg(rd, Register::RAX);
    }

    fn emit_mulh(&mut self, rd: u8, rs1: u8, rs2: u8, unsigned: bool) {
        if rd == 0 {
            return;
        }
        if rs1 == 0 || rs2 == 0 {
            return self.emit_load_imm(rd, 0);
        }

        self.load_reg(Register::RAX, rs1);
        let loc = if rs1 == rs2 { Reg(Register::RAX) } else { loc_of_register(rs2) };
        if unsigned {
            self.emit(Mul(loc))
        } else {
            self.emit(Imul1(loc))
        }
        self.emit(Mov(loc_of_register(rd), OpReg(Register::RDX)));
    }

    fn emit_mulhsu(&mut self, rd: u8, rs1: u8, rs2: u8) {
        if rd == 0 {
            return;
        }
        if rs1 == 0 || rs2 == 0 {
            return self.emit_load_imm(rd, 0);
        }

        self.emit(Mov(Reg(Register::RCX), loc_of_register(rs1).into()));
        self.emit(Mov(Reg(Register::RSI), loc_of_register(rs2).into()));
        self.emit(Mov(Reg(Register::RAX), OpReg(Register::RCX)));
        self.emit(Mul(Reg(Register::RSI)));

        self.emit(Sar(Reg(Register::RCX), Imm(63)));
        self.emit(And(Reg(Register::RCX), OpReg(Register::RSI)));
        self.emit(Sub(Reg(Register::RDX), OpReg(Register::RCX)));
        self.emit(Mov(loc_of_register(rd), OpReg(Register::RDX)));
    }

    fn emit_mulw(&mut self, rd: u8, rs1: u8, rs2: u8) {
        if rd == 0 {
            return;
        }
        if rs1 == 0 || rs2 == 0 {
            return self.emit_load_imm(rd, 0);
        }

        self.load_reg(Register::EAX, rs1);
        if rs1 == rs2 {
            self.emit(Imul2(Register::EAX, Reg(Register::EAX)));
        } else {
            self.emit(Imul2(Register::EAX, loc_of_register(rs2).resize(Size::Dword)));
        }
        self.store_reg(rd, Register::EAX);
    }

    fn emit_div(&mut self, rd: u8, rs1: u8, rs2: u8, unsigned: bool, rem: bool) {
        if rd == 0 {
            return;
        }

        if rs2 == 0 {
            if rem {
                self.emit_move(rd, rs1);
            } else {
                self.emit_load_imm(rd, -1);
            }
            return;
        }

        self.load_reg(Register::RAX, rs1);

        if unsigned {
            self.emit(Xor(Reg(Register::EDX), OpReg(Register::EDX)));
            self.emit(Div(loc_of_register(rs2)));
        } else {
            self.emit(Cqo);
            self.emit(Idiv(loc_of_register(rs2)));
        }

        if rem {
            self.emit(Mov(loc_of_register(rd), OpReg(Register::RDX)));
        } else {
            self.store_reg(rd, Register::RAX);
        }
    }

    fn emit_divw(&mut self, rd: u8, rs1: u8, rs2: u8, unsigned: bool, rem: bool) {
        if rd == 0 {
            return;
        }

        if rs2 == 0 {
            if rem {
                self.emit_move32(rd, rs1);
            } else {
                self.emit_load_imm(rd, -1);
            }
            return;
        }

        self.load_reg(Register::EAX, rs1);

        if unsigned {
            self.emit(Xor(Reg(Register::EDX), OpReg(Register::EDX)));
            self.emit(Div(loc_of_register(rs2).resize(Size::Dword)));
        } else {
            self.emit(Cdq);
            self.emit(Idiv(loc_of_register(rs2).resize(Size::Dword)));
        }

        if rem {
            self.emit(Movsx(Register::RAX, Reg(Register::EDX)));
            self.store_reg(rd, Register::RAX);
        } else {
            self.store_reg(rd, Register::EAX);
        }
    }

    fn amo_op_w(&mut self, rd: u8, rs1: u8, rs2: u8, action: impl FnOnce(&mut Self)) {
        self.before_side_effect();

        self.minstret += 1;
        self.load_reg(Register::RSI, rs1);
        self.dcache_access(Size::Dword, true);
        self.load_reg(Register::EAX, rs2);

        action(self);
        self.store_reg(rd, Register::EAX);
    }

    fn amo_op_d(&mut self, rd: u8, rs1: u8, rs2: u8, action: impl FnOnce(&mut Self)) {
        self.before_side_effect();

        self.minstret += 1;
        self.load_reg(Register::RSI, rs1);
        self.dcache_access(Size::Qword, true);
        self.load_reg(Register::RAX, rs2);

        action(self);
        self.store_reg(rd, Register::RAX);
    }

    fn cmpxchg_w(&mut self, rd: u8, rs1: u8, rs2: u8, action: impl FnOnce(&mut Self)) {
        self.before_side_effect();

        self.minstret += 1;
        self.load_reg(Register::RSI, rs1);
        self.dcache_access(Size::Dword, true);
        self.load_reg(Register::EDX, rs2);
        let mem = Mem((Register::RSI + 0).dword());

        self.emit(Mov(Register::EAX.into(), mem.into()));
        let label_retry = self.label();
        self.emit(Mov(Register::ECX.into(), Register::EAX.into()));

        action(self);
        self.emit(Lock);
        self.emit(Cmpxchg(mem, Register::ECX));
        let jcc_retry = self.emit_jcc_short(ConditionCode::NotEqual);
        self.patch(jcc_retry, label_retry);
        self.store_reg(rd, Register::EAX);
    }

    fn cmpxchg_d(&mut self, rd: u8, rs1: u8, rs2: u8, action: impl FnOnce(&mut Self)) {
        self.before_side_effect();

        self.minstret += 1;
        self.load_reg(Register::RSI, rs1);
        self.dcache_access(Size::Qword, true);
        self.load_reg(Register::RDX, rs2);
        let mem = Mem(Register::RSI + 0);

        self.emit(Mov(Register::RAX.into(), mem.into()));
        let label_retry = self.label();
        self.emit(Mov(Register::RCX.into(), Register::RAX.into()));

        action(self);
        self.emit(Lock);
        self.emit(Cmpxchg(mem, Register::RCX));
        let jcc_retry = self.emit_jcc_short(ConditionCode::NotEqual);
        self.patch(jcc_retry, label_retry);
        self.store_reg(rd, Register::RAX);
    }

    fn emit_read_csr(&mut self, csr: riscv::Csr) {
        self.emit(Mov(Reg(Register::RDI), OpReg(Register::RBP)));
        self.emit(Mov(Reg(Register::ESI), Imm(csr.0 as i64)));
        self.emit_helper_call(read_csr);
    }

    fn emit_write_csr(&mut self, csr: riscv::Csr) {
        self.emit(Mov(Reg(Register::RDI), OpReg(Register::RBP)));
        self.emit(Mov(Reg(Register::ESI), Imm(csr.0 as i64)));
        self.emit_helper_call(write_csr);
    }

    fn emit_trap_check(&mut self) {
        self.emit(Test(Reg(Register::AL), OpReg(Register::AL)));
        let trap = self.emit_jcc_long(ConditionCode::NotEqual);
        let ebx = self.get_ebx();
        self.slow_path.push(SlowPath::Trap(ebx, trap));
    }

    fn emit_op(&mut self, op: &Op, comp: bool) {
        match *op {
            /* LOAD */
            Op::Lb { rd, rs1, imm } => {
                self.emit_load(rs1, imm, Size::Byte);
                self.emit(Movsx(Register::RAX, Mem((Register::RSI + 0).byte())));
                self.store_reg(rd, Register::RAX);
            }
            Op::Lh { rd, rs1, imm } => {
                self.emit_load(rs1, imm, Size::Word);
                self.emit(Movsx(Register::RAX, Mem((Register::RSI + 0).word())));
                self.store_reg(rd, Register::RAX);
            }
            Op::Lw { rd, rs1, imm } => {
                self.emit_load(rs1, imm, Size::Dword);
                self.emit(Movsx(Register::RAX, Mem((Register::RSI + 0).dword())));
                self.store_reg(rd, Register::RAX);
            }
            Op::Ld { rd, rs1, imm } => {
                self.emit_load(rs1, imm, Size::Qword);
                self.emit(Mov(Reg(Register::RAX), OpMem((Register::RSI + 0).qword())));
                self.store_reg(rd, Register::RAX);
            }
            Op::Lbu { rd, rs1, imm } => {
                self.emit_load(rs1, imm, Size::Byte);
                self.emit(Movzx(Register::RAX, Mem((Register::RSI + 0).byte())));
                self.store_reg(rd, Register::RAX);
            }
            Op::Lhu { rd, rs1, imm } => {
                self.emit_load(rs1, imm, Size::Word);
                self.emit(Movzx(Register::RAX, Mem((Register::RSI + 0).word())));
                self.store_reg(rd, Register::RAX);
            }
            Op::Lwu { rd, rs1, imm } => {
                self.emit_load(rs1, imm, Size::Dword);
                self.emit(Mov(Reg(Register::EAX), OpMem((Register::RSI + 0).dword())));
                self.store_reg(rd, Register::RAX);
            }
            /* OP-IMM */
            Op::Addi { rd, rs1, imm } => self.emit_addi(rd, rs1, imm),
            Op::Slli { rd, rs1, imm } => self.emit_slli(rd, rs1, imm),
            Op::Slti { rd, rs1, imm } => self.emit_slti(rd, rs1, imm),
            Op::Sltiu { rd, rs1, imm } => self.emit_sltiu(rd, rs1, imm),
            Op::Xori { rd, rs1, imm } => self.emit_xori(rd, rs1, imm),
            Op::Srli { rd, rs1, imm } => self.emit_srli(rd, rs1, imm),
            Op::Srai { rd, rs1, imm } => self.emit_srai(rd, rs1, imm),
            Op::Ori { rd, rs1, imm } => self.emit_ori(rd, rs1, imm),
            Op::Andi { rd, rs1, imm } => self.emit_andi(rd, rs1, imm),
            /* MISC-MEM */
            Op::Fence => self.emit(Mfence),
            /* OP-IMM-32 */
            Op::Addiw { rd, rs1, imm } => self.emit_addiw(rd, rs1, imm),
            Op::Slliw { rd, rs1, imm } => self.emit_slliw(rd, rs1, imm),
            Op::Srliw { rd, rs1, imm } => self.emit_srliw(rd, rs1, imm),
            Op::Sraiw { rd, rs1, imm } => self.emit_sraiw(rd, rs1, imm),
            /* STORE */
            Op::Sb { rs1, rs2, imm } => self.emit_store(rs1, rs2, imm, Size::Byte),
            Op::Sh { rs1, rs2, imm } => self.emit_store(rs1, rs2, imm, Size::Word),
            Op::Sw { rs1, rs2, imm } => self.emit_store(rs1, rs2, imm, Size::Dword),
            Op::Sd { rs1, rs2, imm } => self.emit_store(rs1, rs2, imm, Size::Qword),
            /* OP */
            Op::Add { rd, rs1, rs2 } => self.emit_add(rd, rs1, rs2),
            Op::Sub { rd, rs1, rs2 } => self.emit_sub(rd, rs1, rs2),
            Op::Sll { rd, rs1, rs2 } => self.emit_sll(rd, rs1, rs2),
            Op::Slt { rd, rs1, rs2 } => self.emit_slt(rd, rs1, rs2),
            Op::Sltu { rd, rs1, rs2 } => self.emit_sltu(rd, rs1, rs2),
            Op::Xor { rd, rs1, rs2 } => self.emit_xor(rd, rs1, rs2),
            Op::Srl { rd, rs1, rs2 } => self.emit_srl(rd, rs1, rs2),
            Op::Sra { rd, rs1, rs2 } => self.emit_sra(rd, rs1, rs2),
            Op::Or { rd, rs1, rs2 } => self.emit_or(rd, rs1, rs2),
            Op::And { rd, rs1, rs2 } => self.emit_and(rd, rs1, rs2),
            /* LUI */
            Op::Lui { rd, imm } => self.emit_load_imm(rd, imm),
            /* OP-32 */
            Op::Addw { rd, rs1, rs2 } => self.emit_addw(rd, rs1, rs2),
            Op::Subw { rd, rs1, rs2 } => self.emit_subw(rd, rs1, rs2),
            Op::Sllw { rd, rs1, rs2 } => self.emit_sllw(rd, rs1, rs2),
            Op::Srlw { rd, rs1, rs2 } => self.emit_srlw(rd, rs1, rs2),
            Op::Sraw { rd, rs1, rs2 } => self.emit_sraw(rd, rs1, rs2),
            /* AUIPC */
            Op::Auipc { rd, imm } => {
                let imm = imm as i64 + self.pc_cur;
                self.emit(Mov(Reg(Register::RAX), OpMem(memory_of!(pc))));
                self.emit(Add(Reg(Register::RAX), Imm(imm)));
                self.store_reg(rd, Register::RAX);
            }
            /* BRANCH */
            Op::Beq { rs1, rs2, imm } => self.emit_branch(rs1, rs2, imm, ConditionCode::Equal, op, comp),
            Op::Bne { rs1, rs2, imm } => self.emit_branch(rs1, rs2, imm, ConditionCode::NotEqual, op, comp),
            Op::Blt { rs1, rs2, imm } => self.emit_branch(rs1, rs2, imm, ConditionCode::Less, op, comp),
            Op::Bge { rs1, rs2, imm } => self.emit_branch(rs1, rs2, imm, ConditionCode::GreaterEqual, op, comp),
            Op::Bltu { rs1, rs2, imm } => self.emit_branch(rs1, rs2, imm, ConditionCode::Below, op, comp),
            Op::Bgeu { rs1, rs2, imm } => self.emit_branch(rs1, rs2, imm, ConditionCode::AboveEqual, op, comp),
            /* JALR */
            Op::Jalr { rd, rs1, imm } => self.emit_jalr(rd, rs1, imm, op, comp),
            /* JAL */
            Op::Jal { rd, imm } => self.emit_jal(rd, imm, op, comp),
            /* SYSTEM */
            Op::Csrrw { csr, .. } |
            Op::Csrrs { csr, .. } |
            Op::Csrrc { csr, .. } |
            Op::Csrrwi { csr, .. } |
            Op::Csrrsi { csr, .. } |
            Op::Csrrci { csr, .. } if match csr {
                Csr::Instret |
                Csr::Instreth |
                Csr::Satp |
                Csr(0x800) | Csr(0x801) => true,
                _ => false,
            } => {
                self.pre_adjust_pc_instret(comp);
                let backup = (self.pc_cur, self.instret);
                self.pc_cur = if comp { -2 } else { -4 };
                self.instret = -1;
                self.emit_step_call(op);
                self.pc_cur = backup.0;
                self.instret = backup.1;
                self.with_model(|this, model| model.after_instruction(this, op, comp));
                self.emit_interrupt_check();
                self.emit_chain_tail();
            }
            Op::Csrrw { rd: 0, rs1, csr } => {
                self.before_side_effect();
                self.load_reg(Register::RDX, rs1);
                self.emit_write_csr(csr);
                self.emit_trap_check();
            }
            Op::Csrrwi { rd: 0, imm, csr } => {
                self.before_side_effect();
                self.emit(Mov(Reg(Register::RDX), Imm(imm as i64)));
                self.emit_write_csr(csr);
                self.emit_trap_check();
            }
            Op::Csrrs { rd, rs1: 0, csr } |
            Op::Csrrc { rd, rs1: 0, csr } |
            Op::Csrrsi { rd, imm: 0, csr } |
            Op::Csrrci { rd, imm: 0, csr } => {
                self.before_side_effect();
                self.emit_read_csr(csr);
                self.emit_trap_check();
                if rd != 0 {
                    self.store_reg(rd, Register::RDX);
                }
            }
            Op::Csrrw {..} |
            Op::Csrrs {..} |
            Op::Csrrc {..} |
            Op::Csrrwi {..} |
            Op::Csrrsi {..} |
            Op::Csrrci {..} => self.emit_step_call(op),

            /* F-extension */
            Op::Flw {..} |
            Op::Fsw {..} |
            Op::FaddS {..} |
            Op::FsubS {..} |
            Op::FmulS {..} |
            Op::FdivS {..} |
            Op::FsqrtS {..} |
            Op::FsgnjS {..} |
            Op::FsgnjnS {..} |
            Op::FsgnjxS {..} |
            Op::FminS {..} |
            Op::FmaxS {..} |
            Op::FcvtWS {..} |
            Op::FcvtWuS {..} |
            Op::FcvtLS {..} |
            Op::FcvtLuS {..} |
            Op::FmvXW {..} |
            Op::FclassS {..} |
            Op::FeqS {..} |
            Op::FltS {..} |
            Op::FleS {..} |
            Op::FcvtSW {..} |
            Op::FcvtSWu {..} |
            Op::FcvtSL {..} |
            Op::FcvtSLu {..} |
            Op::FmvWX {..} |
            Op::FmaddS {..} |
            Op::FmsubS {..} |
            Op::FnmsubS {..} |
            Op::FnmaddS {..} |
            /* D-extension */
            Op::Fld {..} |
            Op::Fsd {..} |
            Op::FaddD {..} |
            Op::FsubD {..} |
            Op::FmulD {..} |
            Op::FdivD {..} |
            Op::FsqrtD {..} |
            Op::FsgnjD {..} |
            Op::FsgnjnD {..} |
            Op::FsgnjxD {..} |
            Op::FminD {..} |
            Op::FmaxD {..} |
            Op::FcvtSD {..} |
            Op::FcvtDS {..} |
            Op::FcvtWD {..} |
            Op::FcvtWuD {..} |
            Op::FcvtLD {..} |
            Op::FcvtLuD {..} |
            Op::FmvXD {..} |
            Op::FclassD {..} |
            Op::FeqD {..} |
            Op::FltD {..} |
            Op::FleD {..} |
            Op::FcvtDW {..} |
            Op::FcvtDWu {..} |
            Op::FcvtDL {..} |
            Op::FcvtDLu {..} |
            Op::FmvDX {..} |
            Op::FmaddD {..} |
            Op::FmsubD {..} |
            Op::FnmsubD {..} |
            Op::FnmaddD {..} => self.emit_step_call(op),

            /* M-extension */
            Op::Mul { rd, rs1, rs2 } => self.emit_mul(rd, rs1, rs2),
            Op::Mulh { rd, rs1, rs2 } => self.emit_mulh(rd, rs1, rs2, false),
            Op::Mulhsu { rd, rs1, rs2 } => self.emit_mulhsu(rd, rs1, rs2),
            Op::Mulhu { rd, rs1, rs2 } => self.emit_mulh(rd, rs1, rs2, true),
            Op::Div { rd, rs1, rs2 } => self.emit_div(rd, rs1, rs2, false, false),
            Op::Divu { rd, rs1, rs2 } => self.emit_div(rd, rs1, rs2, true, false),
            Op::Rem { rd, rs1, rs2 } => self.emit_div(rd, rs1, rs2, false, true),
            Op::Remu { rd, rs1, rs2 } => self.emit_div(rd, rs1, rs2, true, true),
            Op::Mulw { rd, rs1, rs2 } => self.emit_mulw(rd, rs1, rs2),
            Op::Divw { rd, rs1, rs2 } => self.emit_divw(rd, rs1, rs2, false, false),
            Op::Divuw { rd, rs1, rs2 } => self.emit_divw(rd, rs1, rs2, true, false),
            Op::Remw { rd, rs1, rs2 } => self.emit_divw(rd, rs1, rs2, false, true),
            Op::Remuw { rd, rs1, rs2 } => self.emit_divw(rd, rs1, rs2, true, true),

            /* A-extension */
            Op::LrW { rd, rs1, .. } => {
                self.before_side_effect();

                self.minstret += 1;
                self.load_reg(Register::RSI, rs1);
                self.emit(Mov(Reg(Register::RBX), OpReg(Register::RSI)));
                self.dcache_access(Size::Dword, true);
                self.emit(Movsx(Register::RAX, Mem((Register::RSI + 0).dword())));
                self.store_reg(rd, Register::RAX);
                self.emit(Mov(Mem(memory_of!(lr_addr)), OpReg(Register::RBX)));
                self.emit(Mov(Mem(memory_of!(lr_value)), OpReg(Register::RAX)));
            }
            Op::LrD { rd, rs1, .. } => {
                self.before_side_effect();

                self.minstret += 1;
                self.load_reg(Register::RSI, rs1);
                self.emit(Mov(Reg(Register::RBX), OpReg(Register::RSI)));
                self.dcache_access(Size::Qword, true);
                self.emit(Mov(Reg(Register::RAX), OpMem(Register::RSI + 0)));
                self.store_reg(rd, Register::RAX);
                self.emit(Mov(Mem(memory_of!(lr_addr)), OpReg(Register::RBX)));
                self.emit(Mov(Mem(memory_of!(lr_value)), OpReg(Register::RAX)));
            }
            Op::ScW { rd, rs1, rs2, .. } => {
                self.before_side_effect();
                self.load_reg(Register::RSI, rs1);
                self.emit(Cmp(Mem(memory_of!(lr_addr)), Register::RSI.into()));
                let jcc_addr_mismatch = self.emit_jcc_short(ConditionCode::NotEqual);
                self.dcache_access(Size::Dword, true);
                self.emit(Mov(Register::EAX.into(), OpMem(memory_of!(lr_value).dword())));
                self.load_reg(Register::EDX, rs2);
                self.emit(Lock);
                self.emit(Cmpxchg(Mem((Register::RSI + 0).dword()), Register::EDX));
                let label = self.label();
                self.patch(jcc_addr_mismatch, label);
                self.emit(Setcc(Register::CL.into(), ConditionCode::NotEqual));
                self.emit(Movsx(Register::ECX, Register::CL.into()));
                self.store_reg(rd, Register::RCX);
            }
            Op::ScD { rd, rs1, rs2, .. } => {
                self.before_side_effect();

                self.load_reg(Register::RSI, rs1);
                self.emit(Cmp(Mem(memory_of!(lr_addr)), Register::RSI.into()));
                let jcc_addr_mismatch = self.emit_jcc_short(ConditionCode::NotEqual);
                self.dcache_access(Size::Qword, true);
                self.emit(Mov(Register::RAX.into(), OpMem(memory_of!(lr_value))));
                self.load_reg(Register::RDX, rs2);
                self.emit(Lock);
                self.emit(Cmpxchg(Mem(Register::RSI + 0), Register::RDX));
                let label = self.label();
                self.patch(jcc_addr_mismatch, label);
                self.emit(Setcc(Register::CL.into(), ConditionCode::NotEqual));
                self.emit(Movsx(Register::ECX, Register::CL.into()));
                self.store_reg(rd, Register::RCX);
            }
            Op::AmoswapW { rd, rs1, rs2, .. } => self.amo_op_w(rd, rs1, rs2, |this| {
                this.emit(Xchg(Reg(Register::EAX), Mem((Register::RSI + 0).dword())));
            }),
            Op::AmoswapD { rd, rs1, rs2, .. } => self.amo_op_d(rd, rs1, rs2, |this| {
                this.emit(Xchg(Reg(Register::RAX), Mem(Register::RSI + 0)));
            }),
            Op::AmoaddW { rd: 0, rs1, rs2, .. } => self.amo_op_w(0, rs1, rs2, |this| {
                this.emit(Lock);
                this.emit(Add(Mem((Register::RSI + 0).dword()), OpReg(Register::EAX)));
            }),
            Op::AmoaddW { rd, rs1, rs2, .. } => self.amo_op_w(rd, rs1, rs2, |this| {
                this.emit(Lock);
                this.emit(Xadd(Mem((Register::RSI + 0).dword()), Register::EAX));
            }),
            Op::AmoaddD { rd: 0, rs1, rs2, .. } => self.amo_op_d(0, rs1, rs2, |this| {
                this.emit(Lock);
                this.emit(Add(Mem(Register::RSI + 0), OpReg(Register::RAX)));
            }),
            Op::AmoaddD { rd, rs1, rs2, .. } => self.amo_op_d(rd, rs1, rs2, |this| {
                this.emit(Lock);
                this.emit(Xadd(Mem(Register::RSI + 0), Register::RAX));
            }),
            Op::AmoandW { rd: 0, rs1, rs2, .. } => self.amo_op_w(0, rs1, rs2, |this| {
                this.emit(Lock);
                this.emit(And(Mem((Register::RSI + 0).dword()), OpReg(Register::EAX)));
            }),
            Op::AmoandW { rd, rs1, rs2, .. } => self.cmpxchg_w(rd, rs1, rs2, |this| {
                this.emit(And(Register::ECX.into(), Register::EDX.into()));
            }),
            Op::AmoandD { rd: 0, rs1, rs2, .. } => self.amo_op_d(0, rs1, rs2, |this| {
                this.emit(Lock);
                this.emit(And(Mem(Register::RSI + 0), OpReg(Register::RAX)));
            }),
            Op::AmoandD { rd, rs1, rs2, .. } => self.cmpxchg_d(rd, rs1, rs2, |this| {
                this.emit(And(Register::RCX.into(), Register::RDX.into()));
            }),
            Op::AmoorW { rd: 0, rs1, rs2, .. } => self.amo_op_w(0, rs1, rs2, |this| {
                this.emit(Lock);
                this.emit(Or(Mem((Register::RSI + 0).dword()), OpReg(Register::EAX)));
            }),
            Op::AmoorW { rd, rs1, rs2, .. } => self.cmpxchg_w(rd, rs1, rs2, |this| {
                this.emit(Or(Register::ECX.into(), Register::EDX.into()));
            }),
            Op::AmoorD { rd: 0, rs1, rs2, .. } => self.amo_op_d(0, rs1, rs2, |this| {
                this.emit(Lock);
                this.emit(Or(Mem(Register::RSI + 0), OpReg(Register::RAX)));
            }),
            Op::AmoorD { rd, rs1, rs2, .. } => self.cmpxchg_d(rd, rs1, rs2, |this| {
                this.emit(Or(Register::RCX.into(), Register::RDX.into()));
            }),
            Op::AmoxorW { rd: 0, rs1, rs2, .. } => self.amo_op_w(0, rs1, rs2, |this| {
                this.emit(Lock);
                this.emit(Xor(Mem((Register::RSI + 0).dword()), OpReg(Register::EAX)));
            }),
            Op::AmoxorW { rd, rs1, rs2, .. } => self.cmpxchg_w(rd, rs1, rs2, |this| {
                this.emit(Xor(Register::ECX.into(), Register::EDX.into()));
            }),
            Op::AmoxorD { rd: 0, rs1, rs2, .. } => self.amo_op_d(0, rs1, rs2, |this| {
                this.emit(Lock);
                this.emit(Xor(Mem(Register::RSI + 0), OpReg(Register::RAX)));
            }),
            Op::AmoxorD { rd, rs1, rs2, .. } => self.cmpxchg_d(rd, rs1, rs2, |this| {
                this.emit(Xor(Register::RCX.into(), Register::RDX.into()));
            }),
            Op::AmominW { rd, rs1, rs2, .. } => self.cmpxchg_w(rd, rs1, rs2, |this| {
                this.emit(Cmp(Register::EDX.into(), Register::ECX.into()));
                this.emit(Cmovcc(Register::ECX, Register::EDX.into(), ConditionCode::Less));
            }),
            Op::AmominD { rd, rs1, rs2, .. } => self.cmpxchg_d(rd, rs1, rs2, |this| {
                this.emit(Cmp(Register::RDX.into(), Register::RCX.into()));
                this.emit(Cmovcc(Register::RCX, Register::RDX.into(), ConditionCode::Less));
            }),
            Op::AmomaxW { rd, rs1, rs2, .. } => self.cmpxchg_w(rd, rs1, rs2, |this| {
                this.emit(Cmp(Register::EDX.into(), Register::ECX.into()));
                this.emit(Cmovcc(Register::ECX, Register::EDX.into(), ConditionCode::Greater));
            }),
            Op::AmomaxD { rd, rs1, rs2, .. } => self.cmpxchg_d(rd, rs1, rs2, |this| {
                this.emit(Cmp(Register::RDX.into(), Register::RCX.into()));
                this.emit(Cmovcc(Register::RCX, Register::RDX.into(), ConditionCode::Greater));
            }),
            Op::AmominuW { rd, rs1, rs2, .. } => self.cmpxchg_w(rd, rs1, rs2, |this| {
                this.emit(Cmp(Register::EDX.into(), Register::ECX.into()));
                this.emit(Cmovcc(Register::ECX, Register::EDX.into(), ConditionCode::Below));
            }),
            Op::AmominuD { rd, rs1, rs2, .. } => self.cmpxchg_d(rd, rs1, rs2, |this| {
                this.emit(Cmp(Register::RDX.into(), Register::RCX.into()));
                this.emit(Cmovcc(Register::RCX, Register::RDX.into(), ConditionCode::Below));
            }),
            Op::AmomaxuW { rd, rs1, rs2, .. } => self.cmpxchg_w(rd, rs1, rs2, |this| {
                this.emit(Cmp(Register::EDX.into(), Register::ECX.into()));
                this.emit(Cmovcc(Register::ECX, Register::EDX.into(), ConditionCode::Above));
            }),
            Op::AmomaxuD { rd, rs1, rs2, .. } => self.cmpxchg_d(rd, rs1, rs2, |this| {
                this.emit(Cmp(Register::RDX.into(), Register::RCX.into()));
                this.emit(Cmovcc(Register::RCX, Register::RDX.into(), ConditionCode::Above));
            }),

            /* Privileged */
            Op::Wfi => {
                if crate::threaded() || !crate::get_flags().wfi_nop {
                    self.emit_step_call(op)
                }
            }

            /* OPs that can disrupt control flow */
            Op::Mret |
            Op::Sret |
            Op::Ecall |
            Op::Ebreak |
            Op::Illegal |
            Op::FenceI |
            Op::SfenceVma {..} => {
                self.pre_adjust_pc_instret(comp);
                let backup = (self.pc_cur, self.instret);
                self.pc_cur = if comp { -2 } else { -4 };
                self.instret = -1;
                self.emit_step_call(op);
                self.pc_cur = backup.0;
                self.instret = backup.1;
                self.with_model(|this, model| model.after_instruction(this, op, comp));
                self.emit_interrupt_check();
                self.emit_chain_tail();
            }
        }
    }

    pub fn compile_op(&mut self, op: &Op, compressed: bool, bits: u32) {
        self.pc_end = self.pc_cur + if compressed { 2 } else { 4 };
        if cfg!(feature = "sanitize") {
            self.emit_icache_access(self.pc_end - 1, true);
            if bits != 0 {
                let mem = Register::RSI - if compressed { 1 } else { 3 };
                let mem = if compressed { mem.word() } else { mem.dword() };
                self.emit(Cmp(Mem(mem), Imm(bits as i64)));
                self.emit_helper_jcc(ConditionCode::NotEqual, helper_san_fail);
            }
        } else {
            if !same_cache_line(
                self.pc_start.wrapping_add(self.pc_cur as u64) - 1,
                self.pc_start.wrapping_add(self.pc_end as u64) - 1,
            ) {
                if self.pc_cur != 0 {
                    self.emit_icache_access(self.pc_end - 1, false);
                }
            }
        }

        self.with_model(|this, model| model.before_instruction(this, op, compressed));
        self.emit_op(op, compressed);
        self.with_model(|this, model| model.after_instruction(this, op, compressed));

        self.pc_cur = self.pc_end;
        self.instret += 1;
    }

    pub fn compile_cond_op(&mut self, bop: &Op, bcomp: bool, op: &Op, comp: bool) {
        let blen = if bcomp { 2 } else { 4 };
        let olen = if comp { 2 } else { 4 };

        self.pc_end = self.pc_cur + blen + olen;
        if !same_cache_line(
            self.pc_start.wrapping_add(self.pc_cur as u64) - 1,
            self.pc_start.wrapping_add(self.pc_end as u64) - 1,
        ) {
            self.emit_icache_access(self.pc_end - 1, false);
        }

        let (rs1, rs2, mut cc) = match *bop {
            Op::Beq { rs1, rs2, .. } => (rs1, rs2, ConditionCode::Equal),
            Op::Bne { rs1, rs2, .. } => (rs1, rs2, ConditionCode::NotEqual),
            Op::Blt { rs1, rs2, .. } => (rs1, rs2, ConditionCode::Less),
            Op::Bge { rs1, rs2, .. } => (rs1, rs2, ConditionCode::GreaterEqual),
            Op::Bltu { rs1, rs2, .. } => (rs1, rs2, ConditionCode::Below),
            Op::Bgeu { rs1, rs2, .. } => (rs1, rs2, ConditionCode::AboveEqual),
            _ => unreachable!(),
        };

        self.with_model(|this, model| {
            model.before_instruction(this, bop, bcomp);
            model.after_instruction(this, bop, bcomp);
        });
        self.before_side_effect();

        if rs2 == 0 {
            self.emit(Cmp(loc_of_register(rs1), Imm(0)));
        } else if rs1 == 0 {
            cc = cc.swap();
            self.emit(Cmp(loc_of_register(rs2), Imm(0)));
        } else {
            self.emit(Mov(Reg(Register::RDX), loc_of_register(rs1).into()));
            self.emit(Cmp(Reg(Register::RDX), loc_of_register(rs2).into()));
        }

        let jcc = self.emit_jcc_long(cc);

        self.emit(Add(memory_of!(instret).into(), Imm(1)));

        self.pc_cur += blen as i64;
        self.with_model(|this, model| model.before_instruction(this, op, comp));
        self.emit_op(op, comp);

        self.with_model(|this, model| model.after_instruction(this, op, comp));
        self.before_side_effect();

        let label_fin = self.label();
        self.patch(jcc, label_fin);

        self.pc_cur = self.pc_end;
        self.instret += 1;
    }

    pub fn begin(&mut self, pc: u64) {
        self.pc_start = pc;

        self.emit_icache_access(0, true);
        if let Ok(pc32) = i32::try_from(pc as i64) {
            self.emit(Cmp(Register::RSI.into(), Imm(pc32 as i64)));
        } else {
            self.emit(Mov(Register::RAX.into(), Imm(pc as i64)));
            self.emit(Cmp(Register::RSI.into(), Register::RAX.into()));
        }
        self.emit_helper_jcc(ConditionCode::NotEqual, helper_pred_miss);

        self.speculative_len = self.len;
        self.with_model(|this, model| model.begin_block(this, pc));
    }

    fn emit_slow_path(&mut self) {
        let split = self.len;

        for slow in std::mem::replace(&mut self.slow_path, Vec::new()) {
            match slow {
                SlowPath::DCache { ebx, write, jcc_misalign, jcc_miss, label_fin } => {
                    self.dcache_access_slow(ebx, write, jcc_misalign, jcc_miss, label_fin)
                }
                SlowPath::ICache(ebx, jcc_miss, label_fin) => {
                    self.emit_icache_slow(ebx, jcc_miss, label_fin);
                }
                SlowPath::Trap(ebx, jcc_trap) => self.emit_trap(ebx, jcc_trap),
            }
        }

        if crate::get_flags().disassemble {
            let pc_offset = self.buffer.as_ptr() as usize;
            let mut pc = 0;
            while pc < self.len {
                if pc == split {
                    eprintln!("       slow path:");
                }
                let mut pc_next = pc;
                let op = x86::decode(&mut || {
                    let ret = self.buffer[pc_next];
                    pc_next += 1;
                    ret
                });
                eprintln!(
                    "{}",
                    op.pretty_print((pc_offset + pc) as u64, &self.buffer[pc..pc_next])
                );
                pc = pc_next;
            }
        }
    }

    fn pre_adjust_instret(&mut self) {
        let instret_offset = self.instret as i64 + 1;
        if instret_offset != 0 {
            self.emit(Add(memory_of!(instret).into(), Imm(instret_offset)));
        }
        if self.minstret != 0 {
            self.emit(Add(memory_of!(minstret).into(), Imm(self.minstret as i64)));
        }
    }

    fn pre_adjust_pc_instret(&mut self, comp: bool) {
        let pc_offset = self.pc_cur + if comp { 2 } else { 4 };
        if pc_offset != 0 {
            self.emit(Add(memory_of!(pc).into(), Imm(pc_offset)));
        }
        self.pre_adjust_instret();
    }

    fn post_adjust_pc_instret(&mut self) {
        if self.pc_cur != 0 {
            self.emit(Add(memory_of!(pc).into(), Imm(self.pc_cur)));
        }
        if self.instret != 0 {
            self.emit(Add(memory_of!(instret).into(), Imm(self.instret as i64)));
        }
        if self.minstret != 0 {
            self.emit(Add(memory_of!(minstret).into(), Imm(self.minstret as i64)));
        }
    }

    pub fn end_cross(&mut self, lo_bits: u16) {
        self.pre_adjust_pc_instret(false);

        self.pc_cur = -4;
        self.instret = -1;

        self.emit_icache_access(-2, true);

        self.emit(Cmp(Mem((Register::RSI + 0).word()), Imm(0xCCCC)));
        let jcc_miss = self.emit_jcc_long(ConditionCode::NotEqual);
        let label_fin = self.label();

        let jmp_miss = self.emit_jmp_long();
        for _ in 5..PAGE_CROSS_RESERVATION {
            self.emit(Nop);
        }

        let label_miss = self.label();
        self.patch(jcc_miss, label_miss);
        self.patch(jmp_miss, label_miss);
        self.emit(Mov(Reg(Register::ECX), Imm(lo_bits as i64)));
        self.emit_helper_call(helper_icache_cross_miss);
        let jmp_fin = self.emit_jmp_long();
        self.patch(jmp_fin, label_fin);

        self.emit_slow_path();
    }

    pub fn end(&mut self) {
        self.post_adjust_pc_instret();

        self.emit_interrupt_check();

        let pc_end = self.pc_start.wrapping_add(self.pc_cur as u64);
        if same_cache_line(pc_end - 1, pc_end) {
            self.emit_helper_call(helper_patch_direct_jump);
        } else {
            self.emit_chain_tail();
        }

        self.emit_slow_path();
    }

    pub fn end_unreachable(&mut self) {
        self.emit_slow_path();
    }
}

#[no_mangle]
fn icache_cross_miss(ctx: &mut Context, pc: u64, patch: usize, insn: u32) {
    let mut op = riscv::decode(insn);
    if crate::get_flags().disassemble {
        eprintln!("{}", op.pretty_print(pc - 2, insn));
    }

    if (ctx.prv as u8) < op.min_prv_level() {
        op = Op::Illegal
    }

    let slice = unsafe { std::slice::from_raw_parts_mut(patch as *mut u8, PAGE_CROSS_RESERVATION) };
    let mut compiler = DbtCompiler::new(ctx, slice);

    compiler.pc_start = pc + 2;
    compiler.pc_cur = -4;
    compiler.pc_end = 0;
    compiler.instret = -1;
    compiler.with_model(|this, model| {
        model.begin_block(this, pc);
        model.before_instruction(this, &op, false);
    });
    compiler.emit_op(&op, false);

    let unreachable = match op {
        Op::Beq { .. }
        | Op::Bne { .. }
        | Op::Blt { .. }
        | Op::Bge { .. }
        | Op::Bltu { .. }
        | Op::Bgeu { .. } => false,
        op => op.can_change_control_flow(),
    };

    if !unreachable {
        compiler.with_model(|this, model| model.after_instruction(this, &op, false));
        compiler.emit_interrupt_check();
        compiler.emit_chain_tail();
    }
    compiler.end_unreachable();

    unsafe {
        std::ptr::write_unaligned((patch - 8) as *mut u16, (insn >> 16) as u16);
    }
}

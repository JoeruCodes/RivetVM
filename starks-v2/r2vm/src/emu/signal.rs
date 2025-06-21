use std::ptr;
use x86::{Location, Memory, Op, Operand, Register, Size};

const REG_RAX: usize = libc::REG_RAX as usize;
const REG_RDX: usize = libc::REG_RDX as usize;
const REG_RSP: usize = libc::REG_RSP as usize;
const REG_RIP: usize = libc::REG_RIP as usize;

const REG_LIST: [usize; 16] = [
    REG_RAX,
    libc::REG_RCX as usize,
    REG_RDX,
    libc::REG_RBX as usize,
    REG_RSP,
    libc::REG_RBP as usize,
    libc::REG_RSI as usize,
    libc::REG_RDI as usize,
    libc::REG_R8 as usize,
    libc::REG_R9 as usize,
    libc::REG_R10 as usize,
    libc::REG_R11 as usize,
    libc::REG_R12 as usize,
    libc::REG_R13 as usize,
    libc::REG_R14 as usize,
    libc::REG_R15 as usize,
];

struct MemReader(usize);

impl MemReader {
    fn iter_func<'a>(&'a mut self) -> impl FnMut() -> u8 + 'a {
        move || {
            let ptr = self.0;
            self.0 += 1;
            unsafe { *(ptr as *const u8) }
        }
    }
}

fn eval_memory_location(ctx: &libc::ucontext_t, mem: &Memory) -> usize {
    let mut address = mem.displacement as u64;
    if let Some(base) = mem.base {
        address = address
            .wrapping_add(ctx.uc_mcontext.gregs[REG_LIST[(base as u8 & 15) as usize]] as u64);
    }
    if let Some((index, scale)) = mem.index {
        address = address
            .wrapping_add(ctx.uc_mcontext.gregs[REG_LIST[(index as u8 & 15) as usize]] as u64)
            * scale as u64;
    }
    address as usize
}

unsafe fn read_location(ctx: &libc::ucontext_t, loc: &Location) -> u64 {
    match loc {
        &Location::Reg(reg) => {
            let value = ctx.uc_mcontext.gregs[REG_LIST[(reg as u8 & 15) as usize]] as u64;
            match reg.size() {
                Size::Qword => value,
                Size::Dword => value as u32 as u64,
                Size::Word => value as u16 as u64,
                Size::Byte => {
                    (if (reg as u8) >= Register::AH as u8 && (reg as u8) <= Register::BH as u8 {
                        (ctx.uc_mcontext.gregs[REG_LIST[(reg as u8 & 7) as usize]] >> 8) as u8
                    } else {
                        value as u8
                    }) as u64
                }
            }
        }
        Location::Mem(mem) => {
            let address = if mem.base.is_none() && mem.index.is_none() {
                mem.displacement as usize
            } else {
                eval_memory_location(ctx, mem)
            };
            match mem.size {
                Size::Qword => *(address as *const u64),
                Size::Dword => *(address as *const u32) as u64,
                Size::Word => *(address as *const u16) as u64,
                Size::Byte => *(address as *const u8) as u64,
            }
        }
    }
}

unsafe fn write_location(ctx: &mut libc::ucontext_t, loc: &Location, value: u64) {
    match loc {
        &Location::Reg(reg) => {
            let slot = &mut ctx.uc_mcontext.gregs[REG_LIST[(reg as u8 & 15) as usize]];
            match reg.size() {
                Size::Qword => *slot = value as i64,

                Size::Dword => *slot = value as u32 as i64,

                Size::Word => *slot = (*slot & !0xFFFF) | (value as i64 & 0xFFFF),
                Size::Byte => {
                    if (reg as u8) >= Register::AH as u8 && (reg as u8) <= Register::BH as u8 {
                        let slot = &mut ctx.uc_mcontext.gregs[REG_LIST[(reg as u8 & 7) as usize]];
                        *slot = (*slot & !0xFF00) | (value as i64 & 0xFF) << 8
                    } else {
                        *slot = (*slot & !0xFF) | (value as i64 & 0xFF)
                    }
                }
            }
        }
        Location::Mem(mem) => {
            let address = if mem.base.is_none() && mem.index.is_none() {
                mem.displacement as usize
            } else {
                eval_memory_location(ctx, mem)
            };
            match mem.size {
                Size::Qword => *(address as *mut u64) = value,
                Size::Dword => *(address as *mut u32) = value as u32,
                Size::Word => *(address as *mut u16) = value as u16,
                Size::Byte => *(address as *mut u8) = value as u8,
            }
        }
    }
}

unsafe extern "C" fn handle_fpe(
    _: libc::c_int,
    _: &mut libc::siginfo_t,
    ctx: &mut libc::ucontext_t,
) {
    let current_ip = ctx.uc_mcontext.gregs[REG_RIP];

    if (current_ip as usize) < 4096 || (current_ip as usize) >= *super::MEM_BOUNDARY {
        crate::shutdown(crate::ExitReason::Exit(0));
        libc::_exit(0);
    }

    let mut reader = MemReader(current_ip as usize);
    let op = x86::decode(&mut reader.iter_func());

    let opr = match op {
        Op::Div(opr) | Op::Idiv(opr) => opr,
        _ => unimplemented!(),
    };

    let opsize = opr.size();
    let divisor = read_location(&*ctx, &opr);

    let mut dividend = ctx.uc_mcontext.gregs[REG_RAX] as u64;
    if opsize == Size::Dword {
        dividend = dividend as u32 as u64
    }

    if divisor == 0 {
        ctx.uc_mcontext.gregs[REG_RAX] =
            if opsize == Size::Qword { -1 } else { -1i32 as u32 as i64 };
        ctx.uc_mcontext.gregs[REG_RDX] = dividend as i64;
    } else {
        ctx.uc_mcontext.gregs[REG_RAX] = dividend as i64;
        ctx.uc_mcontext.gregs[REG_RDX] = 0;
    }

    ctx.uc_mcontext.gregs[REG_RIP] = reader.0 as i64;
}

unsafe extern "C" fn handle_segv(
    _: libc::c_int,
    info: &mut libc::siginfo_t,
    ctx: &mut libc::ucontext_t,
) {
    let current_ip = ctx.uc_mcontext.gregs[REG_RIP];
    let fault_addr = info.si_addr() as usize;
    if fault_addr < 4096 {
        crate::shutdown(crate::ExitReason::Exit(0));
        libc::_exit(0);
    }

    if (current_ip as usize) < 4096 || (current_ip as usize) >= *super::MEM_BOUNDARY {
        crate::shutdown(crate::ExitReason::Exit(0));
        libc::_exit(0);
    }

    let mut reader = MemReader(current_ip as usize);
    let op = x86::decode(&mut reader.iter_func());

    match op {
        Op::Mov(Location::Reg(reg), Operand::Mem(mem)) | Op::Movzx(reg, Location::Mem(mem)) => {
            let address = if mem.base.is_none() && mem.index.is_none() {
                mem.displacement as usize
            } else {
                eval_memory_location(ctx, &mem)
            };
            if address < 4096 {
                write_location(ctx, &Location::Reg(reg), 0);
            } else {
                let data = crate::emu::io_read(address, mem.size.bytes() as u32);
                write_location(ctx, &Location::Reg(reg), data);
            }
        }
        Op::Mov(Location::Mem(mem), Operand::Reg(reg)) => {
            let address = if mem.base.is_none() && mem.index.is_none() {
                mem.displacement as usize
            } else {
                eval_memory_location(ctx, &mem)
            };
            if address < 4096 {
            } else {
                let data = read_location(ctx, &Location::Reg(reg));
                crate::emu::io_write(address, data, mem.size.bytes() as u32);
            }
        }
        Op::Movsx(reg, Location::Mem(mem)) => {
            let address = if mem.base.is_none() && mem.index.is_none() {
                mem.displacement as usize
            } else {
                eval_memory_location(ctx, &mem)
            };
            let raw = if address < 4096 {
                0
            } else {
                crate::emu::io_read(address, mem.size.bytes() as u32)
            };
            let data = match mem.size {
                Size::Qword => unreachable!(),
                Size::Dword => raw as i32 as u64,
                Size::Word => raw as i16 as u64,
                Size::Byte => raw as i8 as u64,
            };
            write_location(ctx, &Location::Reg(reg), data)
        }

        Op::Add(Location::Mem(mem), src) => {
            let address = if mem.base.is_none() && mem.index.is_none() {
                mem.displacement as usize
            } else {
                eval_memory_location(ctx, &mem)
            };

            if address < 4096 {
                crate::shutdown(crate::ExitReason::Exit(0));
                libc::_exit(0);
            } else if address >= *super::MEM_BOUNDARY {
                let lhs = ptr::read(address as *const u8) as u64;
                let rhs = match src {
                    Operand::Reg(r) => read_location(ctx, &Location::Reg(r)),
                    Operand::Mem(mem_src) => {
                        let addr_src = if mem_src.base.is_none() && mem_src.index.is_none() {
                            mem_src.displacement as usize
                        } else {
                            eval_memory_location(ctx, &mem_src)
                        };
                        ptr::read(addr_src as *const u8) as u64
                    }
                    Operand::Imm(imm) => imm as u64,
                } & mask_from_size(mem.size);
                let mask = mask_from_size(mem.size);
                let result = (lhs + rhs) & mask;

                update_flags_add(mem.size, lhs, rhs, result);
            } else if address >= 4096 && (*super::IO_BOUNDARY == 0 || address < *super::IO_BOUNDARY)
            {
                let lhs = if *super::IO_BOUNDARY != 0 && address < *super::IO_BOUNDARY {
                    crate::emu::io_read(address, mem.size.bytes() as u32)
                } else {
                    unsafe {
                        match mem.size {
                            Size::Byte => *(address as *const u8) as u64,
                            Size::Word => *(address as *const u16) as u64,
                            Size::Dword => *(address as *const u32) as u64,
                            Size::Qword => *(address as *const u64),
                        }
                    }
                };

                let rhs = match src {
                    Operand::Reg(r) => read_location(ctx, &Location::Reg(r)),
                    Operand::Mem(mem_src) => {
                        let addr_src = if mem_src.base.is_none() && mem_src.index.is_none() {
                            mem_src.displacement as usize
                        } else {
                            eval_memory_location(ctx, &mem_src)
                        };
                        crate::emu::io_read(addr_src, mem_src.size.bytes() as u32)
                    }
                    Operand::Imm(imm) => imm as u64,
                } & mask_from_size(mem.size);

                let mask = mask_from_size(mem.size);
                let result = (lhs + rhs) & mask;

                if *super::IO_BOUNDARY != 0 && address < *super::IO_BOUNDARY {
                    crate::emu::io_write(address, result, mem.size.bytes() as u32);
                } else {
                    unsafe {
                        match mem.size {
                            Size::Byte => *(address as *mut u8) = result as u8,
                            Size::Word => *(address as *mut u16) = result as u16,
                            Size::Dword => *(address as *mut u32) = result as u32,
                            Size::Qword => *(address as *mut u64) = result,
                        }
                    }
                }

                update_flags_add(mem.size, lhs, rhs, result);
            } else {
                unimplemented!("{:x} {:?}", current_ip, op);
            }
        }
        Op::Add(Location::Reg(reg), Operand::Mem(mem)) => {
            let address = if mem.base.is_none() && mem.index.is_none() {
                mem.displacement as usize
            } else {
                eval_memory_location(ctx, &mem)
            };
            if address < 4096 {
                crate::shutdown(crate::ExitReason::Exit(0));
                libc::_exit(0);
            } else if address >= *super::MEM_BOUNDARY {
                let rhs = ptr::read(address as *const u8) as u64;
                let lhs = read_location(ctx, &Location::Reg(reg));
                let mask = mask_from_size(mem.size);
                let result = (lhs + rhs) & mask;
                write_location(ctx, &Location::Reg(reg), result);
                update_flags_add(mem.size, lhs, rhs, result);
            } else if address >= 4096 && (*super::IO_BOUNDARY == 0 || address < *super::IO_BOUNDARY)
            {
                let rhs = if *super::IO_BOUNDARY != 0 && address < *super::IO_BOUNDARY {
                    crate::emu::io_read(address, mem.size.bytes() as u32)
                } else {
                    unsafe {
                        match mem.size {
                            Size::Byte => *(address as *const u8) as u64,
                            Size::Word => *(address as *const u16) as u64,
                            Size::Dword => *(address as *const u32) as u64,
                            Size::Qword => *(address as *const u64),
                        }
                    }
                };
                let lhs = read_location(ctx, &Location::Reg(reg));

                let mask = mask_from_size(mem.size);
                let result = (lhs + rhs) & mask;

                write_location(ctx, &Location::Reg(reg), result);

                if matches!(reg, Register::AL | Register::AX | Register::EAX | Register::RAX) {
                    core::arch::asm!("mov rax, {0}", in(reg) result, options(nostack, nomem));
                }

                update_flags_add(mem.size, lhs, rhs, result);
            } else {
                unimplemented!("{:x} {:?}", current_ip, op);
            }
        }

        _ => {
            eprintln!("[r2vm] unhandled op at pc={:#x} -> {:?}", current_ip, op);
            crate::shutdown(crate::ExitReason::Exit(0));
            libc::_exit(0);
        }
    };

    ctx.uc_mcontext.gregs[REG_RIP] = reader.0 as i64;
}

unsafe extern "C" fn handle_int(_: libc::c_int, _: &mut libc::siginfo_t, _: &mut libc::ucontext_t) {
    crate::shutdown(crate::ExitReason::Exit(2));
}

pub fn init() {
    unsafe {
        install_final_exit_handler();

        let mut act: libc::sigaction = std::mem::zeroed();
        act.sa_sigaction = handle_fpe as usize;
        act.sa_flags = libc::SA_SIGINFO;
        libc::sigaction(libc::SIGFPE, &act, std::ptr::null_mut());

        act.sa_sigaction = handle_segv as usize;
        libc::sigaction(libc::SIGSEGV, &act, std::ptr::null_mut());
        libc::sigaction(libc::SIGBUS, &act, std::ptr::null_mut());

        act.sa_sigaction = handle_int as usize;
        libc::sigaction(libc::SIGINT, &act, std::ptr::null_mut());
    }
}

pub fn install_final_exit_handler() {
    unsafe {
        extern "C" fn final_exit(_: libc::c_int) {
            unsafe {
                libc::_exit(0);
            }
        }

        let mut act: libc::sigaction = std::mem::zeroed();
        act.sa_sigaction = final_exit as usize;
        act.sa_flags = 0;
        libc::sigaction(libc::SIGSEGV, &act, std::ptr::null_mut());
        libc::sigaction(libc::SIGBUS, &act, std::ptr::null_mut());
    }
}

fn mask_from_size(size: Size) -> u64 {
    match size {
        Size::Byte => 0xFF,
        Size::Word => 0xFFFF,
        Size::Dword => 0xFFFF_FFFF,
        Size::Qword => 0xFFFF_FFFF_FFFF_FFFF,
    }
}

unsafe fn update_flags_add(size: Size, lhs: u64, rhs: u64, result: u64) {
    const CF_BIT: u64 = 1 << 0;
    const PF_BIT: u64 = 1 << 2;
    const AF_BIT: u64 = 1 << 4;
    const ZF_BIT: u64 = 1 << 6;
    const SF_BIT: u64 = 1 << 7;
    const OF_BIT: u64 = 1 << 11;

    let bits = match size {
        Size::Byte => 8,
        Size::Word => 16,
        Size::Dword => 32,
        Size::Qword => 64,
    };

    let full_sum = (lhs as u128) + (rhs as u128);
    let carry = if full_sum >> bits != 0 { CF_BIT } else { 0 };

    let af = if ((lhs ^ rhs ^ result) & 0x10) != 0 { AF_BIT } else { 0 };

    let zf = if (result & ((1u64 << bits) - 1)) == 0 { ZF_BIT } else { 0 };

    let sign_bit = 1u64 << (bits - 1);
    let sf = if (result & sign_bit) != 0 { SF_BIT } else { 0 };

    let of = if (((lhs ^ result) & (rhs ^ result)) & sign_bit) != 0 { OF_BIT } else { 0 };

    let mut byte = (result & 0xFF) as u8;
    byte ^= byte >> 4;
    byte ^= byte >> 2;
    byte ^= byte >> 1;
    let pf = if byte & 1 == 0 { PF_BIT } else { 0 };

    let mask = CF_BIT | PF_BIT | AF_BIT | ZF_BIT | SF_BIT | OF_BIT;
    let new_bits = carry | pf | af | zf | sf | of;

    let mut rflags: u64;
    core::arch::asm!("pushfq; pop {}", out(reg) rflags, options(nomem, preserves_flags));

    rflags = (rflags & !mask) | new_bits;

    core::arch::asm!("push {0}; popfq", in(reg) rflags, options(nostack));
}

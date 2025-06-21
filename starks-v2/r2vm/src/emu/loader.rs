use super::abi;
use super::interp::Context;
use rand::RngCore;
use std::ffi::{CStr, OsString};
use std::fs::File;
use std::io::Write;
use std::os::unix::ffi::OsStrExt;
use std::os::unix::io::{AsRawFd, FromRawFd, IntoRawFd};
use std::path::Path;

use ro_cell::RoCell;

const EI_CLASS: usize = 0x4;
const PF_R: u32 = 0x4;
const PF_W: u32 = 0x2;
const PF_X: u32 = 0x1;
const ET_EXEC: libc::Elf64_Half = 2;
const ET_DYN: libc::Elf64_Half = 3;
const EM_RISCV: libc::Elf64_Half = 243;

#[repr(C)]
pub struct Loader {
    fd: libc::c_int,
    file_size: libc::c_ulong,
    memory: *mut libc::c_void,
}

impl Drop for Loader {
    fn drop(&mut self) {
        unsafe { libc::munmap(self.memory, self.file_size as usize) };
        unsafe { File::from_raw_fd(self.fd) };
    }
}

struct PhdrIter<'a> {
    i: usize,
    ehdr: &'a libc::Elf64_Ehdr,
}

impl<'a> Iterator for PhdrIter<'a> {
    type Item = &'a libc::Elf64_Phdr;
    fn next(&mut self) -> Option<Self::Item> {
        if self.i == self.ehdr.e_phnum as usize {
            None
        } else {
            let ptr = self.ehdr as *const _ as usize
                + self.ehdr.e_phoff as usize
                + self.ehdr.e_phentsize as usize * self.i;
            self.i += 1;
            Some(unsafe { &*(ptr as *const libc::Elf64_Phdr) })
        }
    }
}

impl Loader {
    pub fn as_slice(&self) -> &[u8] {
        unsafe { std::slice::from_raw_parts(self.memory as *const u8, self.file_size as _) }
    }

    fn ehdr(&self) -> &libc::Elf64_Ehdr {
        unsafe { &*(self.memory as *const libc::Elf64_Ehdr) }
    }

    fn phdr(&self) -> PhdrIter {
        PhdrIter { i: 0, ehdr: self.ehdr() }
    }

    pub fn new(file: &Path) -> std::io::Result<Loader> {
        println!("Loading file: {}", file.display());
        let file = File::open(super::syscall::translate_path(file))?;

        let file_size = file.metadata()?.len();

        println!("Mapping file to memory");
        let memory = unsafe {
            libc::mmap(
                std::ptr::null_mut(),
                file_size as usize,
                libc::PROT_READ,
                libc::MAP_PRIVATE,
                file.as_raw_fd(),
                0,
            )
        };
        println!("Mapped file to memory");
        if memory == libc::MAP_FAILED {
            println!("Failed to map file to memory");
            return Err(std::io::Error::last_os_error());
        }
        println!("Mapped file to memory");
        Ok(Loader { fd: file.into_raw_fd(), file_size, memory })
    }

    pub fn is_elf(&self) -> bool {
        let header = self.ehdr();

        if &header.e_ident[0..4] != b"\x7FELF" {
            return false;
        }

        true
    }

    pub fn validate_elf(&self) -> Result<(), &'static str> {
        let header = self.ehdr();

        if header.e_type != ET_EXEC && header.e_type != ET_DYN {
            return Err("the binary is not executable.");
        }

        if header.e_machine != EM_RISCV {
            return Err("the binary is not for RISC-V.");
        }

        if header.e_ident[EI_CLASS] != 2 {
            return Err("the binary is not ELF64.");
        }

        if (header.e_entry as i64) < 0 {
            return Err("config must be used for full-system emulation");
        }

        Ok(())
    }

    fn find_interpreter(&self) -> Option<&str> {
        let header = unsafe { &*(self.memory as *const libc::Elf64_Ehdr) };

        for i in 0..(header.e_phnum as usize) {
            let h = unsafe {
                &*((self.memory as usize
                    + header.e_phoff as usize
                    + header.e_phentsize as usize * i)
                    as *const libc::Elf64_Phdr)
            };

            if h.p_type == libc::PT_INTERP {
                let content = unsafe {
                    std::slice::from_raw_parts(
                        (self.memory as usize + h.p_offset as usize) as *const u8,
                        h.p_filesz as usize,
                    )
                };
                return Some(CStr::from_bytes_with_nul(content).unwrap().to_str().unwrap());
            }
        }
        None
    }

    fn find_symbol(&self, name: &str) -> Option<u64> {
        unsafe {
            let ehdr = self.ehdr();

            let shdr_base = self.memory as usize + ehdr.e_shoff as usize;
            for i in 0..ehdr.e_shnum {
                let shdr = &*((shdr_base + i as usize * ehdr.e_shentsize as usize)
                    as *const libc::Elf64_Shdr);

                const SHT_SYMTAB: u32 = 2;
                const SHT_DYNSYM: u32 = 11;
                if shdr.sh_type != SHT_SYMTAB && shdr.sh_type != SHT_DYNSYM {
                    continue;
                }

                let strtab_shdr = &*((shdr_base + shdr.sh_link as usize * ehdr.e_shentsize as usize)
                    as *const libc::Elf64_Shdr);
                let strtab = (self.memory as usize + strtab_shdr.sh_offset as usize) as *const u8;

                let num_syms = shdr.sh_size as usize / std::mem::size_of::<libc::Elf64_Sym>();
                let symtab_ptr =
                    (self.memory as usize + shdr.sh_offset as usize) as *const libc::Elf64_Sym;
                for idx in 0..num_syms {
                    let sym = &*symtab_ptr.add(idx);
                    if sym.st_name == 0 {
                        continue;
                    }
                    let c_name = CStr::from_ptr(strtab.add(sym.st_name as usize) as *const i8);
                    if let Ok(n) = c_name.to_str() {
                        if n == name {
                            return Some(sym.st_value);
                        }
                    }
                }
            }
        }
        None
    }

    unsafe fn load_image(&self, load_addr: &mut u64, brk: &mut u64) -> u64 {
        let ehdr = self.ehdr();

        let mut loaddr = u64::max_value();
        let mut hiaddr = 0;
        for h in self.phdr() {
            if h.p_type == libc::PT_LOAD {
                loaddr = std::cmp::min(loaddr, h.p_vaddr);
                hiaddr = std::cmp::max(hiaddr, h.p_vaddr + h.p_memsz);
            }
        }

        loaddr &= !4095;
        hiaddr = (hiaddr + 4095) & !4095;

        let bias = {
            let map = libc::mmap(
                std::ptr::null_mut(),
                (hiaddr - loaddr) as _,
                libc::PROT_NONE,
                libc::MAP_PRIVATE | libc::MAP_ANON | libc::MAP_32BIT,
                -1,
                0,
            );
            if map == libc::MAP_FAILED {
                panic!("mmap failed while loading");
            }
            map as usize as u64 - loaddr
        };

        for h in self.phdr() {
            if h.p_type == libc::PT_LOAD {
                if h.p_filesz > h.p_memsz {
                    panic!("invalid elf file: constraint p_filesz <= p_memsz is not satisified");
                }

                let vaddr_map_end = h.p_vaddr + h.p_filesz;
                let vaddr_end = h.p_vaddr + h.p_memsz;
                let mut file_offset = h.p_offset;
                let page_start = h.p_vaddr & !4095;
                let map_end = vaddr_map_end & !4095;
                let page_end = (vaddr_end + 4095) & !4095;

                let mut prot = 0;
                if (h.p_flags & PF_R) != 0 {
                    prot |= libc::PROT_READ
                };
                if (h.p_flags & PF_W) != 0 {
                    prot |= libc::PROT_WRITE
                };
                if (h.p_flags & PF_X) != 0 {
                    prot |= libc::PROT_READ
                };

                if h.p_vaddr != page_start {
                    file_offset -= h.p_vaddr - page_start;
                }

                if map_end != page_start {
                    let map = libc::mmap(
                        (bias + page_start) as usize as _,
                        (map_end - page_start) as _,
                        prot,
                        libc::MAP_PRIVATE | libc::MAP_FIXED,
                        self.fd,
                        file_offset as _,
                    );
                    if map == libc::MAP_FAILED {
                        panic!("mmap failed while loading");
                    }
                }

                if map_end != page_end {
                    let rem_ptr = (bias + map_end) as usize as _;

                    libc::mprotect(
                        rem_ptr,
                        (page_end - map_end) as usize,
                        libc::PROT_READ | libc::PROT_WRITE,
                    );

                    libc::memcpy(
                        rem_ptr,
                        (self.memory as usize
                            + file_offset as usize
                            + (map_end - page_start) as usize) as _,
                        (vaddr_map_end - map_end) as usize,
                    );

                    if (h.p_flags & PF_W) == 0 {
                        libc::mprotect(rem_ptr, (page_end - map_end) as usize, prot);
                    }
                }

                if vaddr_end > *brk {
                    *brk = vaddr_end;
                }
            }
        }

        *load_addr = bias + loaddr;
        *brk = bias + ((*brk + 4095) & !4095);
        bias + ehdr.e_entry
    }

    pub unsafe fn load_kernel(&self, load_addr: u64) -> u64 {
        let mut loaddr = u64::max_value();
        let mut hiaddr = 0;
        for h in self.phdr() {
            if h.p_type == libc::PT_LOAD {
                loaddr = std::cmp::min(loaddr, h.p_vaddr);
                hiaddr = std::cmp::max(hiaddr, h.p_vaddr + h.p_memsz);
            }
        }

        loaddr &= !4095;
        hiaddr = (hiaddr + 4095) & !4095;

        for h in self.phdr() {
            if h.p_type == libc::PT_LOAD {
                if h.p_filesz > h.p_memsz {
                    panic!("invalid elf file: constraint p_filesz <= p_memsz is not satisified");
                }

                libc::memcpy(
                    (h.p_vaddr - loaddr + load_addr) as usize as _,
                    (self.memory as usize + h.p_offset as usize) as _,
                    h.p_filesz as usize,
                );

                libc::memset(
                    (h.p_vaddr + h.p_filesz - loaddr + load_addr) as usize as _,
                    0,
                    (h.p_memsz - h.p_filesz) as usize,
                );
            }
        }

        hiaddr - loaddr
    }

    unsafe fn load_elf(&self, sp: &mut u64) -> u64 {
        let mut load_addr = 0;
        let mut brk = 0;
        let entry = self.load_image(&mut load_addr, &mut brk);
        let mut actual_entry = entry;
        let mut interp_addr = 0;

        if let Some(interp) = self.find_interpreter() {
            let interp_file = Loader::new(interp.as_ref()).unwrap();
            interp_file.validate_elf().unwrap();

            if interp_file.find_interpreter().is_some() {
                panic!("interpreter cannot require other interpreters");
            }

            let mut interp_brk = 0;
            actual_entry = interp_file.load_image(&mut interp_addr, &mut interp_brk);

            if crate::get_flags().prv == 0 {
                if let Some(sym_val) = self.find_symbol("__libc_start_main") {
                    let libc_start_runtime = sym_val + (load_addr - (sym_val & !0xfff));
                    let return_pc = libc_start_runtime + 0x14;
                    RoCell::replace(&super::LIBC_RETURN_PC, return_pc);
                }
            }
        }

        brk = (brk + 4095) & !4095;
        super::syscall::init_brk(brk);

        let mut push = |value: u64| {
            *sp -= std::mem::size_of::<u64>() as u64;
            *(*sp as usize as *mut u64) = value;
        };

        let header = &*(self.memory as *const libc::Elf64_Ehdr);
        push(load_addr + header.e_phoff);
        push(abi::AT_PHDR);
        push(header.e_phentsize as _);
        push(abi::AT_PHENT);
        push(header.e_phnum as _);
        push(abi::AT_PHNUM);
        push(4096);
        push(abi::AT_PAGESZ);
        push(interp_addr);
        push(abi::AT_BASE);
        push(0);
        push(abi::AT_FLAGS);
        push(entry);
        push(abi::AT_ENTRY);

        actual_entry
    }

    pub unsafe fn load_bin(&self, location: u64) {
        libc::memcpy(location as usize as _, self.memory, self.file_size as _);
    }
}

pub unsafe fn load(
    file: &Loader,
    args: &mut dyn Iterator<Item = OsString>,
    ctxs: &mut [&mut Context],
) {
    if crate::get_flags().prv == 0 {
        let mut sp: u64 = 0x7fff0000;
        let map = libc::mmap(
            (sp - 0x800000) as usize as _,
            0x800000,
            libc::PROT_READ | libc::PROT_WRITE,
            libc::MAP_PRIVATE | libc::MAP_ANON | libc::MAP_FIXED,
            -1,
            0,
        );
        if map == libc::MAP_FAILED {
            panic!("mmap failed while loading");
        }

        let sp_alloc = |sp: &mut u64, size: usize| {
            *sp -= size as u64;
            std::slice::from_raw_parts_mut(*sp as usize as _, size)
        };

        let mut env_pointers = Vec::new();
        let mut arg_pointers = Vec::new();

        for (var_k, var_v) in std::env::vars() {
            sp_alloc(&mut sp, 1)[0] = 0;
            sp_alloc(&mut sp, var_v.len()).copy_from_slice(var_v.as_bytes());
            sp_alloc(&mut sp, 1)[0] = b'=';
            sp_alloc(&mut sp, var_k.len()).copy_from_slice(var_k.as_bytes());
            env_pointers.push(sp);
        }

        for arg in args {
            sp_alloc(&mut sp, 1)[0] = 0;
            sp_alloc(&mut sp, arg.len()).copy_from_slice(arg.as_bytes());
            arg_pointers.push(sp);
        }

        sp &= !7;

        let push = |sp: &mut u64, value: u64| {
            *sp -= std::mem::size_of::<u64>() as u64;
            *(*sp as usize as *mut u64) = value;
        };

        let mut rng = rand::rngs::OsRng;
        push(&mut sp, rng.next_u64());
        push(&mut sp, rng.next_u64());
        push(&mut sp, rng.next_u64());
        push(&mut sp, rng.next_u64());
        let random_data = sp;

        push(&mut sp, 0);
        push(&mut sp, abi::AT_NULL);

        let start = file.load_elf(&mut sp);

        push(&mut sp, libc::getuid() as _);
        push(&mut sp, abi::AT_UID);
        push(&mut sp, libc::geteuid() as _);
        push(&mut sp, abi::AT_EUID);
        push(&mut sp, libc::getgid() as _);
        push(&mut sp, abi::AT_GID);
        push(&mut sp, libc::getegid() as _);
        push(&mut sp, abi::AT_EGID);
        push(&mut sp, 0);
        push(&mut sp, abi::AT_HWCAP);
        push(&mut sp, 100);
        push(&mut sp, abi::AT_CLKTCK);
        push(&mut sp, random_data);
        push(&mut sp, abi::AT_RANDOM);

        push(&mut sp, 0);
        for v in env_pointers.into_iter().rev() {
            push(&mut sp, v)
        }

        push(&mut sp, 0);
        for &v in arg_pointers.iter().rev() {
            push(&mut sp, v)
        }

        push(&mut sp, arg_pointers.len() as _);

        let ctx = &mut ctxs[0];
        ctx.pc = start;

        ctx.registers[2] = sp;

        ctx.registers[10] = 0;
        ctx.prv = 0;
    } else {
        let size = if file.is_elf() {
            file.load_kernel(0x40000000)
        } else {
            file.load_bin(0x40000000);
            file.file_size
        };

        let device_tree = fdt::encode(&crate::emu::device_tree());

        if let Some(ref path) = crate::get_flags().dump_fdt {
            let mut file = File::create(path).unwrap();
            file.write_all(&device_tree).unwrap();
        }

        let target =
            std::slice::from_raw_parts_mut((0x40000000 + size) as *mut u8, device_tree.len());
        target.copy_from_slice(&device_tree[..]);

        for ctx in ctxs {
            ctx.registers[10] = ctx.hartid;

            ctx.registers[11] = 0x40000000 + size;
            ctx.pc = 0x40000000;
            ctx.prv = 1;
        }
    }
}

pub const PTE_V: u64 = 0x01;
pub const PTE_R: u64 = 0x02;
pub const PTE_W: u64 = 0x04;
pub const PTE_X: u64 = 0x08;
pub const PTE_U: u64 = 0x10;
pub const PTE_G: u64 = 0x20;
pub const PTE_A: u64 = 0x40;
pub const PTE_D: u64 = 0x80;

#[derive(PartialEq, Eq, Clone, Copy, Debug)]
pub enum AccessType {
    Read,
    Write,
    Execute,
}

#[derive(Clone, Copy)]
pub struct PageWalkResult {
    pub pte: u64,

    pub granularity: u8,
}

impl PageWalkResult {
    #[inline]
    pub fn invalid() -> Self {
        PageWalkResult { pte: 0, granularity: 0 }
    }

    #[inline]
    pub fn from_4k_pte(pte: u64) -> Self {
        PageWalkResult { pte, granularity: 0 }
    }

    #[inline]
    pub fn synthesise_4k(&self, vaddr: u64) -> Self {
        let page_index_within_superpage = (vaddr >> 12) & ((1 << (self.granularity * 9)) - 1);
        let pte = self.pte | page_index_within_superpage << 10;
        Self { pte, granularity: 0 }
    }
}

pub fn walk_page(satp: u64, vpn: u64, mut read_mem: impl FnMut(u64) -> u64) -> PageWalkResult {
    if (((vpn << (64 - 27)) as i64) >> (64 - 27 - 12)) as u64 >> 12 != vpn {
        return PageWalkResult::invalid();
    }

    let mut ppn = satp & ((1u64 << 44) - 1);
    let mut global = false;

    for i in 0..3 {
        let bits_left = 18 - i * 9;
        let index = (vpn >> bits_left) & 511;
        let pte_addr = (ppn << 12) + index * 8;
        let mut pte = read_mem(pte_addr);
        ppn = pte >> 10;

        if pte & PTE_V == 0 {
            return PageWalkResult::invalid();
        }

        if pte & (PTE_R | PTE_W | PTE_X) == PTE_W {
            return PageWalkResult::invalid();
        }
        if pte & (PTE_R | PTE_W | PTE_X) == PTE_W | PTE_X {
            return PageWalkResult::invalid();
        }

        if pte & PTE_G != 0 {
            global = true
        }

        if pte & (PTE_R | PTE_W | PTE_X) == 0 {
            continue;
        }

        if ppn & ((1 << bits_left) - 1) != 0 {
            return PageWalkResult::invalid();
        }

        if global {
            pte |= PTE_G;
        }
        return PageWalkResult { pte, granularity: 2 - i };
    }

    PageWalkResult::invalid()
}

pub fn check_permission(pte: u64, access: AccessType, prv: u8, status: u64) -> Result<(), ()> {
    if pte & PTE_V == 0 {
        return Err(());
    }

    if prv == 0 {
        if pte & PTE_U == 0 {
            return Err(());
        }
    } else {
        if pte & PTE_U != 0 && status & (1 << 18) == 0 {
            return Err(());
        }
    }

    if pte & PTE_A == 0 {
        return Err(());
    }

    match access {
        AccessType::Read => {
            if pte & PTE_R == 0 && (pte & PTE_X == 0 || status & (1 << 19) == 0) {
                return Err(());
            }
        }
        AccessType::Write => {
            if pte & PTE_W == 0 || pte & PTE_D == 0 {
                return Err(());
            }
        }
        AccessType::Execute => {
            if pte & PTE_X == 0 {
                return Err(());
            }
        }
    }

    Ok(())
}

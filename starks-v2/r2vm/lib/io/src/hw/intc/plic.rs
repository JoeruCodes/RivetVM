use crate::{IoMemory, IrqPin};
use parking_lot::Mutex;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Weak};

const ADDR_PRIORITY_START: usize = 0x000;
const ADDR_PRIORITY_END: usize = 0xFFC;

const ADDR_PENDING_START: usize = 0x1000;
const ADDR_PENDING_END: usize = 0x107C;

const ADDR_ENABLE_START: usize = 0x2000;
const ADDR_ENABLE_SIZE: usize = 0x80;

const ADDR_CONTEXT_START: usize = 0x200000;
const ADDR_CONTEXT_SIZE: usize = 0x1000;
const OFFSET_PRIORITY_THRESHOLD: usize = 0x000;
const OFFSET_INTERRUPT_CLAIM: usize = 0x004;

pub struct Plic(Arc<Mutex<PlicInner>>);

struct PlicInner {
    level: u32,

    edge_trigger: u32,

    priority: [u8; 32],
    pending: u32,
    claimed: u32,
    enable: Box<[u32]>,
    threshold: Box<[u8]>,
    irq: Box<[Box<dyn IrqPin>]>,
}

pub struct PlicIrq {
    plic: Weak<Mutex<PlicInner>>,
    irq: u32,
    prev: AtomicBool,
}

impl PlicInner {
    fn new(ctx_irqs: Vec<Box<dyn IrqPin>>) -> Self {
        Self {
            level: 0,
            edge_trigger: 0,
            priority: [0; 32],
            pending: 0,
            enable: vec![0; ctx_irqs.len()].into_boxed_slice(),
            threshold: vec![0; ctx_irqs.len()].into_boxed_slice(),
            claimed: 0,
            irq: ctx_irqs.into_boxed_slice(),
        }
    }

    fn set_level(&mut self, irq: u32, level: bool) {
        assert!(irq > 0 && irq < 32);
        let mask = 1 << irq;

        if self.edge_trigger & mask != 0 && self.level & mask == 0 && level {
            self.pending |= mask;
        }

        if level {
            self.level |= mask;
        } else {
            self.level &= !mask;
        }

        self.recompute_pending();
    }

    fn pending(&self, ctx: usize) -> bool {
        let claimable = (self.pending & !self.claimed) & self.enable[ctx];
        for irq in 1..32 {
            let prio = self.priority[irq];
            let enabled = (claimable & (1 << irq)) != 0;
            if enabled && prio > self.threshold[ctx] {
                return true;
            }
        }
        false
    }

    fn recompute_pending(&mut self) {
        self.pending = (self.pending & self.edge_trigger) | (!self.edge_trigger & self.level);

        for ctx in 0..self.enable.len() {
            self.irq[ctx].set_level(self.pending(ctx));
        }
    }

    fn claim(&mut self, ctx: usize) -> u32 {
        let claimable = (self.pending & !self.claimed) & self.enable[ctx];
        let mut cur_irq = 0;

        let mut cur_prio = 0;
        for irq in 1..32 {
            let prio = self.priority[irq];
            let enabled = (claimable & (1 << irq)) != 0;
            if enabled && prio > cur_prio {
                cur_irq = irq;
                cur_prio = prio;
            }
        }
        if cur_irq != 0 {
            self.pending &= !(1 << cur_irq);
            self.claimed |= 1 << cur_irq;

            self.recompute_pending();
        }
        cur_irq as u32
    }

    fn read(&mut self, addr: usize, size: u32) -> u64 {
        if size != 4 {
            error!(target: "PLIC", "illegal register read 0x{:x}", addr);
            return 0;
        }
        (match addr {
            ADDR_PRIORITY_START..=ADDR_PRIORITY_END => {
                let irq = (addr - ADDR_PRIORITY_START) / 4;

                if irq == 0 || irq >= 32 {
                    error!(target: "PLIC", "access to interrupt priority of {} is out of bound", irq);
                    return 0;
                }
                let value = self.priority[irq];
                trace!(target: "PLIC", "read interrupt priority of {} as {}", irq, value);
                value as u32
            }

            ADDR_PENDING_START..=ADDR_PENDING_END => {
                let irq = (addr - ADDR_PENDING_START) * 8;

                if irq >= 32 {
                    error!(target: "PLIC", "access to pending of {}-{} is out of bound", irq, irq + 31);
                    return 0;
                }
                let value = self.pending;
                trace!(target: "PLIC", "read pending of {}-{} as {}", irq, irq + 31, value);
                value
            }

            ADDR_ENABLE_START..=0x1FFFFF => {
                let ctx = (addr - ADDR_ENABLE_START) / ADDR_ENABLE_SIZE;
                let irq = (addr & (ADDR_ENABLE_SIZE - 1)) * 8;

                if ctx >= self.enable.len() || irq >= 32 {
                    error!(target: "PLIC", "{} access to interrupt enable of {}-{} is out of bound", ctx, irq, irq + 31);
                    return 0;
                }
                let value = self.enable[ctx];
                trace!(target: "PLIC", "{} read interrupt enable of {}-{} as {:b}", ctx, irq, irq + 31, value);
                value
            }

            addr if addr >= ADDR_CONTEXT_SIZE => {
                let ctx = (addr - ADDR_CONTEXT_START) / ADDR_CONTEXT_SIZE;
                let offset = addr & (ADDR_CONTEXT_SIZE - 1);

                if ctx >= self.enable.len() {
                    error!(target: "PLIC", "access to context id {} is out of bound", ctx);
                    return 0;
                }
                match offset {
                    OFFSET_PRIORITY_THRESHOLD => {
                        let value = self.threshold[ctx];
                        trace!(target: "PLIC", "{} read priority threshold as {}", ctx, value);
                        value as u32
                    }
                    OFFSET_INTERRUPT_CLAIM => {
                        let value = self.claim(ctx);
                        trace!(target: "PLIC", "{} claimed interrupt {}", ctx, value);
                        value
                    }

                    _ => {
                        error!(target: "PLIC", "illegal register read 0x{:x}", addr);
                        return 0;
                    }
                }
            }
            _ => {
                error!(target: "PLIC", "illegal register read 0x{:x}", addr);
                return 0;
            }
        }) as u64
    }

    fn write(&mut self, addr: usize, value: u64, size: u32) {
        if size != 4 {
            error!(target: "PLIC", "illegal register write 0x{:x} = 0x{:x}", addr, value);
            return;
        }
        let value = value as u32;

        match addr {
            ADDR_PRIORITY_START..=ADDR_PRIORITY_END => {
                let irq = (addr - ADDR_PRIORITY_START) / 4;

                if irq == 0 || irq >= 32 {
                    error!(target: "PLIC", "access to interrupt priority of {} is out of bound", irq);
                    return;
                }
                self.priority[irq] = (value & 7) as u8;
                trace!(target: "PLIC", "set interrupt priority of {} to {}", irq, value & 7);
            }

            ADDR_PENDING_START..=ADDR_PENDING_END => {
                error!(target: "PLIC", "illegal write to interrupt pending 0x{:x} = 0x{:x}", addr, value);
                return;
            }

            ADDR_ENABLE_START..=0x1FFFFF => {
                let ctx = (addr - ADDR_ENABLE_START) / ADDR_ENABLE_SIZE;
                let irq = (addr & (ADDR_ENABLE_SIZE - 1)) * 8;

                if ctx >= self.enable.len() || irq >= 32 {
                    error!(target: "PLIC", "{} access to interrupt enable of {}-{} is out of bound", ctx, irq, irq + 31);
                    return;
                }
                self.enable[ctx] = value;
                trace!(target: "PLIC", "{} set interrupt enable of {}-{} to {:b}", ctx, irq, irq + 31, value);
            }

            addr if addr >= ADDR_CONTEXT_START => {
                let ctx = (addr - ADDR_CONTEXT_START) / ADDR_CONTEXT_SIZE;
                let offset = addr & (ADDR_CONTEXT_SIZE - 1);

                if ctx >= self.enable.len() {
                    error!(target: "PLIC", "access to context id {} is out of bound", ctx);
                    return;
                }
                match offset {
                    OFFSET_PRIORITY_THRESHOLD => {
                        self.threshold[ctx] = (value & 7) as u8;
                        trace!(target: "PLIC", "{} set priority threshold to {}", ctx, self.threshold[ctx]);
                    }
                    OFFSET_INTERRUPT_CLAIM => {
                        self.claimed &= !(1 << value);
                        trace!(target: "PLIC", "{} completed interrupt {}", ctx, value);
                    }

                    _ => {
                        error!(target: "PLIC", "illegal register write 0x{:x} = 0x{}", addr, value);
                        return;
                    }
                }
            }
            _ => {
                error!(target: "PLIC", "illegal register write 0x{:x} = 0x{:x}", addr, value);
                return;
            }
        }

        self.recompute_pending();
    }
}

impl Plic {
    pub fn new(ctx_irqs: Vec<Box<dyn IrqPin>>) -> Self {
        Self(Arc::new(Mutex::new(PlicInner::new(ctx_irqs))))
    }

    pub fn irq_pin(&self, irq: u32, edge_trigger: bool) -> Box<dyn IrqPin> {
        assert!(irq > 0 && irq < 32);
        let mut guard = self.0.lock();
        if edge_trigger {
            guard.edge_trigger |= 1 << irq;
        } else {
            guard.edge_trigger &= !(1 << irq);
        }
        Box::new(PlicIrq { plic: Arc::downgrade(&self.0), irq, prev: AtomicBool::new(false) })
    }
}

impl IoMemory for Plic {
    fn read(&self, addr: usize, size: u32) -> u64 {
        self.0.lock().read(addr, size)
    }

    fn write(&self, addr: usize, value: u64, size: u32) {
        self.0.lock().write(addr, value, size)
    }
}

impl IrqPin for PlicIrq {
    fn set_level(&self, level: bool) {
        if self.prev.swap(level, Ordering::Relaxed) == level {
            return;
        }

        if let Some(inner) = self.plic.upgrade() {
            inner.lock().set_level(self.irq, level);
        }
    }
}

use futures::future::BoxFuture;
use futures::future::poll_fn;
use io::hw::intc::Clint;
use io::system::IoSystem;
use io::{IoMemory, IrqPin};
use once_cell::sync::Lazy;
use ro_cell::RoCell;
use std::sync::Arc;
use std::task::Poll;
use std::time::Duration;

pub mod interp;
#[rustfmt::skip]
mod abi;
pub mod dbt;
mod event;
pub mod loader;
pub mod signal;
pub mod syscall;
pub use event::EventLoop;
pub use syscall::syscall;

struct DirectIoContext;

impl io::DmaContext for DirectIoContext {
    fn dma_read<'asyn>(&'asyn self, addr: u64, buf: &'asyn mut [u8]) -> BoxFuture<'asyn, ()> {
        unsafe {
            std::ptr::copy_nonoverlapping(addr as usize as *const u8, buf.as_mut_ptr(), buf.len())
        };
        Box::pin(poll_fn(|_| Poll::Ready(())))
    }

    fn dma_write<'asyn>(&'asyn self, addr: u64, buf: &'asyn [u8]) -> BoxFuture<'asyn, ()> {
        let addr = addr as usize;
        unsafe { std::ptr::copy_nonoverlapping(buf.as_ptr(), addr as *mut u8, buf.len()) };
        crate::emu::interp::icache_invalidate(addr, addr + buf.len());
        Box::pin(poll_fn(|_| Poll::Ready(())))
    }

    fn read_u16<'asyn>(&'asyn self, addr: u64) -> BoxFuture<'asyn, u16> {
        let ret = unsafe {
            (*(addr as *const std::sync::atomic::AtomicU16))
                .load(std::sync::atomic::Ordering::SeqCst)
        };
        Box::pin(futures::future::ready(ret))
    }

    fn write_u16<'asyn>(&'asyn self, addr: u64, value: u16) -> BoxFuture<'asyn, ()> {
        unsafe {
            (*(addr as *const std::sync::atomic::AtomicU16))
                .store(value, std::sync::atomic::Ordering::SeqCst)
        }
        Box::pin(poll_fn(|_| Poll::Ready(())))
    }
}

impl io::RuntimeContext for DirectIoContext {
    fn now(&self) -> Duration {
        Duration::from_micros(crate::event_loop().time())
    }

    fn create_timer(&self, time: Duration) -> BoxFuture<'static, ()> {
        Box::pin(crate::event_loop().on_time(time.as_micros() as u64))
    }

    fn spawn(
        &self,
        task: std::pin::Pin<Box<dyn std::future::Future<Output = ()> + 'static + Send>>,
    ) {
        crate::event_loop().spawn(task);
    }

    fn spawn_blocking(
        &self,
        name: &str,
        task: std::pin::Pin<Box<dyn std::future::Future<Output = ()> + 'static + Send>>,
    ) {
        if crate::get_flags().blocking_io {
            crate::event_loop().spawn(task);
        } else {
            std::thread::Builder::new()
                .name(name.to_owned())
                .spawn(move || futures::executor::block_on(task))
                .unwrap();
        }
    }
}

struct CoreIrq(usize, u64);

impl IrqPin for CoreIrq {
    fn set_level(&self, level: bool) {
        if level {
            crate::shared_context(self.0).assert(self.1);
        } else {
            crate::shared_context(self.0).deassert(self.1);
        }
    }
}

static IO_SYSTEM: Lazy<IoSystem> = Lazy::new(|| {
    assert_ne!(crate::get_flags().prv, 0);

    let mut sys = IoSystem::new(
        Arc::new(DirectIoContext),
        Some(Arc::new(DirectIoContext)),
        crate::core_count(),
        crate::CONFIG.plic.io_base,
        |i| Box::new(CoreIrq(i, 512)),
    );

    if let Some(ref config) = crate::CONFIG.clint {
        let base = config.io_base.unwrap_or_else(|| sys.allocate_mem(0x10000));
        sys.register_mem(base, 0x10000, Arc::new(&*CLINT));
    }

    for config in crate::CONFIG.drive.iter() {
        sys.instantiate_drive(config);
    }

    for config in crate::CONFIG.random.iter() {
        sys.instantiate_random(config);
    }

    for config in crate::CONFIG.share.iter() {
        sys.instantiate_share(config);
    }

    #[cfg(feature = "usernet")]
    for config in crate::CONFIG.network.iter() {
        sys.instantiate_network(config);
    }

    if let Some(ref config) = crate::CONFIG.console {
        sys.instantiate_console(config, Box::new(&*CONSOLE));
    }

    if let Some(ref config) = crate::CONFIG.rtc {
        sys.instantiate_rtc(config);
    }

    sys
});

pub static CLINT: Lazy<Clint> = Lazy::new(|| {
    let core_count = crate::core_count();
    Clint::new(
        Arc::new(DirectIoContext),
        (0..core_count)
            .map(|i| -> Box<dyn IrqPin> {
                Box::new(CoreIrq(i, if crate::get_flags().prv == 1 { 2 } else { 8 }))
            })
            .collect(),
        (0..core_count)
            .map(|i| -> Box<dyn IrqPin> {
                Box::new(CoreIrq(i, if crate::get_flags().prv == 1 { 32 } else { 128 }))
            })
            .collect(),
    )
});

pub static CONSOLE: Lazy<io::serial::Console> = Lazy::new(|| {
    let mut console = io::serial::Console::new().unwrap();
    let mut escape_hit = false;
    console.set_processor(move |x| {
        if !escape_hit {
            if x == 1 {
                escape_hit = true;
                return None;
            }
            return Some(x);
        }

        escape_hit = false;

        match x {
            b't' => {
                let model_id = if crate::get_flags().model_id == 0 { 1 } else { 0 };
                crate::shutdown(crate::ExitReason::SwitchModel(model_id));
            }
            b'x' => {
                println!("Terminated");
                crate::shutdown(crate::ExitReason::Exit(0));
            }
            b'p' => {
                crate::shutdown(crate::ExitReason::PrintStats);
            }
            b'c' => unsafe {
                libc::raise(libc::SIGTRAP);
            },

            1 => return Some(x),

            _ => (),
        }
        None
    });
    console
});

static IO_BOUNDARY: RoCell<usize> = RoCell::new(0);

static MEM_BOUNDARY: RoCell<usize> = RoCell::new(usize::MAX);

pub static LIBC_RETURN_PC: RoCell<u64> = RoCell::new(0);

pub fn init() {
    unsafe {
        RoCell::replace(&IO_BOUNDARY, 0x40000000);

        let phys_size = (crate::CONFIG.memory
            + (if crate::CONFIG.firmware.is_some() { 2 } else { 0 }))
            * 1024
            * 1024;
        let phys_limit = 0x40000000 + phys_size;

        RoCell::replace(&MEM_BOUNDARY, phys_limit);

        let result = libc::mmap(
            0x200000 as _,
            (phys_limit - 0x200000) as _,
            libc::PROT_NONE,
            libc::MAP_ANONYMOUS | libc::MAP_PRIVATE | libc::MAP_FIXED,
            -1,
            0,
        );
        if result == libc::MAP_FAILED {
            panic!("mmap failed while initing");
        }

        let result =
            libc::mprotect(0x40000000 as _, phys_size as _, libc::PROT_READ | libc::PROT_WRITE);
        if result != 0 {
            panic!("mmap failed while initing");
        }
    }
    Lazy::force(&IO_SYSTEM);
}

pub fn device_tree() -> fdt::Node {
    let mut root = fdt::Node::new("");
    root.add_prop("model", "riscv-virtio,qemu");
    root.add_prop("compatible", "riscv-virtio");
    root.add_prop("#address-cells", 2u32);
    root.add_prop("#size-cells", 2u32);

    let chosen = root.add_node("chosen");
    chosen.add_prop("bootargs", crate::CONFIG.cmdline.as_str());

    let cpus = root.add_node("cpus");
    cpus.add_prop("timebase-frequency", 1000000u32);
    cpus.add_prop("#address-cells", 1u32);
    cpus.add_prop("#size-cells", 0u32);

    let core_count = crate::core_count() as u32;

    for i in 0..core_count {
        let cpu = cpus.add_node(format!("cpu@{:x}", i));
        cpu.add_prop("clock-frequency", 0u32);
        cpu.add_prop("mmu-type", "riscv,sv39");
        cpu.add_prop("riscv,isa", "rv64imafdc");
        cpu.add_prop("compatible", "riscv");
        cpu.add_prop("status", "okay");
        cpu.add_prop("reg", i);
        cpu.add_prop("device_type", "cpu");

        let intc = cpu.add_node("interrupt-controller");
        intc.add_prop("#interrupt-cells", 1u32);
        intc.add_prop("interrupt-controller", ());
        intc.add_prop("compatible", "riscv,cpu-intc");
        intc.add_prop("phandle", i + 1);
    }

    root.child.push(IO_SYSTEM.device_tree().clone());

    let memory = root.add_node("memory@40000000");
    memory.add_prop("reg", &[0x40000000, (crate::CONFIG.memory * 1024 * 1024) as u64][..]);
    memory.add_prop("device_type", "memory");

    root
}

pub fn read_memory<T: Copy>(addr: usize) -> T {
    assert!(addr >= *IO_BOUNDARY, "{:x} access out-of-bound", addr);
    unsafe { std::ptr::read(addr as *const T) }
}

pub fn io_read(addr: usize, size: u32) -> u64 {
    assert!(addr >= 4096 && addr < *IO_BOUNDARY, "{:x} access out-of-bound", addr);
    IO_SYSTEM.read(addr, size)
}

pub fn io_write(addr: usize, value: u64, size: u32) {
    assert!(addr >= 4096 && addr < *IO_BOUNDARY, "{:x} access out-of-bound", addr);
    IO_SYSTEM.write(addr, value, size)
}

#[macro_use]
extern crate log;

pub mod hw;

pub mod block;
pub mod network;
pub mod serial;

#[cfg(feature = "entropy")]
pub mod entropy;
#[cfg(feature = "fs")]
pub mod fs;
#[cfg(feature = "system")]
pub mod system;

use futures::future::BoxFuture;
use std::time::Duration;

pub trait DmaContext: Send + Sync {
    fn dma_read<'asyn>(&'asyn self, addr: u64, buf: &'asyn mut [u8]) -> BoxFuture<'asyn, ()>;

    fn dma_write<'asyn>(&'asyn self, addr: u64, buf: &'asyn [u8]) -> BoxFuture<'asyn, ()>;

    fn read_u16<'asyn>(&'asyn self, addr: u64) -> BoxFuture<'asyn, u16>;

    fn write_u16<'asyn>(&'asyn self, addr: u64, value: u16) -> BoxFuture<'asyn, ()>;
}

pub trait RuntimeContext: Send + Sync {
    fn now(&self) -> Duration;

    fn create_timer(&self, time: Duration) -> BoxFuture<'static, ()>;

    fn spawn(&self, task: BoxFuture<'static, ()>);

    fn spawn_blocking(&self, name: &str, task: BoxFuture<'static, ()>);
}

pub trait IrqPin: Send + Sync {
    fn set_level(&self, level: bool);

    fn raise(&self) {
        self.set_level(true);
    }

    fn lower(&self) {
        self.set_level(false);
    }

    fn pulse(&self) {
        self.raise();
        self.lower();
    }
}

pub trait IoMemory: Send + Sync {
    fn read(&self, addr: usize, size: u32) -> u64;

    fn write(&self, addr: usize, value: u64, size: u32);
}

pub trait IoMemoryMut {
    fn read_mut(&mut self, addr: usize, size: u32) -> u64;

    fn write_mut(&mut self, addr: usize, value: u64, size: u32);
}

impl<T: IoMemory> IoMemory for &'_ T {
    fn read(&self, addr: usize, size: u32) -> u64 {
        (**self).read(addr, size)
    }

    fn write(&self, addr: usize, value: u64, size: u32) {
        (**self).write(addr, value, size)
    }
}

impl<T: IoMemory + ?Sized> IoMemoryMut for T {
    fn read_mut(&mut self, addr: usize, size: u32) -> u64 {
        self.read(addr, size)
    }
    fn write_mut(&mut self, addr: usize, value: u64, size: u32) {
        self.write(addr, value, size)
    }
}

impl<R: lock_api::RawMutex + Send + Sync, T: IoMemoryMut + Send> IoMemory
    for lock_api::Mutex<R, T>
{
    fn read(&self, addr: usize, size: u32) -> u64 {
        self.lock().read_mut(addr, size)
    }
    fn write(&self, addr: usize, value: u64, size: u32) {
        self.lock().write_mut(addr, value, size)
    }
}

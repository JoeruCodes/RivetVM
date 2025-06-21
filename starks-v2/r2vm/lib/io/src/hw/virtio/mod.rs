use std::convert::TryInto;

mod mmio;
mod queue;
pub use mmio::Mmio;
pub use queue::{Buffer, BufferReader, BufferWriter, Queue, QueueNotReady};

#[cfg(feature = "virtio-network")]
mod network;
#[cfg(feature = "virtio-network")]
pub use network::Network;

#[cfg(feature = "virtio-block")]
mod block;
#[cfg(feature = "virtio-block")]
pub use block::Block;

#[cfg(feature = "virtio-rng")]
mod rng;
#[cfg(feature = "virtio-rng")]
pub use rng::Rng;

#[cfg(feature = "virtio-p9")]
mod p9;
#[cfg(feature = "virtio-p9")]
pub use self::p9::P9;

#[cfg(feature = "virtio-console")]
mod console;
#[cfg(feature = "virtio-console")]
pub use console::Console;

#[derive(Clone, Copy)]
#[non_exhaustive]
pub enum DeviceId {
    Reserved = 0,
    Network = 1,
    Block = 2,
    Console = 3,
    Entropy = 4,
    P9 = 9,
}

pub trait Device: Send {
    fn device_id(&self) -> DeviceId;

    fn device_feature(&self) -> u32 {
        0
    }

    fn driver_feature(&mut self, _value: u32) {}

    fn get_status(&self) -> u32;

    fn set_status(&mut self, status: u32);

    fn config_space(&self) -> &[u8] {
        unimplemented!()
    }

    fn with_config_space(&self, f: &mut dyn FnMut(&[u8])) {
        f(self.config_space())
    }

    fn config_read(&mut self, offset: usize, size: u32) -> u64 {
        let mut value = 0;
        self.with_config_space(&mut |config| {
            if offset + size as usize > config.len() {
                error!(target: "Mmio", "out-of-bound config register read 0x{:x}", offset);
                return;
            }
            let slice = &config[offset..offset + size as usize];
            value = match size {
                8 => u64::from_le_bytes(slice.try_into().unwrap()) as u64,
                4 => u32::from_le_bytes(slice.try_into().unwrap()) as u64,
                2 => u16::from_le_bytes(slice.try_into().unwrap()) as u64,
                _ => slice[0] as u64,
            };
        });
        value
    }

    fn config_write(&mut self, offset: usize, value: u64, _size: u32) {
        error!(target: "Mmio", "config register write 0x{:x} = 0x{:x}", offset, value);
    }

    fn num_queues(&self) -> usize;

    fn max_queue_len(&self, _idx: usize) -> u16 {
        32768
    }

    fn reset(&mut self);

    fn queue_ready(&mut self, idx: usize, queue: Queue);

    fn interrupt_status(&mut self) -> u32 {
        1
    }

    fn interrupt_ack(&mut self, _ack: u32) {}
}

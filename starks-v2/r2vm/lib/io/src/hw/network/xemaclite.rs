use crate::RuntimeContext;
use crate::network::Network as NetworkDevice;
use crate::{IoMemory, IrqPin};
use byteorder::{ByteOrder, LE};
use futures::channel::mpsc::Sender;
use futures::future::{AbortHandle, poll_fn};
use futures::prelude::*;
use parking_lot::Mutex;
use std::sync::Arc;
use std::task::Poll;

trait Mdio {
    fn read(&mut self, reg: u8) -> u16;
    fn write(&mut self, reg: u8, value: u16);
}

struct Mii;

impl Mdio for Mii {
    fn read(&mut self, reg: u8) -> u16 {
        match reg {
            0 => 0b00110001_00000000,
            1 => 0b01000000_00101101,
            2 => 7,
            3 => 49393,
            _ => {
                warn!(target: "MDIO", "unimplemented MDIO register read {}", reg);
                0xffff
            }
        }
    }

    fn write(&mut self, reg: u8, value: u16) {
        match reg {
            _ => {
                warn!(target: "MDIO", "unimplemented MDIO register write {}={:x}", reg, value);
            }
        }
    }
}

const ADDR_MDIOADDR: usize = 0x7E4;
const ADDR_MDIOWR: usize = 0x7E8;
const ADDR_MDIORD: usize = 0x7EC;
const ADDR_MDIOCTRL: usize = 0x7F0;
const ADDR_TX_LEN_PING: usize = 0x7F4;
const ADDR_GIE: usize = 0x7F8;
const ADDR_TX_CTRL_PING: usize = 0x7FC;
const ADDR_TX_LEN_PONG: usize = 0xFF4;
const ADDR_TX_CTRL_PONG: usize = 0xFFC;
const ADDR_RX_CTRL_PING: usize = 0x17FC;
const ADDR_RX_CTRL_PONG: usize = 0x1FFC;

pub struct XemacLite {
    inner: Arc<Inner>,
    rx_handle: AbortHandle,

    tx_sender: Mutex<Sender<bool>>,
}

struct Inner {
    state: Mutex<State>,
    irq: Box<dyn IrqPin>,
    net: Box<dyn NetworkDevice>,
    ctx: Arc<dyn RuntimeContext>,
}

struct State {
    mdio_enable: bool,

    mdio_op: bool,

    mdio_phyaddr: u8,

    mdio_regaddr: u8,

    mdio_wr: u16,

    mdio_rd: u16,
    tx_len_ping: u16,
    tx_len_pong: u16,
    global_irq_enabled: bool,
    tx_irq_enabled: bool,
    rx_irq_enabled: bool,
    tx_status_ping: bool,
    tx_status_pong: bool,
    rx_status_ping: bool,
    rx_status_pong: bool,
    buffer: [u8; 8192],
    mac: [u8; 6],
    mii: Mii,
}

impl Drop for XemacLite {
    fn drop(&mut self) {
        self.rx_handle.abort();
    }
}

impl XemacLite {
    pub fn new(
        ctx: Arc<dyn RuntimeContext>,
        irq: Box<dyn IrqPin>,
        net: Box<dyn NetworkDevice>,
    ) -> Self {
        let state = State {
            mdio_enable: false,
            mdio_op: false,
            mdio_phyaddr: 0,
            mdio_regaddr: 0,
            mdio_wr: 0,
            mdio_rd: 0,
            tx_len_ping: 0,
            tx_len_pong: 0,
            global_irq_enabled: false,
            tx_irq_enabled: false,
            rx_irq_enabled: false,
            tx_status_ping: false,
            tx_status_pong: false,
            rx_status_ping: false,
            rx_status_pong: false,
            buffer: [0; 8192],
            mac: [0; 6],
            mii: Mii,
        };
        let inner = Arc::new(Inner { state: Mutex::new(state), ctx, irq, net });
        let rx_handle = Self::start_rx(inner.clone());
        let tx_sender = Self::start_tx(inner.clone());
        Self { inner, rx_handle, tx_sender: Mutex::new(tx_sender) }
    }

    fn start_tx(inner: Arc<Inner>) -> futures::channel::mpsc::Sender<bool> {
        let (sender, mut recv) = futures::channel::mpsc::channel::<bool>(2);
        let ctx = inner.ctx.clone();
        ctx.spawn(Box::pin(async move {
            while let Some(pong) = recv.next().await {
                poll_fn(|cx| {
                    let mut state = inner.state.lock();
                    let buffer = if !pong {
                        if !state.tx_status_ping {
                            return Poll::Ready(Ok(()));
                        }
                        &state.buffer[0..state.tx_len_ping as usize]
                    } else {
                        if !state.tx_status_pong {
                            return Poll::Ready(Ok(()));
                        }
                        &state.buffer[0x800..0x800 + state.tx_len_pong as usize]
                    };
                    inner.net.poll_send(cx, buffer).map_ok(|_| {
                        if !pong {
                            state.tx_status_ping = false;
                        } else {
                            state.tx_status_pong = false;
                        }
                        if state.global_irq_enabled && state.tx_irq_enabled {
                            inner.irq.pulse();
                        }
                    })
                })
                .await
                .unwrap();
            }
        }));
        sender
    }
}

impl IoMemory for XemacLite {
    fn read(&self, addr: usize, size: u32) -> u64 {
        let state = self.inner.state.lock();

        if size == 8 && (addr & 0x7ff) < 0x7e0 {
            return LE::read_u64(&state.buffer[addr..]);
        }

        if size != 4 {
            error!(target: "xemaclite", "illegal register read 0x{:x}", addr);
            return 0;
        }
        (match addr {
            ADDR_MDIOADDR => {
                (state.mdio_op as u32) << 10
                    | (state.mdio_phyaddr as u32) << 5
                    | state.mdio_regaddr as u32
            }
            ADDR_MDIOWR => state.mdio_wr as u32,
            ADDR_MDIORD => state.mdio_rd as u32,
            ADDR_MDIOCTRL => (state.mdio_enable as u32) << 3,
            ADDR_TX_LEN_PING => state.tx_len_ping as u32,
            ADDR_GIE => (state.global_irq_enabled as u32) << 31,
            ADDR_TX_LEN_PONG => state.tx_len_pong as u32,
            ADDR_TX_CTRL_PING => (state.tx_irq_enabled as u32) << 3 | state.tx_status_ping as u32,
            ADDR_TX_CTRL_PONG => state.tx_status_pong as u32,
            ADDR_RX_CTRL_PING => (state.rx_irq_enabled as u32) << 3 | state.rx_status_ping as u32,
            ADDR_RX_CTRL_PONG => state.rx_status_pong as u32,
            _ => LE::read_u32(&state.buffer[addr..]),
        }) as u64
    }

    fn write(&self, addr: usize, value: u64, size: u32) {
        let mut state = self.inner.state.lock();
        let state = &mut *state;

        if size == 8 && (addr & 0x7ff) < 0x7e0 {
            LE::write_u64(&mut state.buffer[addr..], value);
            return;
        }

        if size != 4 {
            error!(target: "Xemaclite", "illegal register write 0x{:x} = 0x{:x}", addr, value);
            return;
        }
        let value = value as u32;

        match addr {
            ADDR_MDIOADDR => {
                state.mdio_op = value & (1 << 10) != 0;
                state.mdio_phyaddr = ((value >> 5) & 0b11111) as u8;
                state.mdio_regaddr = (value & 0b11111) as u8;
            }
            ADDR_MDIOWR => {
                state.mdio_wr = value as u16;
            }
            ADDR_MDIORD => (),
            ADDR_MDIOCTRL => {
                state.mdio_enable = value & (1 << 3) != 0;

                if state.mdio_enable && (value & 1) != 0 {
                    if state.mdio_op {
                        state.mdio_rd = if state.mdio_phyaddr == 1 {
                            state.mii.read(state.mdio_regaddr)
                        } else {
                            0xffff
                        };
                    } else {
                        if state.mdio_phyaddr == 1 {
                            state.mii.write(state.mdio_regaddr, state.mdio_wr);
                        }
                    }
                }
            }
            ADDR_TX_LEN_PING => state.tx_len_ping = (value as u16).min(2048),
            ADDR_GIE => state.global_irq_enabled = (value >> 31) & 1 != 0,
            ADDR_TX_CTRL_PING => {
                state.tx_irq_enabled = (value >> 3) & 1 != 0;
                let program = (value >> 1) & 1 != 0;
                let status = value & 1 != 0;
                if !state.tx_status_ping && status {
                    if program {
                        state.mac.copy_from_slice(&state.buffer[0..6]);
                        if state.global_irq_enabled && state.tx_irq_enabled {
                            self.inner.irq.pulse();
                        }
                    } else {
                        state.tx_status_ping = true;
                        self.tx_sender.lock().try_send(false).unwrap();
                    }
                }
            }
            ADDR_TX_LEN_PONG => state.tx_len_pong = (value as u16).min(2048),
            ADDR_TX_CTRL_PONG => {
                let program = (value >> 1) & 1 != 0;
                let status = value & 1 != 0;
                if !state.tx_status_pong && status {
                    if program {
                        state.mac.copy_from_slice(&state.buffer[0x800..0x806]);
                        if state.global_irq_enabled && state.tx_irq_enabled {
                            self.inner.irq.pulse();
                        }
                    } else {
                        state.tx_status_pong = true;
                        self.tx_sender.lock().try_send(true).unwrap();
                    }
                }
            }
            ADDR_RX_CTRL_PING => {
                state.rx_irq_enabled = (value >> 3) & 1 != 0;
                let status = value & 1 != 0;
                if !status {
                    state.rx_status_ping = false;
                }
            }
            ADDR_RX_CTRL_PONG => {
                let status = value & 1 != 0;
                if !status {
                    state.rx_status_pong = false;
                }
            }
            _ => LE::write_u32(&mut state.buffer[addr..], value as u32),
        }
    }
}

impl XemacLite {
    fn start_rx(inner: Arc<Inner>) -> AbortHandle {
        let ctx = inner.ctx.clone();
        let (handle, reg) = futures::future::AbortHandle::new_pair();
        ctx.spawn(Box::pin(async move {
            let _ = futures::future::Abortable::new(
                async move {
                    let mut buffer = [0; 2048];
                    loop {
                        let len = inner.net.recv(&mut buffer).await.unwrap();
                        {
                            let mut guard = inner.state.lock();
                            if !guard.rx_status_ping {
                                guard.buffer[0x1000..0x1000 + len].copy_from_slice(&buffer[0..len]);
                                guard.rx_status_ping = true;
                                if guard.global_irq_enabled && guard.rx_irq_enabled {
                                    inner.irq.pulse();
                                }
                            } else {
                                info!(
                                    target: "Xemaclite",
                                    "discard packet of size {:x} because ping buffer is not empty",
                                    len
                                );
                            }
                        }

                        let len = inner.net.recv(&mut buffer).await.unwrap();
                        {
                            let mut guard = inner.state.lock();
                            if !guard.rx_status_pong {
                                guard.buffer[0x1800..0x1800 + len].copy_from_slice(&buffer[0..len]);
                                guard.rx_status_pong = true;
                                if guard.global_irq_enabled && guard.rx_irq_enabled {
                                    inner.irq.pulse();
                                }
                            } else {
                                info!(
                                    target: "Xemaclite",
                                    "discard packet of size {:x} because pong buffer is not empty",
                                    len
                                );
                            }
                        }
                    }
                },
                reg,
            )
            .await;
        }));
        handle
    }

    pub fn build_dt(base: usize, mac: [u8; 6]) -> fdt::Node {
        let mut node = fdt::Node::new(format!("ethernet@{:x}", base));
        node.add_prop("compatible", "xlnx,xps-ethernetlite-3.00.a");
        node.add_prop("device_type", "network");
        node.add_prop("local-mac-address", &mac[..]);
        node.add_prop("phy-handle", 100u32);
        node.add_prop("xlnx,rx-ping-pong", 1u32);
        node.add_prop("xlnx,tx-ping-pong", 1u32);
        let mdio = node.add_node("mdio");
        mdio.add_prop("#address-cells", 1u32);
        mdio.add_prop("#size-cells", 0u32);
        let phy = mdio.add_node("ethernet-phy@1");
        phy.add_prop("reg", 1u32);
        phy.add_prop("phandle", 100u32);
        node
    }
}

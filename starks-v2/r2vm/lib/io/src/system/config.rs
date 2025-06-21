#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};
use std::net::Ipv4Addr;
use std::path::PathBuf;

#[cfg(feature = "serde")]
fn return_true() -> bool {
    true
}

#[derive(Debug, Default)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct DeviceConfig<T> {
    #[cfg_attr(feature = "serde", serde(default))]
    pub io_base: Option<usize>,

    #[cfg_attr(feature = "serde", serde(default))]
    pub irq: Option<u32>,

    #[cfg_attr(feature = "serde", serde(flatten))]
    pub config: T,
}

#[derive(Debug, Default)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct ClintConfig {}

#[derive(Debug)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[cfg_attr(feature = "serde", serde(rename_all = "lowercase"))]
pub enum ConsoleType {
    Virtio,
    NS16550,
}

impl Default for ConsoleType {
    fn default() -> Self {
        ConsoleType::Virtio
    }
}

#[derive(Debug)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct ConsoleConfig {
    #[cfg_attr(feature = "serde", serde(default))]
    pub r#type: ConsoleType,

    #[cfg_attr(feature = "serde", serde(default = "return_true"))]
    pub resize: bool,
}

impl Default for ConsoleConfig {
    fn default() -> Self {
        ConsoleConfig { r#type: ConsoleType::Virtio, resize: true }
    }
}

#[derive(Debug)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct DriveConfig {
    #[cfg_attr(feature = "serde", serde(default))]
    pub shadow: bool,

    pub path: PathBuf,
}

#[derive(Debug)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[cfg_attr(feature = "serde", serde(rename_all = "lowercase"))]
pub enum RandomType {
    Pseudo,
    OS,
}

#[cfg(feature = "serde")]
fn default_seed() -> u64 {
    0xcafebabedeadbeef
}

#[derive(Debug)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct RandomConfig {
    pub r#type: RandomType,
    #[cfg_attr(feature = "serde", serde(default = "default_seed"))]
    pub seed: u64,
}

#[derive(Debug)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct ShareConfig {
    pub tag: String,

    pub path: PathBuf,
}

#[cfg(feature = "serde")]
fn default_host_addr() -> Ipv4Addr {
    Ipv4Addr::new(127, 0, 0, 1)
}

#[derive(Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[cfg_attr(feature = "serde", serde(rename_all = "lowercase"))]
pub enum ForwardProtocol {
    Tcp,
    Udp,
}

#[derive(Debug)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct ForwardConfig {
    pub protocol: ForwardProtocol,

    #[cfg_attr(feature = "serde", serde(default = "default_host_addr"))]
    pub host_addr: Ipv4Addr,

    pub host_port: u16,

    pub guest_port: u16,
}

#[cfg(feature = "serde")]
fn default_net_type() -> String {
    "virtio".to_owned()
}

#[cfg(feature = "serde")]
fn default_mac() -> String {
    "02:00:00:00:00:01".to_owned()
}

#[derive(Debug)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct NetworkConfig {
    #[cfg_attr(feature = "serde", serde(default = "default_net_type"))]
    pub r#type: String,

    #[cfg_attr(feature = "serde", serde(default = "default_mac"))]
    pub mac: String,

    #[cfg_attr(feature = "serde", serde(default))]
    pub forward: Vec<ForwardConfig>,
}

#[derive(Debug, Default)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct RTCConfig {
    #[cfg_attr(feature = "serde", serde(default))]
    pub irq2: Option<u32>,
}

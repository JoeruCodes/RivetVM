use io::system::config::*;
use serde::{Deserialize, Serialize};
use std::path::PathBuf;

fn default_core() -> usize {
    4
}
fn default_memory() -> usize {
    1024
}
fn default_cmdline() -> String {
    "console=hvc0 rw root=/dev/vda".to_owned()
}

#[derive(Serialize, Deserialize, Debug)]
pub struct Config {
    #[serde(default = "default_core")]
    pub core: usize,

    pub kernel: PathBuf,

    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub firmware: Option<PathBuf>,

    #[serde(default = "default_memory")]
    pub memory: usize,

    #[serde(default = "default_cmdline")]
    pub cmdline: String,

    #[serde(default)]
    pub clint: Option<DeviceConfig<ClintConfig>>,

    #[serde(default)]
    pub plic: DeviceConfig<PlicConfig>,

    #[serde(default)]
    pub console: Option<DeviceConfig<ConsoleConfig>>,

    #[serde(default)]
    pub rtc: Option<DeviceConfig<RTCConfig>>,

    #[serde(default)]
    pub drive: Vec<DeviceConfig<DriveConfig>>,

    #[serde(default)]
    pub random: Vec<DeviceConfig<RandomConfig>>,

    #[serde(default)]
    pub share: Vec<DeviceConfig<ShareConfig>>,

    #[serde(default)]
    pub network: Vec<DeviceConfig<NetworkConfig>>,
}

#[derive(Serialize, Deserialize, Debug, Default)]
pub struct PlicConfig {}

#[derive(Serialize, Deserialize, Debug, Default)]
pub struct ClintConfig {}

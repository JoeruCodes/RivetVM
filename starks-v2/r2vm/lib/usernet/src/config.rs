use std::net::{Ipv4Addr, Ipv6Addr};
use std::path::PathBuf;

#[derive(Debug, Clone)]
pub struct Ipv4Config {
    pub net: Ipv4Addr,

    pub mask: Ipv4Addr,

    pub host: Ipv4Addr,

    pub dhcp_start: Ipv4Addr,

    pub dns: Ipv4Addr,
}

impl Default for Ipv4Config {
    fn default() -> Self {
        Self {
            net: Ipv4Addr::new(10, 0, 2, 0),
            mask: Ipv4Addr::new(255, 255, 255, 0),
            host: Ipv4Addr::new(10, 0, 2, 2),
            dhcp_start: Ipv4Addr::new(10, 0, 2, 15),
            dns: Ipv4Addr::new(10, 0, 2, 3),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Ipv6Config {
    pub prefix: Ipv6Addr,

    pub prefix_len: u8,

    pub host: Ipv6Addr,

    pub dns: Ipv6Addr,
}

impl Default for Ipv6Config {
    fn default() -> Self {
        Self {
            prefix: Ipv6Addr::new(0xfec0, 0, 0, 0, 0, 0, 0, 0),
            prefix_len: 64,
            host: Ipv6Addr::new(0xfec0, 0, 0, 0, 0, 0, 0, 2),
            dns: Ipv6Addr::new(0xfec0, 0, 0, 0, 0, 0, 0, 3),
        }
    }
}

#[derive(Debug)]
pub struct TftpConfig {
    pub name: Option<String>,

    pub root: PathBuf,

    pub bootfile: Option<String>,
}

#[derive(Debug)]
pub struct Config {
    pub restricted: bool,

    pub ipv4: Option<Ipv4Config>,

    pub ipv6: Option<Ipv6Config>,

    pub hostname: Option<String>,

    pub tftp: Option<TftpConfig>,

    pub dns_suffixes: Vec<String>,

    pub domainname: Option<String>,
}

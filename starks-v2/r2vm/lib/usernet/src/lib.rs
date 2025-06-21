use std::future::Future;
use std::pin::Pin;
use std::time::Duration;

mod config;
mod slirp;
mod util;

pub use config::*;
pub use slirp::Network;

pub trait Context {
    fn now(&mut self) -> Duration;

    fn create_timer(&mut self, time: Duration) -> Pin<Box<dyn Future<Output = ()> + Send>>;

    fn spawn(&mut self, future: Pin<Box<dyn Future<Output = ()> + Send>>);
}

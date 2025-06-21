use futures::future::poll_fn;
use std::io::Result;
use std::task::{Context, Poll};

#[cfg(feature = "network-logger")]
mod logger;
#[cfg(feature = "network-logger")]
pub use logger::Logger;
#[cfg(feature = "network-usernet")]
mod usernet;
#[cfg(feature = "network-usernet")]
pub use self::usernet::Usernet;

pub trait Network: Send + Sync {
    fn poll_send(&self, ctx: &mut Context, buf: &[u8]) -> Poll<Result<usize>>;

    fn poll_recv(&self, ctx: &mut Context, buf: &mut [u8]) -> Poll<Result<usize>>;
}

impl dyn Network {
    pub async fn send(&self, buf: &[u8]) -> Result<usize> {
        poll_fn(|cx| self.poll_send(cx, buf)).await
    }

    pub async fn recv(&self, buf: &mut [u8]) -> Result<usize> {
        poll_fn(|cx| self.poll_recv(cx, buf)).await
    }
}

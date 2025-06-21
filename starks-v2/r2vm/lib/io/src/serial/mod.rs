use futures::future::poll_fn;
use std::io::{Error, ErrorKind, Result};
use std::task::{Context, Poll};

#[cfg(feature = "serial-console")]
mod console;
#[cfg(feature = "serial-console")]
pub use console::Console;

pub trait Serial: Send + Sync {
    fn poll_write(&self, cx: &mut Context, buf: &[u8]) -> Poll<Result<usize>>;

    fn poll_read(&self, cx: &mut Context, buf: &mut [u8]) -> Poll<Result<usize>>;

    fn get_window_size(&self) -> Result<(u16, u16)> {
        Err(Error::new(ErrorKind::Other, "get_window_size not supported"))
    }

    fn poll_window_size_changed(&self, cx: &mut Context) -> Poll<Result<()>> {
        let _ = cx;
        Poll::Ready(Err(Error::new(ErrorKind::Other, "poll_window_size_changed not supported")))
    }
}

impl<T: Serial + ?Sized, P: std::ops::Deref<Target = T> + Send + Sync> Serial for P {
    fn poll_write(&self, cx: &mut Context, buf: &[u8]) -> Poll<Result<usize>> {
        (**self).poll_write(cx, buf)
    }

    fn poll_read(&self, cx: &mut Context, buf: &mut [u8]) -> Poll<Result<usize>> {
        (**self).poll_read(cx, buf)
    }

    fn get_window_size(&self) -> Result<(u16, u16)> {
        (**self).get_window_size()
    }

    fn poll_window_size_changed(&self, cx: &mut Context) -> Poll<Result<()>> {
        (**self).poll_window_size_changed(cx)
    }
}

impl dyn Serial {
    pub async fn write(&self, buf: &[u8]) -> Result<usize> {
        poll_fn(|cx| self.poll_write(cx, buf)).await
    }

    pub async fn read(&self, buf: &mut [u8]) -> Result<usize> {
        poll_fn(|cx| self.poll_read(cx, buf)).await
    }

    pub async fn wait_window_size_changed(&self) -> Result<()> {
        poll_fn(|cx| self.poll_window_size_changed(cx)).await
    }

    pub fn try_write(&self, buf: &[u8]) -> Result<usize> {
        let mut cx = std::task::Context::from_waker(futures::task::noop_waker_ref());
        match self.poll_write(&mut cx, buf) {
            Poll::Ready(x) => x,
            Poll::Pending => Err(Error::new(ErrorKind::WouldBlock, "WouldBlock")),
        }
    }

    pub fn try_read(&self, buf: &mut [u8]) -> Result<usize> {
        let mut cx = std::task::Context::from_waker(futures::task::noop_waker_ref());
        match self.poll_read(&mut cx, buf) {
            Poll::Ready(x) => x,
            Poll::Pending => Err(Error::new(ErrorKind::WouldBlock, "WouldBlock")),
        }
    }
}

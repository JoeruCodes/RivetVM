use parking_lot::Mutex;
use std::future::Future;
use std::pin::Pin;
use std::sync::Arc;
use std::task::{Context, Poll, Waker};

struct ReplaceableInner {
    future: Option<Pin<Box<dyn Future<Output = ()> + Send>>>,
    waker: Option<Waker>,
}

pub struct ReplaceableTask {
    inner: Arc<Mutex<ReplaceableInner>>,
}

impl ReplaceableTask {
    pub fn new() -> (ReplaceableTask, ReplaceableFuture) {
        let inner = Arc::new(Mutex::new(ReplaceableInner { future: None, waker: None }));
        let fut = ReplaceableFuture { inner: inner.clone(), started: false };
        (ReplaceableTask { inner }, fut)
    }

    pub fn replace(&self, future: Pin<Box<dyn Future<Output = ()> + Send>>) {
        let mut inner = self.inner.lock();
        inner.future = Some(future);
        inner.waker.as_ref().map(|x| x.wake_by_ref());
    }
}

impl Drop for ReplaceableTask {
    fn drop(&mut self) {
        if let Some(waker) = self.inner.lock().waker.take() {
            waker.wake();
        }
    }
}

pub struct ReplaceableFuture {
    inner: Arc<Mutex<ReplaceableInner>>,
    started: bool,
}

impl Future for ReplaceableFuture {
    type Output = ();

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<()> {
        let this = self.get_mut();
        let mut inner = this.inner.lock();
        if !this.started {
            this.started = true;
            inner.waker = Some(cx.waker().clone());
        } else {
            if inner.waker.is_none() {
                return Poll::Ready(());
            }
        }

        if let Some(mut fut) = inner.future.take() {
            std::mem::drop(inner);
            if fut.as_mut().poll(cx).is_pending() {
                inner = this.inner.lock();
                if inner.future.is_none() {
                    inner.future = Some(fut);
                }
            }
        }
        Poll::Pending
    }
}

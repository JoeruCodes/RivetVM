use futures::future::BoxFuture;
use futures::task::ArcWake;
use parking_lot::{Condvar, Mutex, MutexGuard};
use std::collections::BinaryHeap;
use std::future::Future;
use std::pin::Pin;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::task::{Context, Poll, Waker};
use std::time::{Duration, Instant};

struct Task {
    future: Mutex<Option<BoxFuture<'static, ()>>>,
}

impl ArcWake for Task {
    fn wake_by_ref(arc_self: &Arc<Self>) {
        arc_self.clone().wake();
    }

    fn wake(self: Arc<Self>) {
        let event_loop = crate::event_loop();

        event_loop.queue_handler(0, Handler::Task(self));
    }
}

enum Handler {
    Func(Box<dyn FnOnce() + Send>),
    Waker(Waker),

    Task(Arc<Task>),
}

struct Entry {
    time: u64,
    handler: Handler,
}

struct Timer {
    time: u64,
    polled: bool,
}

impl Future for Timer {
    type Output = ();

    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<()> {
        let event_loop = crate::event_loop();
        if event_loop.cycle() >= self.time {
            return Poll::Ready(());
        }
        if !self.polled {
            self.polled = true;
            let waker = cx.waker().clone();
            event_loop.queue_handler(self.time, Handler::Waker(waker));
        }
        Poll::Pending
    }
}

impl PartialEq for Entry {
    fn eq(&self, other: &Self) -> bool {
        self.time == other.time
    }
}

impl Eq for Entry {}

impl PartialOrd for Entry {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Entry {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        other.time.cmp(&self.time)
    }
}

#[repr(C)]
pub struct EventLoop {
    cycle: AtomicU64,
    next_event: AtomicU64,

    epoch: ro_cell::RoCell<Instant>,
    condvar: Condvar,

    events: Mutex<BinaryHeap<Entry>>,
    shutdown: AtomicBool,

    lockstep_cycle_base: AtomicU64,
}

extern "C" {

    fn event_loop_wait();
}

impl EventLoop {
    pub fn new() -> EventLoop {
        EventLoop {
            cycle: AtomicU64::new(0),
            lockstep_cycle_base: AtomicU64::new(0),
            next_event: AtomicU64::new(u64::max_value()),
            epoch: ro_cell::RoCell::new(Instant::now()),
            condvar: Condvar::new(),
            events: Mutex::new(BinaryHeap::new()),
            shutdown: AtomicBool::new(false),
        }
    }

    pub fn shutdown(&self) {
        let guard = self.events.lock();

        if crate::threaded() {
            let cycle = self.cycle();
            let lockstep_cycle = self.get_lockstep_cycles();
            self.cycle.store(cycle, Ordering::Relaxed);
            self.lockstep_cycle_base.store(cycle - lockstep_cycle, Ordering::Relaxed);
        } else {
            let micro = (self.cycle() + 99) / 100;

            unsafe {
                ro_cell::RoCell::replace(&self.epoch, Instant::now() - Duration::from_micros(micro))
            };
        }
        std::mem::drop(guard);

        self.shutdown.store(true, Ordering::Relaxed);

        self.queue(0, Box::new(|| {}));
    }

    pub fn get_lockstep_cycles(&self) -> u64 {
        self.cycle.load(Ordering::Relaxed) - self.lockstep_cycle_base.load(Ordering::Relaxed)
    }

    pub fn cycle(&self) -> u64 {
        if crate::threaded() {
            let duration = Instant::now().duration_since(*self.epoch);
            duration.as_micros() as u64 * 100
        } else {
            self.cycle.load(Ordering::Relaxed)
        }
    }

    pub fn time(&self) -> u64 {
        self.cycle() / 100
    }

    fn queue_handler(&self, cycle: u64, handler: Handler) {
        let mut guard = self.events.lock();
        guard.push(Entry { time: cycle, handler });

        if crate::threaded() {
            if guard.peek().unwrap().time == cycle {
                self.condvar.notify_one();
            }
        } else {
            self.next_event.store(
                match guard.peek() {
                    Some(it) => it.time,
                    None => u64::max_value(),
                },
                Ordering::Relaxed,
            );
        }
    }

    pub fn queue(&self, cycle: u64, handler: Box<dyn FnOnce() + Send>) {
        self.queue_handler(cycle, Handler::Func(handler));
    }

    pub fn queue_time(&self, time: u64, handler: Box<dyn FnOnce() + Send>) {
        self.queue_handler(time.saturating_mul(100), Handler::Func(handler));
    }

    pub fn on_cycle(&self, cycle: u64) -> impl Future<Output = ()> + Send + 'static {
        Timer { time: cycle, polled: false }
    }

    pub fn on_time(&self, time: u64) -> impl Future<Output = ()> + Send + 'static {
        Timer { time: time.saturating_mul(100), polled: false }
    }

    fn handle_events(
        &self,
        mut guard: &mut MutexGuard<BinaryHeap<Entry>>,
        cycle: u64,
    ) -> Option<u64> {
        loop {
            let time = match guard.peek() {
                None => return None,
                Some(v) => v.time,
            };
            if time > cycle {
                return Some(time);
            }
            let entry = guard.pop().unwrap();
            MutexGuard::unlocked(&mut guard, || match entry.handler {
                Handler::Func(func) => func(),
                Handler::Waker(waker) => waker.wake(),
                Handler::Task(task) => {
                    let waker_ref = futures::task::waker_ref(&task);
                    let mut context = Context::from_waker(&waker_ref);

                    let mut lock = task.future.lock();
                    if let Some(ref mut future) = *lock {
                        let poll = unsafe { Pin::new_unchecked(future) }.poll(&mut context);
                        if poll.is_ready() {
                            *lock = None;
                        }
                    }
                }
            });
        }
    }

    pub fn event_loop(&self) {
        let mut guard = self.events.lock();
        loop {
            if self.shutdown.load(Ordering::Relaxed) {
                self.shutdown.store(false, Ordering::Relaxed);
                return;
            }
            let cycle = self.cycle();
            let result = self.handle_events(&mut guard, cycle);
            if crate::threaded() {
                match result {
                    None => {
                        self.condvar.wait(&mut guard);
                    }
                    Some(v) => {
                        self.condvar.wait_for(&mut guard, Duration::from_micros(v - cycle));
                    }
                }
            } else {
                self.next_event.store(result.unwrap_or(u64::max_value()), Ordering::Relaxed);
                MutexGuard::unlocked(&mut guard, || unsafe { event_loop_wait() });
            }
        }
    }

    pub fn spawn(&self, future: BoxFuture<'static, ()>) {
        let task = Arc::new(Task { future: Mutex::new(Some(future)) });
        task.wake();
    }
}

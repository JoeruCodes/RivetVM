use super::park::{UnparkToken, park, unpark_all, unpark_one};
use lock_api::RawMutex as LRawMutex;
use std::sync::atomic::{AtomicBool, AtomicU8, Ordering};

const LOCKED_BIT: u8 = 0b01;
const PARKED_BIT: u8 = 0b10;

pub struct RawMutex {
    locked: AtomicU8,
}

impl RawMutex {
    #[cold]
    fn lock_slow(&self) {
        let in_fiber = super::in_fiber();

        let mut spinwait = 0;
        let mut state = self.locked.load(Ordering::Relaxed);
        loop {
            if state & LOCKED_BIT == 0 {
                match self.locked.compare_exchange_weak(
                    state,
                    state | LOCKED_BIT,
                    Ordering::Acquire,
                    Ordering::Relaxed,
                ) {
                    Ok(_) => return,
                    Err(x) => state = x,
                }
                continue;
            }

            if !in_fiber {
                std::hint::spin_loop();
                state = self.locked.load(Ordering::Relaxed);
                continue;
            }

            if state & PARKED_BIT == 0 && spinwait < 20 {
                if spinwait < 10 {
                    std::hint::spin_loop();
                } else {
                    unsafe { super::raw::fiber_sleep(0) };
                }
                spinwait += 1;
                state = self.locked.load(Ordering::Relaxed);
                continue;
            }

            if state & PARKED_BIT == 0 {
                if let Err(x) = self.locked.compare_exchange_weak(
                    state,
                    state | PARKED_BIT,
                    Ordering::Relaxed,
                    Ordering::Relaxed,
                ) {
                    state = x;
                    continue;
                }
            }

            park(
                self as *const _ as usize,
                || self.locked.load(Ordering::Relaxed) == LOCKED_BIT | PARKED_BIT,
                || (),
            );

            spinwait = 0;
            state = self.locked.load(Ordering::Relaxed);
        }
    }

    #[cold]
    fn unlock_slow(&self) {
        unpark_one(self as *const _ as usize, |result| {
            self.locked.store(if result.have_more { PARKED_BIT } else { 0 }, Ordering::Release);
            UnparkToken(0)
        });
    }
}

unsafe impl LRawMutex for RawMutex {
    type GuardMarker = lock_api::GuardSend;

    const INIT: Self = Self { locked: AtomicU8::new(0) };

    #[inline]
    fn lock(&self) {
        if self
            .locked
            .compare_exchange_weak(0, LOCKED_BIT, Ordering::Acquire, Ordering::Relaxed)
            .is_err()
        {
            self.lock_slow();
        }
    }

    #[inline]
    fn try_lock(&self) -> bool {
        self.locked
            .fetch_update(Ordering::Acquire, Ordering::Relaxed, |state| {
                if state & LOCKED_BIT != 0 {
                    return None;
                }
                Some(state | LOCKED_BIT)
            })
            .is_ok()
    }

    #[inline]
    unsafe fn unlock(&self) {
        if self
            .locked
            .compare_exchange(LOCKED_BIT, 0, Ordering::Release, Ordering::Relaxed)
            .is_err()
        {
            self.unlock_slow();
        }
    }

    #[inline]
    fn is_locked(&self) -> bool {
        self.locked.load(Ordering::Relaxed) & LOCKED_BIT != 0
    }
}

pub type Mutex<T> = lock_api::Mutex<RawMutex, T>;

pub type MutexGuard<'a, T> = lock_api::MutexGuard<'a, RawMutex, T>;

pub struct Condvar {
    has_queue: AtomicBool,
}

impl Condvar {
    #[cold]
    fn notify_one_slow(&self) {
        unpark_one(self as *const _ as usize, |result| {
            if !result.have_more {
                self.has_queue.store(false, Ordering::Relaxed);
            }
            UnparkToken(0)
        });
    }

    #[cold]
    fn notify_all_slow(&self) {
        self.has_queue.store(false, Ordering::Relaxed);
        unpark_all(self as *const _ as usize, UnparkToken(0));
    }

    fn wait_slow(&self, mutex: &RawMutex) {
        park(
            self as *const _ as usize,
            || {
                if !self.has_queue.load(Ordering::Relaxed) {
                    self.has_queue.store(true, Ordering::Relaxed);
                }
                true
            },
            || unsafe {
                mutex.unlock();
            },
        );
        mutex.lock();
    }
}

impl Condvar {
    #[inline]
    pub const fn new() -> Self {
        Condvar { has_queue: AtomicBool::new(false) }
    }

    #[inline]
    pub fn notify_one(&self) {
        if self.has_queue.load(Ordering::Relaxed) {
            self.notify_one_slow();
        }
    }

    #[inline]
    pub fn notify_all(&self) {
        if self.has_queue.load(Ordering::Relaxed) {
            self.notify_all_slow();
        }
    }

    #[inline]
    pub fn wait<T>(&self, guard: &mut MutexGuard<'_, T>) {
        self.wait_slow(unsafe { MutexGuard::mutex(&guard).raw() });
    }
}

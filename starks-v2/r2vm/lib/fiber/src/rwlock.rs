use lock_api::{RawMutex as LRawMutex, RawRwLock as LRawRwLock};
use std::cell::Cell;

pub struct RawRwLock {
    read: super::RawMutex,
    write: super::RawMutex,

    readers: Cell<usize>,
}

unsafe impl Sync for RawRwLock {}

unsafe impl LRawRwLock for RawRwLock {
    type GuardMarker = lock_api::GuardSend;

    const INIT: Self =
        Self { read: super::RawMutex::INIT, write: super::RawMutex::INIT, readers: Cell::new(0) };

    #[inline]
    fn lock_exclusive(&self) {
        self.write.lock()
    }

    #[inline]
    fn try_lock_exclusive(&self) -> bool {
        self.write.try_lock()
    }

    #[inline]
    unsafe fn unlock_exclusive(&self) {
        self.write.unlock()
    }

    #[inline]
    fn lock_shared(&self) {
        self.read.lock();
        let readers = self.readers.get();
        if readers == 0 {
            self.write.lock();
        }
        self.readers.set(readers + 1);
        unsafe { self.read.unlock() };
    }

    #[inline]
    fn try_lock_shared(&self) -> bool {
        if !self.read.try_lock() {
            return false;
        }
        self.read.lock();
        let readers = self.readers.get();
        if readers == 0 {
            if !self.write.try_lock() {
                return false;
            }
        }
        self.readers.set(readers + 1);
        unsafe { self.read.unlock() };
        true
    }

    #[inline]
    unsafe fn unlock_shared(&self) {
        self.read.lock();
        let readers = self.readers.get() - 1;
        self.readers.set(readers);
        if readers == 0 {
            self.write.unlock();
        }
        self.read.unlock();
    }

    #[inline]
    fn is_locked(&self) -> bool {
        self.write.is_locked()
    }
}

pub type RwLock<T> = lock_api::RwLock<RawRwLock, T>;

pub type RwLockReadGuard<'a, T> = lock_api::RwLockReadGuard<'a, RawRwLock, T>;

pub type RwLockWriteGuard<'a, T> = lock_api::RwLockWriteGuard<'a, RawRwLock, T>;

#[test]
fn test_size() {
    assert_eq!(std::mem::size_of::<RawRwLock>(), 2 * std::mem::size_of::<usize>());
}

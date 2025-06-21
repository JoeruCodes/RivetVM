use std::cell::UnsafeCell;
use std::mem::MaybeUninit;
use std::ops::Deref;

pub struct RoCell<T>(UnsafeCell<MaybeUninit<T>>);

unsafe impl<T: Sync> Sync for RoCell<T> {}

impl<T> Drop for RoCell<T> {
    #[inline]
    fn drop(&mut self) {
        unsafe { std::mem::replace(&mut *(self.0.get()), MaybeUninit::uninit()).assume_init() };
    }
}

impl<T> RoCell<T> {
    #[inline]
    pub const fn new(value: T) -> Self {
        RoCell(UnsafeCell::new(MaybeUninit::new(value)))
    }

    #[inline]
    pub const unsafe fn new_uninit() -> Self {
        RoCell(UnsafeCell::new(MaybeUninit::uninit()))
    }

    #[inline]
    pub unsafe fn init(this: &Self, value: T) {
        std::ptr::write((*this.0.get()).as_mut_ptr(), value);
    }

    #[inline]
    pub unsafe fn replace(this: &Self, value: T) -> T {
        std::mem::replace(RoCell::as_mut(this), value)
    }

    #[inline]
    pub unsafe fn as_mut(this: &Self) -> &mut T {
        &mut *(*this.0.get()).as_mut_ptr()
    }
}

impl<T> Deref for RoCell<T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &T {
        unsafe { &*(*self.0.get()).as_ptr() }
    }
}

impl<T: std::fmt::Debug> std::fmt::Debug for RoCell<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        std::fmt::Debug::fmt(self.deref(), f)
    }
}

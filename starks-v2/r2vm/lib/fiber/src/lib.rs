#[macro_use]
extern crate memoffset;

use parking_lot::{Condvar as PCondvar, Mutex as PMutex};
use std::any::Any;
use std::cell::Cell;
use std::sync::atomic::{AtomicBool, Ordering};

mod map;
mod mutex;
mod park;
pub mod raw;
mod rwlock;

pub use mutex::{Condvar, Mutex, MutexGuard, RawMutex};
pub use rwlock::{RawRwLock, RwLock, RwLockReadGuard, RwLockWriteGuard};

extern "C" {
    fn fiber_start(cell: FiberStack) -> FiberStack;
    fn fiber_current() -> FiberStack;
}

thread_local! {
    static IN_FIBER: Cell<bool> = Cell::new(false);
}

#[inline]
pub fn in_fiber() -> bool {
    IN_FIBER.with(|x| x.get())
}

#[inline]
fn assert_in_fiber() {
    assert!(in_fiber(), "not in fiber");
}

#[inline]
pub fn sleep(num: usize) {
    if num > 0 {
        assert_in_fiber();
        unsafe { raw::fiber_sleep(num - 1) }
    }
}

fn get_vtable_from_any(ptr: *const dyn Any) -> *const () {
    unsafe { std::mem::transmute::<_, (*const (), *const ())>(ptr).1 }
}

#[inline]
fn construct_ptr_from_vtable(ptr: *const (), vtable: *const ()) -> *const dyn Any {
    unsafe { std::mem::transmute((ptr, vtable)) }
}

#[repr(transparent)]
#[derive(Clone, Copy, PartialEq, Eq)]
struct FiberStack(std::num::NonZeroUsize);

#[repr(C)]
struct FiberData {
    group: *const FiberGroupData,
    prev: FiberStack,
    next: FiberStack,
    paused: AtomicBool,
    vtable: *const (),
    cycles_to_sleep: usize,
    next_avail: std::sync::atomic::AtomicUsize,
    stack_pointer: usize,
}

impl FiberStack {
    fn allocate() -> Self {
        assert_eq!(std::mem::size_of::<FiberData>(), 64);
        assert_eq!(offset_of!(FiberData, next), 16);
        assert_eq!(offset_of!(FiberData, cycles_to_sleep), 40);
        assert_eq!(offset_of!(FiberData, next_avail), 48);
        assert_eq!(offset_of!(FiberData, stack_pointer), 56);

        let map = unsafe { libc::memalign(0x200000, 0x200000) };
        if map.is_null() {
            panic!("cannot create fiber stack");
        }
        FiberStack(
            std::num::NonZeroUsize::new(map as usize + std::mem::size_of::<FiberData>()).unwrap(),
        )
    }

    unsafe fn deallocate(self) {
        libc::free((self.0.get() - std::mem::size_of::<FiberData>()) as _)
    }

    unsafe fn data(self) -> &'static mut FiberData {
        &mut *((self.0.get() - std::mem::size_of::<FiberData>()) as *mut FiberData)
    }

    fn init(self) {
        unsafe {
            let data = self.data();
            data.stack_pointer = self.0.get() - std::mem::size_of::<FiberData>() + 0x200000 - 32;
            data.next = self;
            data.prev = self;
            data.next_avail.store(self.0.get(), Ordering::Relaxed);
            data.paused = AtomicBool::new(false);
            data.cycles_to_sleep = 0;
        }
    }

    fn data_pointer(self) -> usize {
        self.0.get()
    }

    fn set_fn(&self, f: fn()) {
        unsafe { *((self.data_pointer() - 64 + 0x200000 - 32) as *mut usize) = f as usize };
    }

    #[inline]
    fn data_ptr_any(self) -> *const dyn Any {
        unsafe { construct_ptr_from_vtable(self.0.get() as *const (), self.data().vtable) }
    }
}

pub struct FiberContext(FiberStack);

impl FiberContext {
    pub fn new<T: Any + Send>(data: T) -> Self {
        let ret = Self(FiberStack::allocate());
        unsafe {
            ret.0.data().vtable = get_vtable_from_any(&data);
            std::ptr::write(ret.0.data_pointer() as _, data);
        }
        ret
    }

    pub unsafe fn data_ptr<T: Any + Send>(&self) -> *const T {
        self.0.data_pointer() as _
    }

    pub fn any_data(&self) -> &dyn Any {
        unsafe { &*self.0.data_ptr_any() }
    }

    #[inline]
    pub fn try_data<T: Any + Send>(&self) -> Option<&T> {
        self.any_data().downcast_ref()
    }

    #[inline]
    pub fn data<T: Any + Send>(&self) -> &T {
        self.try_data().unwrap()
    }
}

impl Drop for FiberContext {
    fn drop(&mut self) {
        unsafe {
            std::ptr::drop_in_place(self.0.data_ptr_any() as *mut dyn Any);
            self.0.deallocate();
        }
    }
}

#[inline]
pub fn with_any_context<R>(callback: impl FnOnce(&dyn Any) -> R) -> R {
    assert_in_fiber();
    let ptr = unsafe { &*fiber_current().data_ptr_any() };
    callback(ptr)
}

#[inline]
pub fn try_with_context<T: Any + Send, R>(callback: impl FnOnce(&T) -> R) -> Option<R> {
    with_any_context(|any| any.downcast_ref().map(callback))
}

#[inline]
pub fn with_context<T: Any + Send, R>(callback: impl FnOnce(&T) -> R) -> R {
    with_any_context(|any| callback(any.downcast_ref().unwrap()))
}

struct FiberGroupData {
    first: Option<FiberStack>,
    last: Option<FiberStack>,
    mutex: PMutex<()>,
    condvar: PCondvar,
}

pub struct FiberGroup<'a>(Box<FiberGroupData>, std::marker::PhantomData<&'a mut FiberContext>);

impl<'a> FiberGroup<'a> {
    fn new() -> Self {
        FiberGroup(
            Box::new(FiberGroupData {
                first: None,
                last: None,
                mutex: PMutex::new(()),
                condvar: PCondvar::new(),
            }),
            std::marker::PhantomData,
        )
    }

    fn spawn_fn(&mut self, fiber: &'a mut FiberContext, f: Box<dyn FnOnce() + 'a>) {
        fiber.0.init();

        let ptr = (fiber.0).0.get() - std::mem::size_of::<FiberData>() + 0x200000 - 8;
        unsafe { std::ptr::write(ptr as *mut _, Box::new(f)) };

        fiber.0.set_fn(|| {
            let ptr = unsafe { fiber_current() }.0.get() - std::mem::size_of::<FiberData>()
                + 0x200000
                - 8;
            let box_fn: Box<Box<dyn FnOnce() + 'a>> = unsafe { std::ptr::read(ptr as *mut _) };
            box_fn();
        });

        let inner = &mut *self.0;

        let fiber_data = unsafe { fiber.0.data() };
        fiber_data.group = inner;

        if inner.first.is_none() {
            inner.first = Some(fiber.0);
            inner.last = Some(fiber.0);
        } else {
            let last = inner.last.unwrap();

            unsafe {
                let last_data = last.data();
                let next = last_data.next;
                let next_data = next.data();
                let next_avail = last_data.next_avail.load(Ordering::Relaxed);
                next_data.prev = fiber.0;
                fiber_data.next = next;
                fiber_data.next_avail.store(next_avail, Ordering::Relaxed);
                last_data.next = fiber.0;

                last_data.next_avail.store((fiber.0).0.get(), Ordering::Relaxed);
                fiber_data.prev = last;
            }

            inner.last = Some(fiber.0);
        }
    }

    pub fn spawn(&mut self, fiber: &'a mut FiberContext, f: impl FnOnce() + 'a) {
        self.spawn_fn(fiber, Box::new(f));
    }

    unsafe fn prepare_pause(stack: FiberStack) {
        stack.data().paused.store(true, Ordering::Relaxed);
    }

    unsafe fn pause(stack: FiberStack) -> bool {
        let group = &*stack.data().group;

        let mut guard = group.mutex.lock();

        if !stack.data().paused.load(Ordering::Relaxed) {
            return true;
        }

        while stack.data().next_avail.load(Ordering::Relaxed) == stack.0.get() {
            group.condvar.wait(&mut guard);

            if !stack.data().paused.load(Ordering::Relaxed) {
                return true;
            }
        }

        let mut prev = stack.data().prev;
        loop {
            let prev_data = prev.data();

            prev_data
                .next_avail
                .store(stack.data().next_avail.load(Ordering::Relaxed), Ordering::Relaxed);
            if !prev_data.paused.load(Ordering::Relaxed) {
                break;
            }
            prev = prev_data.prev;
        }

        false
    }

    unsafe fn unpause(stack: FiberStack) {
        let fiber = stack.data();
        let group = &*fiber.group;

        let mut _guard = group.mutex.lock();

        fiber.paused.store(false, Ordering::Relaxed);
        let mut prev = fiber.prev;
        loop {
            let prev_data = prev.data();

            prev_data.next_avail.store(stack.0.get(), Ordering::Relaxed);
            if !prev_data.paused.load(Ordering::Relaxed) {
                break;
            }
            prev = prev_data.prev;
        }

        group.condvar.notify_all();
    }

    fn run(&mut self) {
        IN_FIBER.with(|x| {
            assert!(!x.get(), "FiberGroup re-entry");
            x.set(true)
        });
        let inner = &mut self.0;
        loop {
            let stack = unsafe { fiber_start(inner.first.unwrap()) };
            let next = unsafe { stack.data().next };
            if stack == next {
                inner.first = None;
                inner.last = None;
                IN_FIBER.with(|x| x.set(false));
                return;
            }
            unsafe {
                Self::prepare_pause(stack);
                Self::pause(stack);

                let mut _guard = inner.mutex.lock();

                let prev = stack.data().prev;
                if stack == inner.first.unwrap() {
                    inner.first = Some(next);
                }
                if stack == inner.last.unwrap() {
                    inner.last = Some(prev);
                }
                prev.data().next = next;
                next.data().prev = prev;
            }
        }
    }

    pub fn with(closure: impl FnOnce(&mut Self)) {
        let mut group = FiberGroup::new();
        {
            let borrow = &mut group;
            closure(borrow);
        }
        group.run();
    }
}

#[doc(hidden)]
impl<'a> Drop for FiberGroup<'a> {
    fn drop(&mut self) {
        assert!(self.0.first.is_none(), "fiber group cannot be dropped without running");
    }
}

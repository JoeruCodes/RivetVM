extern "C" {

    pub fn fiber_save_raw();

    pub fn fiber_restore_ret_raw();

    pub fn fiber_sleep_raw();

    pub fn fiber_yield_raw();

    pub fn fiber_sleep(num: usize);

    pub fn fiber_current() -> std::num::NonZeroUsize;
}

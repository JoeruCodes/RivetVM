pub use fifo::Fifo;
pub use random::Random;

pub trait ReplacementPolicy {
    fn new(assoc: usize) -> Self
    where
        Self: Sized;

    fn insert(&mut self, index: usize);

    fn invalidate(&mut self, index: usize);

    fn touch(&mut self, index: usize);

    fn select(&mut self) -> usize;

    fn indexes_to_capture(&mut self) -> Vec<usize> {
        Vec::new()
    }
}

mod random {

    use super::ReplacementPolicy;
    use rand::{RngCore, SeedableRng};
    use rand_chacha::ChaCha8Rng as Rng;

    pub struct Random {
        valid: Box<[bool]>,
        rng: Rng,
    }

    impl ReplacementPolicy for Random {
        fn new(assoc: usize) -> Self {
            Self {
                valid: vec![false; assoc].into_boxed_slice(),
                rng: SeedableRng::seed_from_u64(0),
            }
        }

        fn insert(&mut self, index: usize) {
            self.valid[index] = true;
        }

        fn invalidate(&mut self, index: usize) {
            self.valid[index] = false;
        }

        fn touch(&mut self, _index: usize) {}

        fn select(&mut self) -> usize {
            for i in 0..self.valid.len() {
                if !self.valid[i] {
                    return i;
                }
            }
            self.rng.next_u32() as usize % self.valid.len()
        }
    }
}

mod fifo {

    use super::ReplacementPolicy;

    pub struct Fifo {
        valid: Box<[bool]>,
        ptr: usize,
    }

    impl ReplacementPolicy for Fifo {
        fn new(assoc: usize) -> Self {
            Self { valid: vec![false; assoc].into_boxed_slice(), ptr: 0 }
        }

        fn insert(&mut self, index: usize) {
            if self.ptr == index {
                self.ptr = if self.ptr == self.valid.len() - 1 { 0 } else { self.ptr + 1 }
            }
            self.valid[index] = true;
        }

        fn invalidate(&mut self, index: usize) {
            self.valid[index] = false;
        }

        fn touch(&mut self, _index: usize) {}

        fn select(&mut self) -> usize {
            for i in 0..self.valid.len() {
                if !self.valid[i] {
                    return i;
                }
            }
            self.ptr
        }
    }
}

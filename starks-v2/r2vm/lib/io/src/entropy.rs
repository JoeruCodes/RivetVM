pub use rand;

#[doc(no_inline)]
pub use rand::RngCore as Entropy;
#[doc(no_inline)]
pub use rand::rngs::OsRng as Os;
#[doc(no_inline)]
pub use rand_chacha::ChaCha8Rng as Seeded;

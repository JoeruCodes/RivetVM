#![no_std]

extern crate alloc;

mod decode;
mod disasm;
mod encode;
mod op;

pub use decode::{Decoder, decode};
pub use encode::{Encoder, encode};
pub use op::{ConditionCode, Location, Memory, Op, Operand, Register, Size};

pub mod builder {
    pub use super::Location::*;
    pub use super::Operand::{Imm, Mem as OpMem, Reg as OpReg};
}

#[cfg(feature = "block-file")]
mod file;
#[cfg(feature = "block-file")]
pub use file::File;
#[cfg(feature = "block-shadow")]
mod shadow;
#[cfg(feature = "block-shadow")]
pub use shadow::Shadow;

use std::io::Result;

#[non_exhaustive]
pub struct Capability {
    pub blksize: usize,

    pub discard: bool,
}

impl Default for Capability {
    fn default() -> Self {
        Capability { blksize: 512, discard: false }
    }
}

pub trait Block {
    fn read_exact_at(&self, buf: &mut [u8], offset: u64) -> Result<()>;

    fn write_all_at(&self, buf: &[u8], offset: u64) -> Result<()>;

    fn write_zero_at(&self, offset: u64, len: usize) -> Result<()> {
        let buf = vec![0; len];
        self.write_all_at(&buf, offset)
    }

    fn discard(&self, offset: u64, len: usize) -> Result<()> {
        let _ = (offset, len);
        Ok(())
    }

    fn flush(&self) -> Result<()> {
        Ok(())
    }

    fn len(&self) -> u64;

    fn capability(&self) -> Capability {
        Default::default()
    }
}

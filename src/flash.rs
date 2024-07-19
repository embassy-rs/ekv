//! Flash storage trait.
//!
//! You must implement this trait for your flash storage to use it with `ekv`.

use core::fmt::Debug;

#[cfg(feature = "std")]
use crate::config::*;
pub use crate::types::PageID;

// TODO: use embedded-storage instead
// or make an adapter instead?

/// Flash storage trait
pub trait Flash {
    /// Error type for the flash operations.
    type Error: Debug;

    /// Get the page count of the flash storage.
    ///
    /// The [`PageID`](crate::types::PageID) is backed by a `u16` so the maximum page count is 65535.
    fn page_count(&self) -> usize;

    /// Erase a page.
    ///
    /// If power is lost during an erase, the resulting data is allowed to be
    /// anything, but data on other pages must stay unaffected.
    ///
    /// After erasing, all bytes in the page must be equal to [`ERASE_VALUE`](crate::config::ERASE_VALUE).
    async fn erase(&mut self, page_id: PageID) -> Result<(), Self::Error>;

    /// Read data.
    ///
    /// `offset` and `data.len()` are guaranteed to be a multiple of [`ALIGN`](crate::config::ALIGN).
    async fn read(&mut self, page_id: PageID, offset: usize, data: &mut [u8]) -> Result<(), Self::Error>;

    /// Write data.
    ///
    /// If power is lost during a write, the resulting data in the written bytes
    /// is allowed to be anything, but data on other bytes within the page must
    /// stay unaffected. This means it is NOT okay to implement this with underlying
    /// "read-erase-modify-write" strategies.
    ///
    /// `offset` and `data.len()` are guaranteed to be a multiple of [`ALIGN`](crate::config::ALIGN).
    ///
    /// It is guaranteed that each byte will be written only once after each erase.
    /// This ensures maximum compatibility with different flash hardware, in particular
    /// flash memory with ECC.
    async fn write(&mut self, page_id: PageID, offset: usize, data: &[u8]) -> Result<(), Self::Error>;
}

impl<T: Flash> Flash for &mut T {
    type Error = T::Error;
    fn page_count(&self) -> usize {
        T::page_count(self)
    }
    async fn erase(&mut self, page_id: PageID) -> Result<(), Self::Error> {
        T::erase(self, page_id).await
    }
    async fn read(&mut self, page_id: PageID, offset: usize, data: &mut [u8]) -> Result<(), Self::Error> {
        T::read(self, page_id, offset, data).await
    }
    async fn write(&mut self, page_id: PageID, offset: usize, data: &[u8]) -> Result<(), Self::Error> {
        T::write(self, page_id, offset, data).await
    }
}

/// Fake in-memory flash
#[cfg(feature = "std")]
pub struct MemFlash {
    /// Data. Length must equal `PAGE_SIZE * MAX_PAGE_COUNT`
    pub data: Vec<u8>,
    /// Count of read operations.
    pub read_count: usize,
    /// Count of read bytes (sum of all operations)
    pub read_bytes: usize,
    /// Count of write operations.
    pub write_count: usize,
    /// Count of written bytes (sum of all operations)
    pub write_bytes: usize,
    /// Count of erase operations.
    pub erase_count: usize,
    /// Count of erased bytes (sum of all operations)
    pub erase_bytes: usize,
}

#[cfg(feature = "std")]
impl MemFlash {
    /// Create a new MemFlash
    pub fn new() -> Self {
        Self {
            data: vec![ERASE_VALUE; PAGE_SIZE * MAX_PAGE_COUNT],
            read_count: 0,
            read_bytes: 0,
            write_count: 0,
            write_bytes: 0,
            erase_count: 0,
            erase_bytes: 0,
        }
    }

    /// Reset statistics counters.
    pub fn reset_counters(&mut self) {
        self.read_count = 0;
        self.read_bytes = 0;
        self.write_count = 0;
        self.write_bytes = 0;
        self.erase_count = 0;
        self.erase_bytes = 0;
    }
}

#[cfg(feature = "std")]
impl Flash for MemFlash {
    type Error = core::convert::Infallible;

    fn page_count(&self) -> usize {
        MAX_PAGE_COUNT
    }

    async fn erase(&mut self, page_id: PageID) -> Result<(), Self::Error> {
        let page_id = page_id.index();

        assert!(page_id < self.page_count());
        self.data[page_id * PAGE_SIZE..][..PAGE_SIZE].fill(ERASE_VALUE);
        self.erase_count += 1;
        self.erase_bytes += PAGE_SIZE;

        Ok(())
    }

    async fn read(&mut self, page_id: PageID, offset: usize, data: &mut [u8]) -> Result<(), Self::Error> {
        let page_id = page_id.index();

        assert!(page_id < self.page_count());
        assert!(offset <= PAGE_SIZE);
        assert!(offset + data.len() <= PAGE_SIZE);
        assert!(offset % ALIGN == 0);
        assert!(data.len() % ALIGN == 0);

        let mem = &self.data[page_id * PAGE_SIZE + offset..][..data.len()];
        data.copy_from_slice(mem);
        self.read_count += 1;
        self.read_bytes += data.len();

        Ok(())
    }

    async fn write(&mut self, page_id: PageID, offset: usize, data: &[u8]) -> Result<(), Self::Error> {
        let page_id = page_id.index();

        assert!(page_id < self.page_count());
        assert!(offset <= PAGE_SIZE);
        assert!(offset + data.len() <= PAGE_SIZE);
        assert!(offset % ALIGN == 0);
        assert!(data.len() % ALIGN == 0);

        let mem = &mut self.data[page_id * PAGE_SIZE + offset..][..data.len()];
        assert!(mem.iter().all(|x| *x == ERASE_VALUE));
        mem.copy_from_slice(data);
        self.write_count += 1;
        self.write_bytes += data.len();

        Ok(())
    }
}

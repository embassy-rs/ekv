// Flash parameters -- TODO unhardcode
pub const WRITE_SIZE: usize = 4;
pub const PAGE_SIZE: usize = 4096;
pub const PAGE_COUNT: usize = 256;
pub const ERASE_VALUE: u8 = 0xFF;

/// NOR flash memory trait
/// TODO use embedded-storage
pub trait Flash {
    fn erase(&mut self, page_id: usize);
    fn read(&mut self, page_id: usize, offset: usize, data: &mut [u8]);
    fn write(&mut self, page_id: usize, offset: usize, data: &[u8]);
}

/// Fake in-memory flash
pub struct MemFlash {
    data: Vec<u8>,
}

impl MemFlash {
    pub fn new() -> Self {
        Self {
            data: vec![ERASE_VALUE; PAGE_SIZE * PAGE_COUNT],
        }
    }
}

impl Flash for MemFlash {
    fn erase(&mut self, page_id: usize) {
        assert!(page_id < PAGE_COUNT);
        self.data[page_id * PAGE_SIZE..][..PAGE_SIZE].fill(ERASE_VALUE);
    }

    fn read(&mut self, page_id: usize, offset: usize, data: &mut [u8]) {
        assert!(page_id < PAGE_COUNT);
        assert!(offset <= PAGE_SIZE);
        assert!(offset + data.len() <= PAGE_SIZE);

        let mem = &self.data[page_id * PAGE_SIZE + offset..][..data.len()];
        data.copy_from_slice(mem);
    }

    fn write(&mut self, page_id: usize, offset: usize, data: &[u8]) {
        assert!(page_id < PAGE_COUNT);
        assert!(offset <= PAGE_SIZE);
        assert!(offset + data.len() <= PAGE_SIZE);

        let mem = &mut self.data[page_id * PAGE_SIZE + offset..][..data.len()];
        assert!(mem.iter().all(|x| *x == ERASE_VALUE));
        mem.copy_from_slice(data);
    }
}

impl<T: Flash> Flash for &mut T {
    fn erase(&mut self, page_id: usize) {
        T::erase(self, page_id)
    }
    fn read(&mut self, page_id: usize, offset: usize, data: &mut [u8]) {
        T::read(self, page_id, offset, data)
    }
    fn write(&mut self, page_id: usize, offset: usize, data: &[u8]) {
        T::write(self, page_id, offset, data)
    }
}

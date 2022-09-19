use std::marker::PhantomData;

use crate::config::*;
use crate::file::Header;
use crate::flash::Flash;

const PAGE_HEADER_MAGIC: u32 = 0xc4e21c75;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[repr(C)]
pub struct PageHeader {
    magic: u32,
    len: u32,

    // Higher layer data
    file_header: Header,
}
impl_bytes!(PageHeader);

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ReadError {
    Eof,
}

pub struct PageManager<F: Flash> {
    _phantom: PhantomData<F>,
}

impl<F: Flash> PageManager<F> {
    pub fn new() -> Self {
        Self { _phantom: PhantomData }
    }

    fn write_page_header(flash: &mut F, page_id: PageID, h: PageHeader) {
        let buf = h.to_bytes();
        flash.write(page_id as _, 0, &buf);
    }

    fn read_page_header(flash: &mut F, page_id: PageID) -> Result<PageHeader, ReadError> {
        let mut buf = [0u8; PageHeader::SIZE];
        flash.read(page_id as _, 0, &mut buf);
        let h = PageHeader::from_bytes(buf);
        if h.magic != PAGE_HEADER_MAGIC {
            return Err(ReadError::Eof);
        }

        Ok(h)
    }

    pub fn read_header(&mut self, flash: &mut F, page_id: PageID) -> Result<Header, ReadError> {
        let h = Self::read_page_header(flash, page_id)?;
        Ok(h.file_header)
    }

    pub fn read(&mut self, flash: &mut F, page_id: PageID) -> Result<(Header, PageReader<F>), ReadError> {
        let header = Self::read_page_header(flash, page_id)?;
        Ok((
            header.file_header,
            PageReader {
                _phantom: PhantomData,
                page_id,
                len: header.len as _,
                offset: 0,
            },
        ))
    }

    pub fn write(&mut self, _flash: &mut F, page_id: PageID) -> PageWriter<F> {
        PageWriter {
            _phantom: PhantomData,
            page_id,
            offset: 0,
        }
    }
}

pub struct PageReader<F: Flash> {
    _phantom: PhantomData<F>,
    page_id: PageID,
    offset: usize,
    len: usize,
}

impl<F: Flash> PageReader<F> {
    pub fn page_id(&self) -> PageID {
        self.page_id
    }

    pub fn seek(&mut self, offset: usize) {
        assert!(offset <= self.len);
        self.offset = offset;
    }

    pub fn read(&mut self, flash: &mut F, data: &mut [u8]) -> usize {
        let n = data.len().min(self.len - self.offset);
        let offset = PageHeader::SIZE + self.offset;
        flash.read(self.page_id as _, offset, &mut data[..n]);
        self.offset += n;
        n
    }

    pub fn skip(&mut self, len: usize) -> usize {
        let n = len.min(self.len - self.offset);
        self.offset += n;
        n
    }
}

pub struct PageWriter<F: Flash> {
    _phantom: PhantomData<F>,
    page_id: PageID,
    offset: usize,
}

impl<F: Flash> PageWriter<F> {
    pub fn page_id(&self) -> PageID {
        self.page_id
    }

    pub fn write(&mut self, flash: &mut F, data: &[u8]) -> usize {
        let n = data.len().min(PAGE_MAX_PAYLOAD_SIZE - self.offset);
        let offset = PageHeader::SIZE + self.offset;
        flash.write(self.page_id as _, offset, &data[..n]);
        self.offset += n;
        n
    }

    pub fn commit(self, flash: &mut F, header: Header) {
        PageManager::write_page_header(
            flash,
            self.page_id,
            PageHeader {
                magic: PAGE_HEADER_MAGIC,
                len: self.offset as _,
                file_header: header,
            },
        );
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::flash::MemFlash;

    #[test]
    fn test_header() {
        let f = &mut MemFlash::new();

        let h = PageHeader {
            magic: PAGE_HEADER_MAGIC,
            len: 1234,
            file_header: Header::DUMMY,
        };
        PageManager::write_page_header(f, 0, h);
        let h2 = PageManager::read_page_header(f, 0).unwrap();
        assert_eq!(h, h2)
    }

    #[test]
    fn test_header_read_unwritten() {
        let f = &mut MemFlash::new();

        let res = PageManager::read_page_header(f, 0);
        assert!(matches!(res, Err(ReadError::Eof)))
    }

    #[test]
    fn test_read_unwritten() {
        let f = &mut MemFlash::new();
        let mut b = PageManager::new();

        // Read
        let res = b.read(f, 0);
        assert!(matches!(res, Err(ReadError::Eof)));
    }

    #[test]
    fn test_read_uncommitted() {
        let f = &mut MemFlash::new();
        let mut b = PageManager::new();

        let data = dummy_data(13);

        // Write
        let mut w = b.write(f, 0);
        w.write(f, &data);
        drop(w); // don't commit

        // Read
        let res = b.read(f, 0);
        assert!(matches!(res, Err(ReadError::Eof)));
    }

    #[test]
    fn test_write_short() {
        let f = &mut MemFlash::new();
        let mut b = PageManager::new();

        let data = dummy_data(13);

        // Write
        let mut w = b.write(f, 0);
        let n = w.write(f, &data);
        assert_eq!(n, 13);
        w.commit(f, Header::DUMMY);

        // Read
        let (h, mut r) = b.read(f, 0).unwrap();
        assert_eq!(h, Header::DUMMY);
        let mut buf = vec![0; data.len()];
        let n = r.read(f, &mut buf);
        assert_eq!(n, 13);
        assert_eq!(data, buf);

        // Remount
        let mut b = PageManager::new();

        // Read
        let (h, mut r) = b.read(f, 0).unwrap();
        assert_eq!(h, Header::DUMMY);
        let mut buf = vec![0; data.len()];
        let n = r.read(f, &mut buf);
        assert_eq!(n, 13);
        assert_eq!(data, buf);
    }

    #[test]
    fn test_overread() {
        let f = &mut MemFlash::new();
        let mut b = PageManager::new();

        let data = dummy_data(13);

        // Write
        let mut w = b.write(f, 0);
        w.write(f, &data);
        w.commit(f, Header::DUMMY);

        // Read
        let (h, mut r) = b.read(f, 0).unwrap();
        assert_eq!(h, Header::DUMMY);
        let mut buf = vec![0; 1024];
        let n = r.read(f, &mut buf);
        assert_eq!(n, 13);
        assert_eq!(data, buf[..13]);
    }

    #[test]
    fn test_overwrite() {
        let f = &mut MemFlash::new();
        let mut b = PageManager::new();

        let data = dummy_data(65536);

        // Write
        let mut w = b.write(f, 0);
        let n = w.write(f, &data);
        assert_eq!(n, PAGE_MAX_PAYLOAD_SIZE);
        w.commit(f, Header::DUMMY);

        // Read
        let (h, mut r) = b.read(f, 0).unwrap();
        assert_eq!(h, Header::DUMMY);
        let mut buf = vec![0; PAGE_MAX_PAYLOAD_SIZE];
        let n = r.read(f, &mut buf);
        assert_eq!(n, PAGE_MAX_PAYLOAD_SIZE);
        assert_eq!(data[..13], buf[..13]);
    }

    #[test]
    fn test_write_many() {
        let f = &mut MemFlash::new();
        let mut b = PageManager::new();

        // Write
        let mut w = b.write(f, 0);
        let n = w.write(f, &[1, 2, 3]);
        assert_eq!(n, 3);
        let n = w.write(f, &[4, 5, 6, 7, 8, 9]);
        assert_eq!(n, 6);
        w.commit(f, Header::DUMMY);

        // Read
        let (h, mut r) = b.read(f, 0).unwrap();
        assert_eq!(h, Header::DUMMY);
        let mut buf = vec![0; PAGE_MAX_PAYLOAD_SIZE];
        let n = r.read(f, &mut buf);
        assert_eq!(n, 9);
        assert_eq!(buf[..9], [1, 2, 3, 4, 5, 6, 7, 8, 9]);
    }

    #[test]
    fn test_read_many() {
        let f = &mut MemFlash::new();
        let mut b = PageManager::new();

        // Write
        let mut w = b.write(f, 0);
        let n = w.write(f, &[1, 2, 3, 4, 5, 6, 7, 8, 9]);
        assert_eq!(n, 9);
        w.commit(f, Header::DUMMY);

        // Read
        let (h, mut r) = b.read(f, 0).unwrap();
        assert_eq!(h, Header::DUMMY);
        let mut buf = vec![0; PAGE_MAX_PAYLOAD_SIZE];

        let n = r.read(f, &mut buf[..3]);
        assert_eq!(n, 3);
        assert_eq!(buf[..3], [1, 2, 3]);

        let n = r.read(f, &mut buf);
        assert_eq!(n, 6);
        assert_eq!(buf[..6], [4, 5, 6, 7, 8, 9]);
    }

    fn dummy_data(len: usize) -> Vec<u8> {
        let mut res = vec![0; len];
        for (i, v) in res.iter_mut().enumerate() {
            *v = i as u8 ^ (i >> 8) as u8 ^ (i >> 16) as u8 ^ (i >> 24) as u8;
        }
        res
    }
}

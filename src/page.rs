use crate::flash::*;

pub type PageID = u16;

const PAGE_HEADER_MAGIC: u32 = 0xc4e21c75;
const MAX_PAYLOAD_SIZE: usize = PAGE_SIZE - PageHeader::SIZE;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[repr(C)]
pub struct PageHeader {
    magic: u32,
    len: u32,

    // Higher layer data
    file_header: FilePageHeader,
}
impl_bytes!(PageHeader);

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[repr(C)]
pub struct FilePageHeader {
    // TODO
}

impl FilePageHeader {
    #[cfg(test)]
    pub const DUMMY: Self = Self {};
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ReadError {
    Eof,
}

pub struct PageManager<F: Flash> {
    flash: F,
}

impl<F: Flash> PageManager<F> {
    pub fn new(flash: F) -> Self {
        Self { flash }
    }

    fn write_header(&mut self, page_id: PageID, h: PageHeader) {
        let mut buf = h.to_bytes();
        self.flash.write(page_id as _, 0, &buf);
    }

    fn read_header(&mut self, page_id: PageID) -> Result<PageHeader, ReadError> {
        let mut buf = [0u8; PageHeader::SIZE];
        self.flash.read(page_id as _, 0, &mut buf);
        let h = PageHeader::from_bytes(buf);
        if h.magic != PAGE_HEADER_MAGIC {
            return Err(ReadError::Eof);
        }

        Ok(h)
    }

    fn read(&mut self, page_id: PageID) -> Result<(FilePageHeader, PageReader<'_, F>), ReadError> {
        let header = self.read_header(page_id)?;
        Ok((
            header.file_header,
            PageReader {
                backend: self,
                page_id,
                len: header.len as _,
                offset: 0,
            },
        ))
    }

    fn write(&mut self, page_id: PageID) -> PageWriter<'_, F> {
        PageWriter {
            backend: self,
            page_id,
            offset: 0,
        }
    }
}

pub struct PageReader<'a, F: Flash> {
    backend: &'a mut PageManager<F>,
    page_id: PageID,
    offset: usize,
    len: usize,
}

impl<'a, F: Flash> PageReader<'a, F> {
    fn seek(&mut self, offset: usize) {
        assert!(offset <= self.len);
        self.offset = offset;
    }

    fn read(&mut self, data: &mut [u8]) -> usize {
        let n = data.len().min(self.len - self.offset);
        let offset = PageHeader::SIZE + self.offset;
        self.backend.flash.read(self.page_id as _, offset, &mut data[..n]);
        self.offset += n;
        n
    }
}

pub struct PageWriter<'a, F: Flash> {
    backend: &'a mut PageManager<F>,
    page_id: PageID,
    offset: usize,
}

impl<'a, F: Flash> PageWriter<'a, F> {
    fn write(&mut self, data: &[u8]) -> usize {
        let n = data.len().min(MAX_PAYLOAD_SIZE - self.offset);
        let offset = PageHeader::SIZE + self.offset;
        self.backend.flash.write(self.page_id as _, offset, &data[..n]);
        self.offset += n;
        n
    }

    fn commit(mut self, header: FilePageHeader) {
        self.backend.write_header(
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

    #[test]
    fn test_rw_header() {
        let mut b = PageManager::new(MemFlash::new());
        let h = PageHeader {
            magic: PAGE_HEADER_MAGIC,
            len: 1234,
            file_header: FilePageHeader::DUMMY,
        };
        b.write_header(0, h);
        let h2 = b.read_header(0).unwrap();
        assert_eq!(h, h2)
    }

    #[test]
    fn test_read_unwritten() {
        let mut f = MemFlash::new();
        let mut b = PageManager::new(&mut f);

        // Read
        let res = b.read(0);
        assert!(matches!(res, Err(ReadError::Eof)));
    }

    #[test]
    fn test_read_uncommitted() {
        let mut f = MemFlash::new();
        let mut b = PageManager::new(&mut f);

        let data = dummy_data(13);

        // Write
        let mut w = b.write(0);
        w.write(&data);
        drop(w); // don't commit

        // Read
        let res = b.read(0);
        assert!(matches!(res, Err(ReadError::Eof)));
    }

    #[test]
    fn test_write_short() {
        let mut f = MemFlash::new();
        let mut b = PageManager::new(&mut f);

        let data = dummy_data(13);

        // Write
        let mut w = b.write(0);
        let n = w.write(&data);
        assert_eq!(n, 13);
        w.commit(FilePageHeader::DUMMY);

        // Read
        let (h, mut r) = b.read(0).unwrap();
        assert_eq!(h, FilePageHeader::DUMMY);
        let mut buf = vec![0; data.len()];
        let n = r.read(&mut buf);
        assert_eq!(n, 13);
        assert_eq!(data, buf);

        // Remount
        let mut b = PageManager::new(&mut f);

        // Read
        let (h, mut r) = b.read(0).unwrap();
        assert_eq!(h, FilePageHeader::DUMMY);
        let mut buf = vec![0; data.len()];
        let n = r.read(&mut buf);
        assert_eq!(n, 13);
        assert_eq!(data, buf);
    }

    #[test]
    fn test_overread() {
        let mut f = MemFlash::new();
        let mut b = PageManager::new(&mut f);

        let data = dummy_data(13);

        // Write
        let mut w = b.write(0);
        w.write(&data);
        w.commit(FilePageHeader::DUMMY);

        // Read
        let (h, mut r) = b.read(0).unwrap();
        assert_eq!(h, FilePageHeader::DUMMY);
        let mut buf = vec![0; 1024];
        let n = r.read(&mut buf);
        assert_eq!(n, 13);
        assert_eq!(data, buf[..13]);
    }

    #[test]
    fn test_overwrite() {
        let mut f = MemFlash::new();
        let mut b = PageManager::new(&mut f);

        let data = dummy_data(65536);

        // Write
        let mut w = b.write(0);
        let n = w.write(&data);
        assert_eq!(n, MAX_PAYLOAD_SIZE);
        w.commit(FilePageHeader::DUMMY);

        // Read
        let (h, mut r) = b.read(0).unwrap();
        assert_eq!(h, FilePageHeader::DUMMY);
        let mut buf = vec![0; MAX_PAYLOAD_SIZE];
        let n = r.read(&mut buf);
        assert_eq!(n, MAX_PAYLOAD_SIZE);
        assert_eq!(data[..13], buf[..13]);
    }

    #[test]
    fn test_write_many() {
        let mut f = MemFlash::new();
        let mut b = PageManager::new(&mut f);

        // Write
        let mut w = b.write(0);
        let n = w.write(&[1, 2, 3]);
        assert_eq!(n, 3);
        let n = w.write(&[4, 5, 6, 7, 8, 9]);
        assert_eq!(n, 6);
        w.commit(FilePageHeader::DUMMY);

        // Read
        let (h, mut r) = b.read(0).unwrap();
        assert_eq!(h, FilePageHeader::DUMMY);
        let mut buf = vec![0; MAX_PAYLOAD_SIZE];
        let n = r.read(&mut buf);
        assert_eq!(n, 9);
        assert_eq!(buf[..9], [1, 2, 3, 4, 5, 6, 7, 8, 9]);
    }

    #[test]
    fn test_read_many() {
        let mut f = MemFlash::new();
        let mut b = PageManager::new(&mut f);

        // Write
        let mut w = b.write(0);
        let n = w.write(&[1, 2, 3, 4, 5, 6, 7, 8, 9]);
        assert_eq!(n, 9);
        w.commit(FilePageHeader::DUMMY);

        // Read
        let (h, mut r) = b.read(0).unwrap();
        assert_eq!(h, FilePageHeader::DUMMY);
        let mut buf = vec![0; MAX_PAYLOAD_SIZE];

        let n = r.read(&mut buf[..3]);
        assert_eq!(n, 3);
        assert_eq!(buf[..3], [1, 2, 3]);

        let n = r.read(&mut buf);
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

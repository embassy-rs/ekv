use core::mem;
use std::cell::RefCell;

use crate::alloc::Allocator;
use crate::config::*;
use crate::flash::Flash;
use crate::page::{PageManager, PageReader, PageWriter, ReadError};

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum SeekDirection {
    Left,
    Right,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[repr(C)]
pub struct Header {
    seq: u32,
    previous_page_id: PageID, // TODO add a skiplist for previous pages, instead of just storing the immediately previous one.
}

impl Header {
    #[cfg(test)]
    pub const DUMMY: Self = Self {
        seq: 3,
        previous_page_id: 2,
    };
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[repr(C)]
pub struct FileMeta {
    file_id: FileID,
    last_page_id: PageID,
    first_seq: u32,
}
impl_bytes!(FileMeta);

struct FileState {
    last_page: Option<PagePointer>,
    first_seq: u32,
    last_seq: u32,
}

pub struct FileManager<F: Flash> {
    inner: RefCell<Inner<F>>,
}

struct Inner<F: Flash> {
    flash: F,
    pages: PageManager<F>,
    files: [FileState; FILE_COUNT],
    meta_page_id: PageID,
    meta_seq: u32,

    alloc: Allocator,
}

impl<F: Flash> FileManager<F> {
    pub fn format(flash: F) {
        let mut inner = Inner::new(flash);
        inner.format();
    }

    pub fn new(flash: F) -> Self {
        let mut inner = Inner::new(flash);
        inner.mount();

        Self {
            inner: RefCell::new(inner),
        }
    }

    pub fn commit(&self) {
        self.inner.borrow_mut().commit();
    }

    pub fn read(&self, file_id: FileID) -> FileReader<'_, F> {
        FileReader::new(self, file_id)
    }

    pub fn write(&self, file_id: FileID) -> FileWriter<'_, F> {
        FileWriter::new(self, file_id)
    }

    pub fn left_truncate(&self, file_id: FileID, seq: u32) {
        let m = &mut *self.inner.borrow_mut();
        let mut f = &mut m.files[file_id as usize];
        assert!(seq >= f.first_seq);
        assert!(seq <= f.last_seq);
        f.first_seq = seq;
    }
}

impl<F: Flash> Inner<F> {
    fn new(flash: F) -> Self {
        // TODO initialize self in mount() to avoid having to
        // use dummy values here.
        const DUMMY_FILE: FileState = FileState {
            last_page: None,
            first_seq: 0,
            last_seq: 0,
        };
        Self {
            flash,
            meta_page_id: 0,
            meta_seq: 0,
            pages: PageManager::new(),
            files: [DUMMY_FILE; FILE_COUNT],
            alloc: Allocator::new(),
        }
    }

    fn format(&mut self) {
        // Erase all meta pages.
        for page_id in 0..PAGE_COUNT {
            if let Ok(h) = self.read_header(page_id as _) {
                if h.previous_page_id == PageID::MAX - 1 {
                    self.flash.erase(page_id);
                }
            }
        }

        // Write initial meta page.
        let w = self.write_page(0);
        w.commit(
            &mut self.flash,
            Header {
                seq: 1,
                previous_page_id: PageID::MAX - 1,
            },
        );
    }

    fn mount(&mut self) {
        let mut meta_page_id = None;
        let mut meta_seq = 0;
        for page_id in 0..PAGE_COUNT {
            if let Ok(h) = self.read_header(page_id as _) {
                if h.previous_page_id == PageID::MAX - 1 && h.seq > meta_seq {
                    meta_page_id = Some(page_id as PageID);
                    meta_seq = h.seq;
                }
            }
        }

        let meta_page_id = meta_page_id.unwrap();
        self.meta_page_id = meta_page_id;
        self.meta_seq = meta_seq;
        self.alloc.mark_allocated(meta_page_id);

        #[derive(Clone, Copy)]
        struct FileInfo {
            last_page_id: PageID,
            first_seq: u32,
        }

        let (_, mut r) = self.read_page(meta_page_id).unwrap();
        let mut files = [FileInfo {
            last_page_id: PageID::MAX,
            first_seq: 0,
        }; FILE_COUNT];
        loop {
            let mut meta = [0; FileMeta::SIZE];
            let n = r.read(&mut self.flash, &mut meta);
            if n == 0 {
                break;
            }
            assert_eq!(n, FileMeta::SIZE);
            let meta = FileMeta::from_bytes(meta);
            assert!(meta.file_id < FILE_COUNT as _);
            assert!(meta.last_page_id < PAGE_COUNT as _ || meta.last_page_id == PageID::MAX);
            files[meta.file_id as usize] = FileInfo {
                last_page_id: meta.last_page_id,
                first_seq: meta.first_seq,
            }
        }

        for file_id in 0..FILE_COUNT as FileID {
            let fi = files[file_id as usize];
            if fi.last_page_id == PageID::MAX {
                continue;
            }

            let (h, mut r) = self.read_page(fi.last_page_id).unwrap();
            let page_len = r.skip(PAGE_SIZE);
            let last_seq = h.seq.checked_add(page_len.try_into().unwrap()).unwrap();

            let mut p = Some(PagePointer {
                page_id: fi.last_page_id,
                header: h,
            });

            self.files[file_id as usize] = FileState {
                last_page: p,
                first_seq: fi.first_seq,
                last_seq,
            };

            while let Some(pp) = p {
                self.alloc.mark_allocated(pp.page_id);
                p = pp.prev(self);
            }
        }
    }

    fn commit(&mut self) {
        let page_id = self.alloc.allocate();
        let mut w = self.write_page(page_id);
        for file_id in 0..FILE_COUNT as FileID {
            let f = &self.files[file_id as usize];
            if let Some(last) = f.last_page {
                let meta = FileMeta {
                    file_id,
                    first_seq: f.first_seq,
                    last_page_id: last.page_id,
                };
                let n = w.write(&mut self.flash, &meta.to_bytes());
                assert_eq!(n, FileMeta::SIZE);
            }
        }

        self.meta_seq = self.meta_seq.wrapping_add(1);
        w.commit(
            &mut self.flash,
            Header {
                seq: self.meta_seq,
                previous_page_id: PageID::MAX - 1,
            },
        );

        self.alloc.free(self.meta_page_id);
        self.meta_page_id = page_id;
    }

    fn get_file_page(&mut self, file_id: FileID, seq: u32) -> Option<PagePointer> {
        let f = &self.files[file_id as usize];
        let last = f.last_page?;
        if seq < f.first_seq || seq >= f.last_seq {
            None
        } else {
            last.prev_seq(self, seq)
        }
    }

    fn free_between(&mut self, mut from: Option<PagePointer>, to: Option<PagePointer>) {
        while let Some(pp) = from {
            if let Some(to) = to {
                if pp.page_id == to.page_id {
                    break;
                }
            }
            self.alloc.free(pp.page_id);
            from = pp.prev(self);
        }
    }

    fn read_page(&mut self, page_id: PageID) -> Result<(Header, PageReader<F>), ReadError> {
        self.pages.read(&mut self.flash, page_id)
    }

    fn read_header(&mut self, page_id: PageID) -> Result<Header, ReadError> {
        self.pages.read_header(&mut self.flash, page_id)
    }

    fn write_page(&mut self, page_id: PageID) -> PageWriter<F> {
        self.pages.write(&mut self.flash, page_id)
    }
}

/// "cursor" pointing to a page within a file.
#[derive(Clone, Copy, Debug)]
struct PagePointer {
    page_id: PageID,
    header: Header,
}

impl PagePointer {
    fn prev(self, m: &mut Inner<impl Flash>) -> Option<PagePointer> {
        let p2 = self.header.previous_page_id;
        if p2 == PageID::MAX {
            None
        } else {
            let h2 = m.read_header(p2).unwrap();
            assert!(h2.seq < self.header.seq);
            Some(PagePointer {
                page_id: p2,
                header: h2,
            })
        }
    }

    fn prev_seq(self, m: &mut Inner<impl Flash>, seq: u32) -> Option<PagePointer> {
        let mut p = self;
        while p.header.seq > seq {
            p = p.prev(m)?;
        }
        Some(p)
    }
}

pub struct FileReader<'a, F: Flash> {
    m: &'a FileManager<F>,
    file_id: FileID,

    state: ReaderState<F>,
}

enum ReaderState<F: Flash> {
    Created,
    Reading(ReaderStateReading<F>),
    Finished,
}
struct ReaderStateReading<F: Flash> {
    seq: u32,
    reader: PageReader<F>,
}

impl<'a, F: Flash> FileReader<'a, F> {
    fn new(m: &'a FileManager<F>, file_id: FileID) -> Self {
        Self {
            m,
            file_id,
            state: ReaderState::Created,
        }
    }

    pub fn binary_search_start(&mut self) {
        // TODO
    }

    pub fn binary_search_seek(&mut self, _direction: SeekDirection) -> bool {
        // TODO
        false
    }

    fn next_page(&mut self, m: &mut Inner<F>) {
        let seq = match &self.state {
            ReaderState::Created => m.files[self.file_id as usize].first_seq,
            ReaderState::Reading(s) => s.seq,
            ReaderState::Finished => unreachable!(),
        };
        self.state = match m.get_file_page(self.file_id, seq) {
            Some(pp) => {
                let (h, mut r) = m.read_page(pp.page_id).unwrap();
                r.seek((seq - h.seq) as usize);
                ReaderState::Reading(ReaderStateReading { seq, reader: r })
            }
            None => ReaderState::Finished,
        };
    }

    pub fn read(&mut self, mut data: &mut [u8]) -> Result<(), ReadError> {
        let m = &mut *self.m.inner.borrow_mut();
        while !data.is_empty() {
            match &mut self.state {
                ReaderState::Finished => return Err(ReadError::Eof),
                ReaderState::Created => {
                    self.next_page(m);
                    continue;
                }
                ReaderState::Reading(s) => {
                    let n = s.reader.read(&mut m.flash, data);
                    data = &mut data[n..];
                    s.seq = s.seq.checked_add(n.try_into().unwrap()).unwrap();
                    if n == 0 {
                        self.next_page(m);
                    }
                }
            }
        }
        Ok(())
    }

    pub fn skip(&mut self, mut len: usize) -> Result<(), ReadError> {
        let m = &mut *self.m.inner.borrow_mut();
        while len != 0 {
            match &mut self.state {
                ReaderState::Finished => return Err(ReadError::Eof),
                ReaderState::Created => {
                    self.next_page(m);
                    continue;
                }
                ReaderState::Reading(s) => {
                    let n = s.reader.skip(len);
                    len -= n;
                    s.seq = s.seq.checked_add(n.try_into().unwrap()).unwrap();
                    if n == 0 {
                        self.next_page(m);
                    }
                }
            }
        }
        Ok(())
    }
}

pub struct FileWriter<'a, F: Flash> {
    m: &'a FileManager<F>,
    file_id: FileID,
    last_page: Option<PagePointer>,
    seq: u32,
    writer: Option<PageWriter<F>>,
}

impl<'a, F: Flash> Drop for FileWriter<'a, F> {
    fn drop(&mut self) {
        let m = &mut *self.m.inner.borrow_mut();
        if let Some(w) = &self.writer {
            // Free the page we're writing now (not yet committed)
            let page_id = w.page_id();
            m.alloc.free(page_id);

            // Free previous pages, if any
            let f = &m.files[self.file_id as usize];
            m.free_between(self.last_page, f.last_page);
        };
    }
}

impl<'a, F: Flash> FileWriter<'a, F> {
    fn new(m: &'a FileManager<F>, file_id: FileID) -> Self {
        let mm = &mut *m.inner.borrow_mut();
        let f = &mm.files[file_id as usize];

        Self {
            m,
            file_id,
            last_page: f.last_page,
            seq: f.last_seq,
            writer: None,
        }
    }

    fn flush_header(&mut self, m: &mut Inner<F>, w: PageWriter<F>) {
        let page_size = w.offset().try_into().unwrap();
        let page_id = w.page_id();
        let header = Header {
            previous_page_id: self.last_page.map(|p| p.page_id).unwrap_or(PageID::MAX),
            seq: self.seq,
        };
        w.commit(&mut m.flash, header);

        self.seq = self.seq.checked_add(page_size).unwrap();
        self.last_page = Some(PagePointer { page_id, header });
    }

    fn next_page(&mut self, m: &mut Inner<F>) {
        if let Some(w) = mem::replace(&mut self.writer, None) {
            self.flush_header(m, w);
        }

        let page_id = m.alloc.allocate();
        self.writer = Some(m.write_page(page_id));
    }

    pub fn write(&mut self, mut data: &[u8]) {
        let m = &mut *self.m.inner.borrow_mut();
        while !data.is_empty() {
            match &mut self.writer {
                None => {
                    self.next_page(m);
                    continue;
                }
                Some(w) => {
                    let n = w.write(&mut m.flash, data);
                    data = &data[n..];
                    if n == 0 {
                        self.next_page(m);
                    }
                }
            }
        }
    }

    pub fn commit(&mut self) {
        let m = &mut *self.m.inner.borrow_mut();
        if let Some(w) = mem::replace(&mut self.writer, None) {
            self.flush_header(m, w);
            let f = &mut m.files[self.file_id as usize];
            f.last_page = self.last_page;
            f.last_seq = self.seq;
        }
    }

    pub fn record_end(&mut self) {
        // TODO
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::flash::MemFlash;

    #[test]
    fn test_read_write() {
        let mut f = MemFlash::new();
        FileManager::format(&mut f);
        let m = FileManager::new(&mut f);

        let data = dummy_data(24);

        let mut w = m.write(0);
        w.write(&data);
        w.commit();
        drop(w);

        let mut r = m.read(0);
        let mut buf = vec![0; data.len()];
        r.read(&mut buf).unwrap();
        assert_eq!(data, buf);

        m.commit();

        // Remount
        let m = FileManager::new(&mut f);

        let mut r = m.read(0);
        let mut buf = vec![0; data.len()];
        r.read(&mut buf).unwrap();
        assert_eq!(data, buf);
    }

    #[test]
    fn test_read_write_long() {
        let mut f = MemFlash::new();
        FileManager::format(&mut f);
        let m = FileManager::new(&mut f);

        let data = dummy_data(65201);

        let mut w = m.write(0);
        w.write(&data);
        w.commit();
        drop(w);

        let mut r = m.read(0);
        let mut buf = vec![0; data.len()];
        r.read(&mut buf).unwrap();
        assert_eq!(data, buf);

        m.commit();

        // Remount
        let m = FileManager::new(&mut f);

        let mut r = m.read(0);
        let mut buf = vec![0; data.len()];
        r.read(&mut buf).unwrap();
        assert_eq!(data, buf);
    }

    #[test]
    fn test_append() {
        let mut f = MemFlash::new();
        FileManager::format(&mut f);
        let m = FileManager::new(&mut f);

        let mut w = m.write(0);
        w.write(&[1, 2, 3, 4, 5]);
        w.commit();
        drop(w);

        let mut w = m.write(0);
        w.write(&[6, 7, 8, 9]);
        w.commit();
        drop(w);

        let mut r = m.read(0);
        let mut buf = vec![0; 9];
        r.read(&mut buf).unwrap();
        assert_eq!(buf, [1, 2, 3, 4, 5, 6, 7, 8, 9]);

        m.commit();

        let mut r = m.read(0);
        r.read(&mut buf).unwrap();
        assert_eq!(buf, [1, 2, 3, 4, 5, 6, 7, 8, 9]);

        // Remount
        let m = FileManager::new(&mut f);

        let mut r = m.read(0);
        r.read(&mut buf).unwrap();
        assert_eq!(buf, [1, 2, 3, 4, 5, 6, 7, 8, 9]);
    }

    #[test]
    fn test_truncate() {
        let mut f = MemFlash::new();
        FileManager::format(&mut f);
        let m = FileManager::new(&mut f);

        let mut w = m.write(0);
        w.write(&[1, 2, 3, 4, 5]);
        w.commit();
        drop(w);

        m.left_truncate(0, 2);

        let mut r = m.read(0);
        let mut buf = [0; 3];
        r.read(&mut buf).unwrap();
        assert_eq!(buf, [3, 4, 5]);

        m.left_truncate(0, 3);

        let mut r = m.read(0);
        let mut buf = [0; 2];
        r.read(&mut buf).unwrap();
        assert_eq!(buf, [4, 5]);

        m.commit();

        let mut r = m.read(0);
        let mut buf = [0; 2];
        r.read(&mut buf).unwrap();
        assert_eq!(buf, [4, 5]);

        // Remount
        let m = FileManager::new(&mut f);

        let mut r = m.read(0);
        let mut buf = [0; 2];
        r.read(&mut buf).unwrap();
        assert_eq!(buf, [4, 5]);
    }

    #[test]
    fn test_append_truncate() {
        let mut f = MemFlash::new();
        FileManager::format(&mut f);
        let m = FileManager::new(&mut f);

        let mut w = m.write(0);
        w.write(&[1, 2, 3, 4, 5]);
        w.commit();
        drop(w);

        let mut w = m.write(0);
        w.write(&[6, 7, 8, 9]);
        w.commit();
        drop(w);

        m.left_truncate(0, 2);

        let mut r = m.read(0);
        let mut buf = [0; 7];
        r.read(&mut buf).unwrap();
        assert_eq!(buf, [3, 4, 5, 6, 7, 8, 9]);

        m.left_truncate(0, 3);

        let mut r = m.read(0);
        let mut buf = [0; 6];
        r.read(&mut buf).unwrap();
        assert_eq!(buf, [4, 5, 6, 7, 8, 9]);

        m.left_truncate(0, 8);

        let mut r = m.read(0);
        let mut buf = [0; 1];
        r.read(&mut buf).unwrap();
        assert_eq!(buf, [9]);

        m.commit();

        let mut r = m.read(0);
        let mut buf = [0; 1];
        r.read(&mut buf).unwrap();
        assert_eq!(buf, [9]);

        // Remount
        let m = FileManager::new(&mut f);

        let mut r = m.read(0);
        let mut buf = [0; 1];
        r.read(&mut buf).unwrap();
        assert_eq!(buf, [9]);

        let mut w = m.write(0);
        w.write(&[10, 11, 12]);
        w.commit();

        let mut r = m.read(0);
        let mut buf = [0; 4];
        r.read(&mut buf).unwrap();
        assert_eq!(buf, [9, 10, 11, 12]);
    }

    #[test]
    fn test_append_no_commit() {
        let mut f = MemFlash::new();
        FileManager::format(&mut f);
        let m = FileManager::new(&mut f);

        let mut w = m.write(0);
        w.write(&[1, 2, 3, 4, 5]);
        w.commit();

        let mut w = m.write(0);
        w.write(&[6, 7, 8, 9]);
        drop(w);

        let mut r = m.read(0);
        let mut buf = [0; 5];
        r.read(&mut buf).unwrap();
        assert_eq!(buf, [1, 2, 3, 4, 5]);
        let mut buf = [0; 1];
        let res = r.read(&mut buf);
        assert!(matches!(res, Err(ReadError::Eof)));

        let mut w = m.write(0);
        w.write(&[10, 11]);
        w.commit();

        let mut r = m.read(0);
        let mut buf = [0; 7];
        r.read(&mut buf).unwrap();
        assert_eq!(buf, [1, 2, 3, 4, 5, 10, 11]);
    }

    #[test]
    fn test_read_unwritten() {
        let mut f = MemFlash::new();
        FileManager::format(&mut f);
        let m = FileManager::new(&mut f);

        let mut r = m.read(0);
        let mut buf = vec![0; 1024];
        let res = r.read(&mut buf);
        assert!(matches!(res, Err(ReadError::Eof)));
    }

    #[test]
    fn test_read_uncommitted() {
        let mut f = MemFlash::new();
        FileManager::format(&mut f);
        let m = FileManager::new(&mut f);

        let data = dummy_data(65201);

        let mut w = m.write(0);
        w.write(&data);
        drop(w); // don't commit

        let mut r = m.read(0);
        let mut buf = vec![0; 1024];
        let res = r.read(&mut buf);
        assert!(matches!(res, Err(ReadError::Eof)));
    }

    #[test]
    fn test_alloc_commit() {
        let mut f = MemFlash::new();
        FileManager::format(&mut f);
        let m = FileManager::new(&mut f);

        assert_eq!(m.inner.borrow().alloc.is_allocated(1), false);
        assert_eq!(m.inner.borrow().alloc.is_allocated(2), false);

        let data = dummy_data(PAGE_MAX_PAYLOAD_SIZE);
        let mut w = m.write(0);

        w.write(&data);
        assert_eq!(m.inner.borrow().alloc.is_allocated(0), true); // old meta
        assert_eq!(m.inner.borrow().alloc.is_allocated(1), true);
        assert_eq!(m.inner.borrow().alloc.is_allocated(2), false);
        assert_eq!(m.inner.borrow().alloc.is_allocated(3), false);

        w.write(&data);
        assert_eq!(m.inner.borrow().alloc.is_allocated(0), true); // old meta
        assert_eq!(m.inner.borrow().alloc.is_allocated(1), true);
        assert_eq!(m.inner.borrow().alloc.is_allocated(2), true);
        assert_eq!(m.inner.borrow().alloc.is_allocated(3), false);

        w.commit();
        assert_eq!(m.inner.borrow().alloc.is_allocated(0), true); // old meta
        assert_eq!(m.inner.borrow().alloc.is_allocated(1), true);
        assert_eq!(m.inner.borrow().alloc.is_allocated(2), true);
        assert_eq!(m.inner.borrow().alloc.is_allocated(3), false);

        drop(w);
        assert_eq!(m.inner.borrow().alloc.is_allocated(0), true); // old meta
        assert_eq!(m.inner.borrow().alloc.is_allocated(1), true);
        assert_eq!(m.inner.borrow().alloc.is_allocated(2), true);
        assert_eq!(m.inner.borrow().alloc.is_allocated(3), false);

        m.commit();
        assert_eq!(m.inner.borrow().alloc.is_allocated(0), false); // old meta
        assert_eq!(m.inner.borrow().alloc.is_allocated(1), true);
        assert_eq!(m.inner.borrow().alloc.is_allocated(2), true);
        assert_eq!(m.inner.borrow().alloc.is_allocated(3), true); // new meta

        // Remount
        let m = FileManager::new(&mut f);
        assert_eq!(m.inner.borrow().alloc.is_allocated(1), true);
        assert_eq!(m.inner.borrow().alloc.is_allocated(2), true);
        assert_eq!(m.inner.borrow().alloc.is_allocated(3), true); // new meta
    }

    #[test]
    fn test_alloc_not_commit_1page() {
        let mut f = MemFlash::new();
        FileManager::format(&mut f);
        let m = FileManager::new(&mut f);

        assert_eq!(m.inner.borrow().alloc.is_allocated(0), true);
        assert_eq!(m.inner.borrow().alloc.is_allocated(1), false);
        assert_eq!(m.inner.borrow().alloc.is_allocated(2), false);

        let data = dummy_data(PAGE_MAX_PAYLOAD_SIZE);
        let mut w = m.write(0);

        w.write(&data);
        assert_eq!(m.inner.borrow().alloc.is_allocated(0), true);
        assert_eq!(m.inner.borrow().alloc.is_allocated(1), true);
        assert_eq!(m.inner.borrow().alloc.is_allocated(2), false);

        drop(w);
        assert_eq!(m.inner.borrow().alloc.is_allocated(0), true);
        assert_eq!(m.inner.borrow().alloc.is_allocated(1), false);
        assert_eq!(m.inner.borrow().alloc.is_allocated(2), false);

        m.commit();
        assert_eq!(m.inner.borrow().alloc.is_allocated(0), false);
        assert_eq!(m.inner.borrow().alloc.is_allocated(1), false);
        assert_eq!(m.inner.borrow().alloc.is_allocated(2), true); // new meta

        // Remount
        let m = FileManager::new(&mut f);
        assert_eq!(m.inner.borrow().alloc.is_allocated(0), false);
        assert_eq!(m.inner.borrow().alloc.is_allocated(1), false);
        assert_eq!(m.inner.borrow().alloc.is_allocated(2), true); // new meta
    }

    #[test]
    fn test_alloc_not_commit_2page() {
        let mut f = MemFlash::new();
        FileManager::format(&mut f);
        let m = FileManager::new(&mut f);

        assert_eq!(m.inner.borrow().alloc.is_allocated(0), true);
        assert_eq!(m.inner.borrow().alloc.is_allocated(1), false);

        let data = dummy_data(PAGE_MAX_PAYLOAD_SIZE);
        let mut w = m.write(0);

        w.write(&data);
        assert_eq!(m.inner.borrow().alloc.is_allocated(0), true);
        assert_eq!(m.inner.borrow().alloc.is_allocated(1), true);
        assert_eq!(m.inner.borrow().alloc.is_allocated(2), false);

        w.write(&data);
        assert_eq!(m.inner.borrow().alloc.is_allocated(0), true);
        assert_eq!(m.inner.borrow().alloc.is_allocated(1), true);
        assert_eq!(m.inner.borrow().alloc.is_allocated(2), true);
        assert_eq!(m.inner.borrow().alloc.is_allocated(3), false);

        drop(w);
        assert_eq!(m.inner.borrow().alloc.is_allocated(0), true);
        assert_eq!(m.inner.borrow().alloc.is_allocated(1), false);
        assert_eq!(m.inner.borrow().alloc.is_allocated(2), false);
        assert_eq!(m.inner.borrow().alloc.is_allocated(3), false);

        m.commit();
        assert_eq!(m.inner.borrow().alloc.is_allocated(0), false);
        assert_eq!(m.inner.borrow().alloc.is_allocated(1), false);
        assert_eq!(m.inner.borrow().alloc.is_allocated(2), false);
        assert_eq!(m.inner.borrow().alloc.is_allocated(3), true);

        // Remount
        let m = FileManager::new(&mut f);
        assert_eq!(m.inner.borrow().alloc.is_allocated(0), false);
        assert_eq!(m.inner.borrow().alloc.is_allocated(1), false);
        assert_eq!(m.inner.borrow().alloc.is_allocated(2), false);
        assert_eq!(m.inner.borrow().alloc.is_allocated(3), true);
    }

    #[test]
    fn test_alloc_not_commit_3page() {
        let mut f = MemFlash::new();
        FileManager::format(&mut f);
        let m = FileManager::new(&mut f);

        assert_eq!(m.inner.borrow().alloc.is_allocated(0), true);
        assert_eq!(m.inner.borrow().alloc.is_allocated(1), false);
        assert_eq!(m.inner.borrow().alloc.is_allocated(2), false);
        assert_eq!(m.inner.borrow().alloc.is_allocated(3), false);

        let data = dummy_data(PAGE_MAX_PAYLOAD_SIZE * 3);
        let mut w = m.write(0);
        w.write(&data);
        assert_eq!(m.inner.borrow().alloc.is_allocated(0), true);
        assert_eq!(m.inner.borrow().alloc.is_allocated(1), true);
        assert_eq!(m.inner.borrow().alloc.is_allocated(2), true);
        assert_eq!(m.inner.borrow().alloc.is_allocated(3), true);
        assert_eq!(m.inner.borrow().alloc.is_allocated(4), false);

        drop(w);
        assert_eq!(m.inner.borrow().alloc.is_allocated(0), true);
        assert_eq!(m.inner.borrow().alloc.is_allocated(1), false);
        assert_eq!(m.inner.borrow().alloc.is_allocated(2), false);
        assert_eq!(m.inner.borrow().alloc.is_allocated(3), false);
        assert_eq!(m.inner.borrow().alloc.is_allocated(4), false);

        m.commit();
        assert_eq!(m.inner.borrow().alloc.is_allocated(0), false);
        assert_eq!(m.inner.borrow().alloc.is_allocated(1), false);
        assert_eq!(m.inner.borrow().alloc.is_allocated(2), false);
        assert_eq!(m.inner.borrow().alloc.is_allocated(3), false);
        assert_eq!(m.inner.borrow().alloc.is_allocated(4), true);

        // Remount
        let m = FileManager::new(&mut f);
        assert_eq!(m.inner.borrow().alloc.is_allocated(0), false);
        assert_eq!(m.inner.borrow().alloc.is_allocated(1), false);
        assert_eq!(m.inner.borrow().alloc.is_allocated(2), false);
        assert_eq!(m.inner.borrow().alloc.is_allocated(3), false);
        assert_eq!(m.inner.borrow().alloc.is_allocated(4), true);
    }

    #[test]
    fn test_append_alloc_not_commit() {
        let mut f = MemFlash::new();
        FileManager::format(&mut f);
        let m = FileManager::new(&mut f);

        assert_eq!(m.inner.borrow().alloc.is_allocated(0), true);
        assert_eq!(m.inner.borrow().alloc.is_allocated(1), false);

        let data = dummy_data(24);
        let mut w = m.write(0);
        w.write(&data);
        w.commit();
        drop(w);
        assert_eq!(m.inner.borrow().alloc.is_allocated(0), true);
        assert_eq!(m.inner.borrow().alloc.is_allocated(1), true);
        assert_eq!(m.inner.borrow().alloc.is_allocated(2), false);

        let mut w = m.write(0);
        w.write(&data);
        assert_eq!(m.inner.borrow().alloc.is_allocated(0), true);
        assert_eq!(m.inner.borrow().alloc.is_allocated(1), true);
        assert_eq!(m.inner.borrow().alloc.is_allocated(2), true);

        drop(w);
        assert_eq!(m.inner.borrow().alloc.is_allocated(0), true);
        assert_eq!(m.inner.borrow().alloc.is_allocated(1), true);
        assert_eq!(m.inner.borrow().alloc.is_allocated(2), false);

        m.commit();

        // Remount
        let m = FileManager::new(&mut f);
        assert_eq!(m.inner.borrow().alloc.is_allocated(0), false);
        assert_eq!(m.inner.borrow().alloc.is_allocated(1), true);
        assert_eq!(m.inner.borrow().alloc.is_allocated(2), false);
        assert_eq!(m.inner.borrow().alloc.is_allocated(3), true); // new meta
    }

    /*
    #[test]
    fn test_overwrite() {
        let mut f = MemFlash::new();
        FileManager::format(&mut f);
        let m = FileManager::new(&mut f);

        for i in 0..3000u32 {
            let mut w = m.write(0);
            w.write(&i.to_le_bytes());
            w.commit();
        }
    }

    #[test]
    fn test_overwrite_remount() {
        let mut f = MemFlash::new();
        FileManager::format(&mut f);

        for i in 0..3000u32 {
            let m = FileManager::new(&mut f);
            let mut w = m.write(0);
            w.write(&i.to_le_bytes());
            w.commit();
            m.commit();

            let m = FileManager::new(&mut f);
            let mut r = m.read(0);
            let mut buf = [0; 4];
            r.read(&mut buf).unwrap();
            assert_eq!(buf, i.to_le_bytes());
        }

        let m = FileManager::new(&mut f);
        let mut r = m.read(0);
        let mut buf = [0; 4];
        r.read(&mut buf).unwrap();
        assert_eq!(buf, 2999u32.to_le_bytes());
    }

    #[test]
    fn test_overwrite_remount_2() {
        let mut f = MemFlash::new();
        FileManager::format(&mut f);

        let m = FileManager::new(&mut f);
        for i in 0..3000u32 {
            let mut w = m.write(0);
            w.write(&i.to_le_bytes());
            w.commit();
            m.commit();
        }

        let m = FileManager::new(&mut f);
        let mut r = m.read(0);
        let mut buf = [0; 4];
        r.read(&mut buf).unwrap();
        assert_eq!(buf, 2999u32.to_le_bytes());
    }
     */

    fn dummy_data(len: usize) -> Vec<u8> {
        let mut res = vec![0; len];
        for (i, v) in res.iter_mut().enumerate() {
            *v = i as u8 ^ (i >> 8) as u8 ^ (i >> 16) as u8 ^ (i >> 24) as u8;
        }
        res
    }
}

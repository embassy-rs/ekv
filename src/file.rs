use core::mem;
use std::cell::RefCell;

use crate::alloc::Allocator;
use crate::config::*;
use crate::flash::Flash;
use crate::page::{PageManager, PageReader, PageWriter, ReadError};

const HEADER_FLAG_COMMITTED: u32 = 0x01;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum SeekDirection {
    Left,
    Right,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[repr(C)]
pub struct Header {
    flags: u32,
    file_id: FileID,
    index: u16,
    previous_page_id: PageID,
    // TODO add a skiplist for previous pages, instead of just storing the immediately previous one.
}

impl Header {
    #[cfg(test)]
    pub const DUMMY: Self = Self {
        flags: 0,
        file_id: 1,
        index: 2,
        previous_page_id: 3,
    };
}

struct FileState {
    last: Option<PagePointer>,
}

pub struct FileManager<F: Flash> {
    inner: RefCell<Inner<F>>,
}

struct Inner<F: Flash> {
    flash: F,
    pages: PageManager<F>,
    files: [FileState; FILE_COUNT],

    alloc: Allocator,
}

impl<F: Flash> FileManager<F> {
    pub fn new(flash: F) -> Self {
        const DUMMY_FILE: FileState = FileState { last: None };
        let mut inner = Inner {
            flash,
            pages: PageManager::new(),
            files: [DUMMY_FILE; FILE_COUNT],
            alloc: Allocator::new(),
        };
        inner.mount();

        Self {
            inner: RefCell::new(inner),
        }
    }

    pub fn read(&self, file_id: FileID) -> FileReader<'_, F> {
        FileReader::new(self, file_id)
    }

    pub fn write(&self, file_id: FileID) -> FileWriter<'_, F> {
        self.inner.borrow_mut().free_all_file(file_id);
        FileWriter::new(self, file_id)
    }
}

impl<F: Flash> Inner<F> {
    fn mount(&mut self) {
        for page_id in 0..PAGE_COUNT {
            if let Ok(h) = self.read_header(page_id as _) {
                if h.flags & HEADER_FLAG_COMMITTED != 0 {
                    self.files[h.file_id as usize] = FileState {
                        last: Some(PagePointer {
                            page_id: page_id as _,
                            header: h,
                        }),
                    };
                }
            }
        }

        for file_id in 0..FILE_COUNT as FileID {
            let mut p = self.files[file_id as usize].last;
            while let Some(pp) = p {
                self.alloc.mark_allocated(pp.page_id);
                p = pp.prev(self);
            }
        }
    }

    fn get_file_page(&mut self, file_id: FileID, index: usize) -> Option<PagePointer> {
        let last = self.files[file_id as usize].last?;
        if index > last.header.index as _ {
            None
        } else {
            last.prev_index(self, index)
        }
    }

    fn free_all_prev(&mut self, page_id: PageID) {
        let p = PagePointer {
            page_id,
            header: self.read_header(page_id).unwrap(),
        };
        self.free_all_prev_pp(Some(p));
    }

    fn free_all_prev_pp(&mut self, mut p: Option<PagePointer>) {
        while let Some(pp) = p {
            self.alloc.free(pp.page_id);
            p = pp.prev(self);
        }
    }

    fn free_all_file(&mut self, file_id: FileID) {
        self.free_all_prev_pp(self.files[file_id as usize].last);
        self.files[file_id as usize].last = None;
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
            assert_eq!(h2.file_id, self.header.file_id);
            assert_eq!(h2.index, self.header.index - 1);
            Some(PagePointer {
                page_id: p2,
                header: h2,
            })
        }
    }

    fn prev_index(self, m: &mut Inner<impl Flash>, index: usize) -> Option<PagePointer> {
        assert!(index <= self.header.index as _);

        let mut p = self;
        while p.header.index as usize != index {
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
    page_index: usize,
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
        let index = match &self.state {
            ReaderState::Created => 0,
            ReaderState::Reading(s) => s.page_index,
            ReaderState::Finished => unreachable!(),
        };
        self.state = match m.get_file_page(self.file_id, index) {
            Some(pp) => ReaderState::Reading(ReaderStateReading {
                page_index: index + 1,
                reader: m.read_page(pp.page_id).unwrap().1,
            }),
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

    state: WriterState<F>,
}

enum WriterState<F: Flash> {
    Created,
    Writing(WriterStateWriting<F>),
}

struct WriterStateWriting<F: Flash> {
    page_index: usize,
    previous_page_id: Option<PageID>,
    writer: PageWriter<F>,
}

impl<'a, F: Flash> Drop for FileWriter<'a, F> {
    fn drop(&mut self) {
        let m = &mut *self.m.inner.borrow_mut();
        if let WriterState::Writing(s) = &self.state {
            // Free the page we're writing now (not yet committed)
            let page_id = s.writer.page_id();
            m.alloc.free(page_id);

            // Free previous pages, if any
            if let Some(pp) = s.previous_page_id {
                m.free_all_prev(pp);
            }
        };
    }
}

impl<'a, F: Flash> FileWriter<'a, F> {
    fn new(m: &'a FileManager<F>, file_id: FileID) -> Self {
        Self {
            m,
            file_id,
            state: WriterState::Created,
        }
    }

    fn flush_header(&mut self, m: &mut Inner<F>, s: WriterStateWriting<F>, flags: u32) -> Header {
        let header = Header {
            flags: flags,
            file_id: self.file_id.try_into().unwrap(),
            index: s.page_index.try_into().unwrap(),
            previous_page_id: s.previous_page_id.unwrap_or(PageID::MAX),
        };
        s.writer.commit(&mut m.flash, header);
        header
    }

    fn next_page(&mut self, m: &mut Inner<F>) {
        let (page_index, previous_page_id) = match mem::replace(&mut self.state, WriterState::Created) {
            WriterState::Created => (0, None),
            WriterState::Writing(s) => {
                let page_id = s.writer.page_id();
                let page_index = s.page_index;

                // Flush header for the page we're done writing.
                self.flush_header(m, s, 0);

                (page_index + 1, Some(page_id))
            }
        };

        let page_id = m.alloc.allocate();
        self.state = WriterState::Writing(WriterStateWriting {
            page_index,
            previous_page_id,
            writer: m.write_page(page_id),
        });
    }

    pub fn write(&mut self, mut data: &[u8]) {
        let m = &mut *self.m.inner.borrow_mut();
        while !data.is_empty() {
            match &mut self.state {
                WriterState::Created => {
                    self.next_page(m);
                    continue;
                }
                WriterState::Writing(s) => {
                    let n = s.writer.write(&mut m.flash, data);
                    data = &data[n..];
                    if n == 0 {
                        self.next_page(m);
                    }
                }
            }
        }
    }

    pub fn commit(mut self) {
        let m = &mut *self.m.inner.borrow_mut();
        match mem::replace(&mut self.state, WriterState::Created) {
            WriterState::Created => {}
            WriterState::Writing(s) => {
                let page_id = s.writer.page_id();
                let header = self.flush_header(m, s, HEADER_FLAG_COMMITTED);
                m.files[self.file_id as usize] = FileState {
                    last: Some(PagePointer { page_id, header }),
                };
            }
        };
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
        let m = FileManager::new(&mut f);

        let data = dummy_data(65201);

        let mut w = m.write(0);
        w.write(&data);
        w.commit();

        let mut r = m.read(0);
        let mut buf = vec![0; data.len()];
        r.read(&mut buf).unwrap();
        assert_eq!(data, buf);

        // Remount
        let m = FileManager::new(&mut f);

        let mut r = m.read(0);
        let mut buf = vec![0; data.len()];
        r.read(&mut buf).unwrap();
        assert_eq!(data, buf);
    }

    #[test]
    fn test_read_unwritten() {
        let mut f = MemFlash::new();
        let m = FileManager::new(&mut f);

        let mut r = m.read(0);
        let mut buf = vec![0; 1024];
        let res = r.read(&mut buf);
        assert!(matches!(res, Err(ReadError::Eof)));
    }

    #[test]
    fn test_read_uncommitted() {
        let mut f = MemFlash::new();
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
        let m = FileManager::new(&mut f);

        assert_eq!(m.inner.borrow().alloc.is_allocated(0), false);
        assert_eq!(m.inner.borrow().alloc.is_allocated(1), false);

        let data = dummy_data(PAGE_MAX_PAYLOAD_SIZE);
        let mut w = m.write(0);

        w.write(&data);
        assert_eq!(m.inner.borrow().alloc.is_allocated(0), true);
        assert_eq!(m.inner.borrow().alloc.is_allocated(1), false);
        assert_eq!(m.inner.borrow().alloc.is_allocated(2), false);

        w.write(&data);
        assert_eq!(m.inner.borrow().alloc.is_allocated(0), true);
        assert_eq!(m.inner.borrow().alloc.is_allocated(1), true);
        assert_eq!(m.inner.borrow().alloc.is_allocated(2), false);

        w.commit();
        assert_eq!(m.inner.borrow().alloc.is_allocated(0), true);
        assert_eq!(m.inner.borrow().alloc.is_allocated(1), true);
        assert_eq!(m.inner.borrow().alloc.is_allocated(2), false);

        // Remount
        let m = FileManager::new(&mut f);
        assert_eq!(m.inner.borrow().alloc.is_allocated(0), true);
        assert_eq!(m.inner.borrow().alloc.is_allocated(1), true);
        assert_eq!(m.inner.borrow().alloc.is_allocated(2), false);
    }

    #[test]
    fn test_alloc_not_commit_1page() {
        let mut f = MemFlash::new();
        let m = FileManager::new(&mut f);

        assert_eq!(m.inner.borrow().alloc.is_allocated(0), false);
        assert_eq!(m.inner.borrow().alloc.is_allocated(1), false);

        let data = dummy_data(PAGE_MAX_PAYLOAD_SIZE);
        let mut w = m.write(0);

        w.write(&data);
        assert_eq!(m.inner.borrow().alloc.is_allocated(0), true);
        assert_eq!(m.inner.borrow().alloc.is_allocated(1), false);

        drop(w);
        assert_eq!(m.inner.borrow().alloc.is_allocated(0), false);
        assert_eq!(m.inner.borrow().alloc.is_allocated(1), false);

        // Remount
        let m = FileManager::new(&mut f);
        assert_eq!(m.inner.borrow().alloc.is_allocated(0), false);
        assert_eq!(m.inner.borrow().alloc.is_allocated(1), false);
    }

    #[test]
    fn test_alloc_not_commit_2page() {
        let mut f = MemFlash::new();
        let m = FileManager::new(&mut f);

        assert_eq!(m.inner.borrow().alloc.is_allocated(0), false);
        assert_eq!(m.inner.borrow().alloc.is_allocated(1), false);

        let data = dummy_data(PAGE_MAX_PAYLOAD_SIZE);
        let mut w = m.write(0);

        w.write(&data);
        assert_eq!(m.inner.borrow().alloc.is_allocated(0), true);
        assert_eq!(m.inner.borrow().alloc.is_allocated(1), false);
        assert_eq!(m.inner.borrow().alloc.is_allocated(2), false);

        w.write(&data);
        assert_eq!(m.inner.borrow().alloc.is_allocated(0), true);
        assert_eq!(m.inner.borrow().alloc.is_allocated(1), true);
        assert_eq!(m.inner.borrow().alloc.is_allocated(2), false);

        drop(w);
        assert_eq!(m.inner.borrow().alloc.is_allocated(0), false);
        assert_eq!(m.inner.borrow().alloc.is_allocated(1), false);
        assert_eq!(m.inner.borrow().alloc.is_allocated(2), false);

        // Remount
        let m = FileManager::new(&mut f);
        assert_eq!(m.inner.borrow().alloc.is_allocated(0), false);
        assert_eq!(m.inner.borrow().alloc.is_allocated(1), false);
        assert_eq!(m.inner.borrow().alloc.is_allocated(2), false);
    }

    #[test]
    fn test_alloc_not_commit_3page() {
        let mut f = MemFlash::new();
        let m = FileManager::new(&mut f);

        assert_eq!(m.inner.borrow().alloc.is_allocated(0), false);
        assert_eq!(m.inner.borrow().alloc.is_allocated(1), false);
        assert_eq!(m.inner.borrow().alloc.is_allocated(2), false);
        assert_eq!(m.inner.borrow().alloc.is_allocated(3), false);

        let data = dummy_data(PAGE_MAX_PAYLOAD_SIZE * 3);
        let mut w = m.write(0);
        w.write(&data);
        assert_eq!(m.inner.borrow().alloc.is_allocated(0), true);
        assert_eq!(m.inner.borrow().alloc.is_allocated(1), true);
        assert_eq!(m.inner.borrow().alloc.is_allocated(2), true);
        assert_eq!(m.inner.borrow().alloc.is_allocated(3), false);

        drop(w);
        assert_eq!(m.inner.borrow().alloc.is_allocated(0), false);
        assert_eq!(m.inner.borrow().alloc.is_allocated(1), false);
        assert_eq!(m.inner.borrow().alloc.is_allocated(2), false);
        assert_eq!(m.inner.borrow().alloc.is_allocated(3), false);

        // Remount
        let m = FileManager::new(&mut f);
        assert_eq!(m.inner.borrow().alloc.is_allocated(0), false);
        assert_eq!(m.inner.borrow().alloc.is_allocated(1), false);
        assert_eq!(m.inner.borrow().alloc.is_allocated(2), false);
        assert_eq!(m.inner.borrow().alloc.is_allocated(3), false);
    }

    #[test]
    fn test_overwrite() {
        let mut f = MemFlash::new();
        let m = FileManager::new(&mut f);

        for i in 0..3000u32 {
            let mut w = m.write(0);
            w.write(&i.to_le_bytes());
            w.commit();

            let mut r = m.read(0);
            let mut buf = [0; 4];
            r.read(&mut buf).unwrap();
            assert_eq!(buf, i.to_le_bytes());
        }
    }

    fn dummy_data(len: usize) -> Vec<u8> {
        let mut res = vec![0; len];
        for (i, v) in res.iter_mut().enumerate() {
            *v = i as u8 ^ (i >> 8) as u8 ^ (i >> 16) as u8 ^ (i >> 24) as u8;
        }
        res
    }
}

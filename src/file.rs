use core::mem;
use std::cell::RefCell;

use crate::flash::*;
use crate::page::{PageID, PageManager, PageReader, PageWriter, ReadError};

const BRANCHING_FACTOR: usize = 3;
const LEVEL_COUNT: usize = 3;
const MAX_FILE_COUNT: usize = BRANCHING_FACTOR * LEVEL_COUNT + 1; // TODO maybe it is +2

pub type FileID = u16;

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

enum FileState {
    Empty,
    Written { last_page_id: PageID },
}

pub struct FileManager<F: Flash> {
    inner: RefCell<Inner<F>>,
}

struct Inner<F: Flash> {
    flash: F,
    pages: PageManager<F>,
    files: [FileState; MAX_FILE_COUNT],

    // Page allocator
    used_pages: [bool; PAGE_COUNT], // TODO use a bitfield
    next_page_id: PageID,
}

impl<F: Flash> FileManager<F> {
    pub fn new(flash: F) -> Self {
        const DUMMY_FILE: FileState = FileState::Empty;
        let mut inner = Inner {
            flash,
            pages: PageManager::new(),
            files: [DUMMY_FILE; MAX_FILE_COUNT],
            used_pages: [false; PAGE_COUNT],
            next_page_id: 0, // TODO make random to spread out wear
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
        FileWriter::new(self, file_id)
    }
}

impl<F: Flash> Inner<F> {
    fn mount(&mut self) {
        for page_id in 0..PAGE_COUNT {
            if let Ok(h) = self.pages.read_header(&mut self.flash, page_id as _) {
                if h.flags & HEADER_FLAG_COMMITTED != 0 {
                    self.files[h.file_id as usize] = FileState::Written {
                        last_page_id: page_id as _,
                    }
                }
            }
        }
    }

    fn allocate_page(&mut self) -> PageID {
        let start = self.next_page_id;
        loop {
            let p = self.next_page_id;
            self.next_page_id += 1;

            if !self.used_pages[p as usize] {
                self.used_pages[p as usize] = true;
                return p;
            }

            if self.next_page_id == start {
                panic!("No free pages"); // TODO
            }
        }
    }

    fn get_file_page(&mut self, file_id: FileID, page_index: usize) -> Option<PageID> {
        match self.files[file_id as usize] {
            FileState::Empty => None,
            FileState::Written { last_page_id } => {
                let mut page_id = last_page_id;
                loop {
                    let h = self.pages.read_header(&mut self.flash, page_id).unwrap();
                    if h.index as usize == page_index {
                        break Some(page_id);
                    }

                    // TODO avoid infinite loops, checking the index in the header decreases.
                    page_id = h.previous_page_id;
                    if page_id == PageID::MAX {
                        break None;
                    }
                }
            }
        }
    }

    fn read_page(&mut self, page_id: PageID) -> Result<(Header, PageReader<F>), ReadError> {
        self.pages.read(&mut self.flash, page_id)
    }

    fn write_page(&mut self, page_id: PageID) -> PageWriter<F> {
        self.pages.write(&mut self.flash, page_id)
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
        todo!()
    }

    pub fn binary_search_seek(&mut self, direction: SeekDirection) -> bool {
        todo!()
    }

    fn next_page(&mut self, m: &mut Inner<F>) {
        let index = match &self.state {
            ReaderState::Created => 0,
            ReaderState::Reading(s) => s.page_index,
            ReaderState::Finished => unreachable!(),
        };
        self.state = match m.get_file_page(self.file_id, index) {
            Some(page_id) => ReaderState::Reading(ReaderStateReading {
                page_index: index + 1,
                reader: m.read_page(page_id).unwrap().1,
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
        // TODO mark pages for the non-committed file as freed.
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

    fn flush_header(&mut self, m: &mut Inner<F>, s: WriterStateWriting<F>, flags: u32) {
        let header = Header {
            flags: flags,
            file_id: self.file_id.try_into().unwrap(),
            index: s.page_index.try_into().unwrap(),
            previous_page_id: s.previous_page_id.unwrap_or(PageID::MAX),
        };
        s.writer.commit(&mut m.flash, header);
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

        let page_id = m.allocate_page();
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
                self.flush_header(m, s, HEADER_FLAG_COMMITTED);
                m.files[self.file_id as usize] = FileState::Written { last_page_id: page_id };
            }
        };
    }

    pub fn record_end(&mut self) {
        todo!();
    }
}

#[cfg(test)]
mod tests {

    use super::*;

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

    fn dummy_data(len: usize) -> Vec<u8> {
        let mut res = vec![0; len];
        for (i, v) in res.iter_mut().enumerate() {
            *v = i as u8 ^ (i >> 8) as u8 ^ (i >> 16) as u8 ^ (i >> 24) as u8;
        }
        res
    }
}

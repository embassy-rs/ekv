use std::mem::forget;

use crate::backend::{ReadError, SeekDirection};
use crate::flash::*;

const BRANCHING_FACTOR: usize = 3;
const LEVEL_COUNT: usize = 3;
const MAX_RUN_COUNT: usize = BRANCHING_FACTOR * LEVEL_COUNT + 1; // TODO maybe it is +2

const PAGE_HEADER_MAGIC: u32 = 0xc4e21c75;

type RunID = u16;
type PageID = u16;

const HEADER_FLAG_COMMITTED: u32 = 0x01;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[repr(C)]
struct PageHeader {
    magic: u32,
    flags: u32,
    run_id: RunID,
    index: u16,
    previous_page_id: PageID,
    // TODO add a skiplist for previous pages, instead of just storing the immediately previous one.
    // TODO some kind of "this is the last page in the run, so the run is complete"
}
impl_bytes!(PageHeader);

enum RunState {
    Empty,
    Written { last_page_id: PageID },
}

pub struct Backend<F: Flash> {
    flash: F,
    runs: [RunState; MAX_RUN_COUNT],

    // Page allocator
    used_pages: [bool; PAGE_COUNT], // TODO use a bitfield
    next_page_id: PageID,
}

impl<F: Flash> Backend<F> {
    pub fn new(flash: F) -> Self {
        const DUMMY_RUN: RunState = RunState::Empty;
        let mut this = Self {
            flash,
            runs: [DUMMY_RUN; MAX_RUN_COUNT],
            used_pages: [false; PAGE_COUNT],
            next_page_id: 0, // TODO make random to spread out wear
        };
        this.mount();
        this
    }

    fn mount(&mut self) {
        for page_id in 0..PAGE_COUNT {
            if let Some(h) = self.read_header(page_id as _) {
                if h.flags & HEADER_FLAG_COMMITTED != 0 {
                    self.runs[h.run_id as usize] = RunState::Written {
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

    fn write_header(&mut self, page_id: PageID, h: PageHeader) {
        let mut buf = h.to_bytes();
        self.flash.write(page_id as _, 0, &buf);
    }

    fn read_header(&mut self, page_id: PageID) -> Option<PageHeader> {
        let mut buf = [0u8; PageHeader::SIZE];
        self.flash.read(page_id as _, 0, &mut buf);
        let h = PageHeader::from_bytes(buf);
        if h.magic != PAGE_HEADER_MAGIC {
            return None;
        }

        Some(h)
    }

    fn get_run_page(&mut self, run_id: usize, page_index: usize) -> Option<PageID> {
        match self.runs[run_id] {
            RunState::Empty => None,
            RunState::Written { last_page_id } => {
                let mut page_id = last_page_id;
                loop {
                    let h = self.read_header(page_id).unwrap();
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

    fn read_run(&mut self, run_id: usize) -> RunReader<'_, F> {
        // TODO
        RunReader::new(self, run_id)
    }

    fn write_run(&mut self, run_id: usize) -> RunWriter<'_, F> {
        // TODO
        RunWriter::new(self, run_id)
    }
}

pub struct RunReader<'a, F: Flash> {
    backend: &'a mut Backend<F>,
    run_id: usize,

    state: ReaderState,
}

enum ReaderState {
    Created,
    Reading(ReaderStateReading),
    Finished,
}
struct ReaderStateReading {
    page_index: usize,
    page_id: PageID,
    offset: usize,
}

impl<'a, F: Flash> RunReader<'a, F> {
    fn new(backend: &'a mut Backend<F>, run_id: usize) -> Self {
        Self {
            backend,
            run_id,
            state: ReaderState::Created,
        }
    }

    /*
    fn binary_search_start(&mut self) {
        todo!()
    }

    fn binary_search_seek(&mut self, direction: SeekDirection) -> bool {
        todo!()
    }

    fn skip(&mut self, mut len: usize) -> Result<(), ReadError> {
        todo!()
    }
     */

    fn next_page(&mut self) {
        let index = match &self.state {
            ReaderState::Created => 0,
            ReaderState::Reading(s) => s.page_index,
            ReaderState::Finished => unreachable!(),
        };
        self.state = match self.backend.get_run_page(self.run_id, index) {
            Some(page_id) => ReaderState::Reading(ReaderStateReading {
                page_index: index + 1,
                page_id,
                offset: PageHeader::SIZE,
            }),
            None => ReaderState::Finished,
        };
    }

    fn read(&mut self, mut data: &mut [u8]) -> Result<(), ReadError> {
        while !data.is_empty() {
            match &mut self.state {
                ReaderState::Finished => return Err(ReadError::Eof),
                ReaderState::Created => {
                    self.next_page();
                    continue;
                }
                ReaderState::Reading(s) => {
                    let n = data.len().min(PAGE_SIZE - s.offset);
                    self.backend.flash.read(s.page_id as _, s.offset, &mut data[..n]);
                    data = &mut data[n..];
                    s.offset += n;
                    if s.offset == PAGE_SIZE {
                        self.next_page();
                    }
                }
            }
        }
        Ok(())
    }
}

pub struct RunWriter<'a, F: Flash> {
    backend: &'a mut Backend<F>,
    run_id: usize,

    state: WriterState,
}

enum WriterState {
    Created,
    Writing(WriterStateWriting),
}

struct WriterStateWriting {
    page_index: usize,
    page_id: PageID,
    offset: usize,
    previous_page_id: Option<PageID>,
}

impl<'a, F: Flash> Drop for RunWriter<'a, F> {
    fn drop(&mut self) {
        // TODO mark pages for the non-committed run as freed.
    }
}

impl<'a, F: Flash> RunWriter<'a, F> {
    fn new(backend: &'a mut Backend<F>, run_id: usize) -> Self {
        Self {
            backend,
            run_id,
            state: WriterState::Created,
        }
    }

    fn next_page(&mut self) {
        // Flush header for the page we're done writing.
        self.flush_header(0);
        let (page_index, previous_page_id) = match &self.state {
            WriterState::Created => (0, None),
            WriterState::Writing(s) => (s.page_index + 1, Some(s.page_id)),
        };

        let page_id = self.backend.allocate_page();
        self.state = WriterState::Writing(WriterStateWriting {
            page_index,
            page_id,
            offset: PageHeader::SIZE,
            previous_page_id,
        });
    }

    fn write(&mut self, mut data: &[u8]) {
        while !data.is_empty() {
            match &mut self.state {
                WriterState::Created => {
                    self.next_page();
                    continue;
                }
                WriterState::Writing(s) => {
                    let n = data.len().min(PAGE_SIZE - s.offset);
                    self.backend.flash.write(s.page_id as _, s.offset, &data[..n]);
                    data = &data[n..];
                    s.offset += n;
                    if s.offset == PAGE_SIZE {
                        self.next_page();
                    }
                }
            }
        }
    }

    fn flush_header(&mut self, flags: u32) {
        if let WriterState::Writing(s) = &self.state {
            let h = PageHeader {
                magic: PAGE_HEADER_MAGIC,
                flags,
                run_id: self.run_id.try_into().unwrap(),
                index: s.page_index.try_into().unwrap(),
                previous_page_id: s.previous_page_id.unwrap_or(PageID::MAX),
            };
            self.backend.write_header(s.page_id, h);
        }
    }

    fn commit(mut self) {
        self.flush_header(HEADER_FLAG_COMMITTED);
        if let WriterState::Writing(s) = &self.state {
            self.backend.runs[self.run_id] = RunState::Written {
                last_page_id: s.page_id,
            };
        }

        forget(self);
    }

    fn record_end(&mut self) {
        todo!();
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn test_rw_header() {
        let mut b = Backend::new(MemFlash::new());
        let h = PageHeader {
            magic: PAGE_HEADER_MAGIC,
            index: 1,
            run_id: 3,
            previous_page_id: 5,
            flags: 1234,
        };
        b.write_header(0, h);
        let h2 = b.read_header(0).unwrap();
        assert_eq!(h, h2)
    }

    #[test]
    fn test_write_run() {
        let mut f = MemFlash::new();
        let mut b = Backend::new(&mut f);

        let data = dummy_data(65201);

        let mut w = b.write_run(0);
        w.write(&data);
        w.commit();

        let mut r = b.read_run(0);
        let mut buf = vec![0; data.len()];
        r.read(&mut buf).unwrap();
        assert_eq!(data, buf);

        let mut b = Backend::new(&mut f);

        let mut r = b.read_run(0);
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

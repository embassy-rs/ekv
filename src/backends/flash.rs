use std::mem::forget;

use crate::backend::{ReadError, SeekDirection};
use crate::flash::*;

const BRANCHING_FACTOR: usize = 3;
const LEVEL_COUNT: usize = 3;
const MAX_RUN_COUNT: usize = BRANCHING_FACTOR * LEVEL_COUNT + 1; // TODO maybe it is +2

const PAGE_HEADER_MAGIC: u32 = 0xc4e21c75;

type RunID = u16;
type PageID = u16;
const INVALID_PAGE_ID: PageID = PageID::MAX;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[repr(C)]
struct PageHeader {
    magic: u32,
    run_id: RunID,
    index: u16,
    previous_page_id: PageID,
    // TODO add a skiplist for previous pages, instead of just storing the immediately previous one.
    // TODO some kind of "this is the last page in the run, so the run is complete"
}
impl_bytes!(PageHeader);

struct Run {
    last_page_id: PageID,
}

pub struct Backend<F: Flash> {
    flash: F,
    runs: [Run; MAX_RUN_COUNT],

    // Page allocator
    used_pages: [bool; PAGE_COUNT], // TODO use a bitfield
    next_page_id: PageID,
}

impl<F: Flash> Backend<F> {
    pub fn new(flash: F) -> Self {
        const DUMMY_RUN: Run = Run {
            last_page_id: INVALID_PAGE_ID,
        };
        Self {
            flash,
            runs: [DUMMY_RUN; MAX_RUN_COUNT],
            used_pages: [false; PAGE_COUNT],
            next_page_id: 0, // TODO make random to spread out wear
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
        let mut page_id = self.runs[run_id].last_page_id;
        while page_id != INVALID_PAGE_ID {
            let h = self.read_header(page_id).unwrap();
            if h.index as usize == page_index {
                return Some(page_id);
            }
            page_id = h.previous_page_id
        }
        None
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

    // Current cursor
    page_index: usize,
    page_id: PageID,
    offset: usize,
}

impl<'a, F: Flash> RunReader<'a, F> {
    fn new(backend: &'a mut Backend<F>, run_id: usize) -> Self {
        Self {
            backend,
            run_id,
            page_id: INVALID_PAGE_ID,
            page_index: 0,
            offset: 0,
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
        if self.page_id == INVALID_PAGE_ID {
            self.page_id = 0;
        } else {
            self.page_id += 1;
        }

        self.offset = PageHeader::SIZE;
    }

    fn read(&mut self, mut data: &mut [u8]) -> Result<(), ReadError> {
        while !data.is_empty() {
            assert!(self.offset <= PAGE_SIZE);
            if self.page_id == INVALID_PAGE_ID || self.offset == PAGE_SIZE {
                self.next_page();
            }

            let n = data.len().min(PAGE_SIZE - self.offset);
            self.backend.flash.read(self.page_id as _, self.offset, &mut data[..n]);
            data = &mut data[n..];
            self.offset += n;
        }
        Ok(())
    }
}

pub struct RunWriter<'a, F: Flash> {
    backend: &'a mut Backend<F>,
    run_id: usize,

    // Current write cursor
    page_id: PageID,
    page_index: usize,
    offset: usize,

    previous_page_id: PageID,
}

impl<'a, F: Flash> RunWriter<'a, F> {
    fn new(backend: &'a mut Backend<F>, run_id: usize) -> Self {
        Self {
            backend,
            run_id,

            previous_page_id: INVALID_PAGE_ID,
            page_id: INVALID_PAGE_ID,
            page_index: 0,
            offset: 0,
        }
    }

    fn next_page(&mut self) {
        // Flush header for the page we're done writing.
        if self.page_id != INVALID_PAGE_ID {
            let h = PageHeader {
                magic: PAGE_HEADER_MAGIC,
                run_id: self.run_id as _,
                index: self.page_index as _,
                previous_page_id: self.previous_page_id as _,
            };
            self.backend.write_header(self.page_id, h);
        }

        self.previous_page_id = self.page_id;

        self.page_id = self.backend.allocate_page();
        self.page_index += 1;
        self.offset = PageHeader::SIZE;
    }

    fn write(&mut self, mut data: &[u8]) {
        while !data.is_empty() {
            assert!(self.offset <= PAGE_SIZE);
            if self.page_id == INVALID_PAGE_ID || self.offset == PAGE_SIZE {
                self.next_page();
            }

            let n = data.len().min(PAGE_SIZE - self.offset);
            self.backend.flash.write(self.page_id as _, self.offset, &data[..n]);
            data = &data[n..];
            self.offset += n;
        }
    }

    fn commit(self) {
        let h = PageHeader {
            magic: PAGE_HEADER_MAGIC,
            run_id: self.run_id.try_into().unwrap(),
            index: self.page_index.try_into().unwrap(),
            previous_page_id: self.previous_page_id.try_into().unwrap(),
        };
        self.backend.write_header(self.page_id, h);

        self.backend.runs[self.run_id].last_page_id = self.page_id;

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
        drop(w);

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

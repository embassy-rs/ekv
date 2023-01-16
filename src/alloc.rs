use crate::config::*;
use crate::types::{PageID, RawPageID};

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum PageState {
    Free,
    Used,
}

/// Page allocator
pub struct Allocator {
    pages: [PageState; PAGE_COUNT], // TODO use a bitfield
    used: usize,
    next_page_id: RawPageID,
}

impl Allocator {
    pub fn new() -> Self {
        Self {
            pages: [PageState::Free; PAGE_COUNT],
            used: 0,
            next_page_id: 0, // TODO make random to spread out wear
        }
    }

    pub fn reset(&mut self) {
        self.used = 0;
        self.pages.fill(PageState::Free);
    }

    pub fn allocate(&mut self) -> PageID {
        let start = self.next_page_id;
        loop {
            let p = self.next_page_id;
            self.next_page_id += 1;
            if self.next_page_id == PAGE_COUNT as _ {
                self.next_page_id = 0;
            }

            let v = &mut self.pages[p as usize];
            if *v == PageState::Free {
                *v = PageState::Used;
                self.used += 1;
                return PageID::from_raw(p).unwrap();
            }

            if self.next_page_id == start {
                panic!("No free pages"); // TODO
            }
        }
    }

    pub fn mark_used(&mut self, page_id: PageID) {
        assert_eq!(self.pages[page_id.index()], PageState::Free);
        self.pages[page_id.index()] = PageState::Used;
        self.used += 1;
    }

    pub fn free(&mut self, page_id: PageID) {
        let v = &mut self.pages[page_id.index()];
        *v = match *v {
            PageState::Free => panic!("double free"),
            PageState::Used => PageState::Free,
        };
        self.used -= 1;
    }

    pub fn is_used(&self, page_id: PageID) -> bool {
        self.pages[page_id.index()] == PageState::Used
    }

    pub fn used(&self) -> usize {
        self.used
    }
}

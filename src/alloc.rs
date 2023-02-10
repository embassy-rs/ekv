use crate::config::*;
use crate::types::{PageID, RawPageID};

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub enum PageState {
    Free,
    Used,
}

/// Page allocator
pub struct Allocator {
    page_count: usize,
    pages: [PageState; MAX_PAGE_COUNT], // TODO use a bitfield
    used: usize,
    next_page_id: usize,
}

impl Allocator {
    pub fn new(page_count: usize) -> Self {
        assert!(page_count <= MAX_PAGE_COUNT);
        Self {
            page_count,
            pages: [PageState::Free; MAX_PAGE_COUNT],
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
            if self.next_page_id == self.page_count {
                self.next_page_id = 0;
            }

            let v = &mut self.pages[p];
            if *v == PageState::Free {
                *v = PageState::Used;
                self.used += 1;
                return PageID::from_raw(p as RawPageID).unwrap();
            }

            if self.next_page_id == start {
                panic!("No free pages"); // TODO
            }
        }
    }

    pub fn mark_used(&mut self, page_id: PageID) {
        assert!(page_id.index() < self.page_count);

        assert_eq!(self.pages[page_id.index()], PageState::Free);
        self.pages[page_id.index()] = PageState::Used;
        self.used += 1;
    }

    pub fn free(&mut self, page_id: PageID) {
        assert!(page_id.index() < self.page_count);

        let v = &mut self.pages[page_id.index()];
        *v = match *v {
            PageState::Free => panic!("double free"),
            PageState::Used => PageState::Free,
        };
        self.used -= 1;
    }

    pub fn is_used(&self, page_id: PageID) -> bool {
        assert!(page_id.index() < self.page_count);

        self.pages[page_id.index()] == PageState::Used
    }

    pub fn used_pages(&self) -> usize {
        self.used
    }

    pub(crate) fn free_pages(&self) -> usize {
        self.page_count - self.used
    }

    pub(crate) fn page_count(&self) -> usize {
        self.page_count
    }
}

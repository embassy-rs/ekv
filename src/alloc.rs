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
    pages: [u8; (MAX_PAGE_COUNT + 7) / 8],
    used: usize,
    next_page_id: usize,
}

impl Allocator {
    pub fn new(page_count: usize) -> Self {
        assert!(page_count <= MAX_PAGE_COUNT);
        Self {
            page_count,
            pages: [0u8; (MAX_PAGE_COUNT + 7) / 8],
            used: 0,
            next_page_id: 0, // TODO make random to spread out wear
        }
    }

    pub fn get_bit(&self, i: usize) -> PageState {
        match (self.pages[i / 8] >> (i % 8)) & 1 {
            0 => PageState::Free,
            1 => PageState::Used,
            _ => unreachable!(),
        }
    }

    pub fn set_bit(&mut self, i: usize, state: PageState) {
        match state {
            PageState::Free => self.pages[i / 8] &= !(1 << (i % 8)),
            PageState::Used => self.pages[i / 8] |= 1 << (i % 8),
        }
    }

    pub fn reset(&mut self) {
        self.used = 0;
        self.pages.fill(0x00);
    }

    pub fn allocate(&mut self) -> PageID {
        unwrap!(self.try_allocate())
    }

    pub fn try_allocate(&mut self) -> Option<PageID> {
        let start = self.next_page_id;
        loop {
            let p = self.next_page_id;
            self.next_page_id += 1;
            if self.next_page_id == self.page_count {
                self.next_page_id = 0;
            }

            if self.get_bit(p) == PageState::Free {
                self.set_bit(p, PageState::Used);
                self.used += 1;
                return Some(PageID::from_raw(p as RawPageID).unwrap());
            }

            if self.next_page_id == start {
                return None;
            }
        }
    }

    pub fn mark_used(&mut self, page_id: PageID) {
        assert!(page_id.index() < self.page_count, "out of bounds");
        assert_eq!(self.get_bit(page_id.index()), PageState::Free, "double mark_used");

        self.set_bit(page_id.index(), PageState::Used);
        self.used += 1;
    }

    pub fn free(&mut self, page_id: PageID) {
        assert!(page_id.index() < self.page_count, "out of bounds");
        assert_eq!(self.get_bit(page_id.index()), PageState::Used, "double free");

        self.set_bit(page_id.index(), PageState::Free);
        self.used -= 1;
    }

    pub fn is_used(&self, page_id: PageID) -> bool {
        assert!(page_id.index() < self.page_count, "out of bounds");

        self.get_bit(page_id.index()) == PageState::Used
    }

    pub fn used_pages(&self) -> usize {
        self.used
    }

    pub fn free_pages(&self) -> usize {
        self.page_count - self.used
    }

    pub fn page_count(&self) -> usize {
        self.page_count
    }
}

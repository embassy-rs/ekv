use crate::config::*;

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum PageState {
    Free,
    UsedOnCommit,
    FreedOnCommit,
    Used,
}

/// Page allocator
pub struct Allocator {
    pages: [PageState; PAGE_COUNT], // TODO use a bitfield
    next_page_id: PageID,
}

impl Allocator {
    pub fn new() -> Self {
        Self {
            pages: [PageState::Free; PAGE_COUNT],
            next_page_id: 0, // TODO make random to spread out wear
        }
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
                *v = PageState::UsedOnCommit;
                return p;
            }

            if self.next_page_id == start {
                panic!("No free pages"); // TODO
            }
        }
    }

    pub fn mark_used(&mut self, page_id: PageID) {
        assert_eq!(self.pages[page_id as usize], PageState::Free);
        self.pages[page_id as usize] = PageState::Used;
    }

    pub fn free(&mut self, page_id: PageID) {
        let v = &mut self.pages[page_id as usize];
        *v = match *v {
            PageState::Free => panic!("double free"),
            PageState::FreedOnCommit => panic!("double free"),
            PageState::Used => PageState::FreedOnCommit,
            PageState::UsedOnCommit => PageState::Free,
        };
    }

    pub fn commit(&mut self) {
        for v in &mut self.pages {
            *v = match *v {
                PageState::Free => PageState::Free,
                PageState::FreedOnCommit => PageState::Free,
                PageState::Used => PageState::Used,
                PageState::UsedOnCommit => PageState::Used,
            }
        }
    }

    #[cfg(test)]
    pub fn is_used(&self, page_id: PageID) -> bool {
        self.pages[page_id as usize] != PageState::Free
    }
}

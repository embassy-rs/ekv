use crate::page::PageHeader;

// Flash parameters -- TODO unhardcode
pub const WRITE_SIZE: usize = 4;
pub const PAGE_SIZE: usize = 4096;
pub const PAGE_COUNT: usize = 256;
pub const ERASE_VALUE: u8 = 0xFF;

pub const PAGE_MAX_PAYLOAD_SIZE: usize = PAGE_SIZE - PageHeader::SIZE;

// File tree parameters
pub const BRANCHING_FACTOR: usize = 2;
pub const LEVEL_COUNT: usize = 4;
pub const FILE_COUNT: usize = BRANCHING_FACTOR * LEVEL_COUNT + 1;

pub type FileID = u16;
pub type PageID = u16;

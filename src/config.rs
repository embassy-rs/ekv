use crate::page::{ChunkHeader, PageHeader};

// ======== Flash parameters -- TODO unhardcode
pub const WRITE_SIZE: usize = 1;
pub const PAGE_SIZE: usize = 256;
pub const PAGE_COUNT: usize = 128;
pub const ERASE_VALUE: u8 = 0xFF;

pub const PAGE_MAX_PAYLOAD_SIZE: usize = PAGE_SIZE - PageHeader::SIZE - ChunkHeader::SIZE;

// ======== Filesystem parameters
/// Number of entries in the page header skiplist.
pub const SKIPLIST_LEN: usize = 5;
/// Shift of the first entry of the skiplist. Ideal value is ceil(log2(PAGE_SIZE))
pub const SKIPLIST_SHIFT: usize = 8;

// ======== File tree parameters
pub const BRANCHING_FACTOR: usize = 3; // must be 2 or higher
pub const LEVEL_COUNT: usize = 4;
pub const FILE_COUNT: usize = BRANCHING_FACTOR * LEVEL_COUNT + 1;

// ======== Key-value database parameters
pub const MAX_KEY_SIZE: usize = 64;

pub type FileID = u16;
pub type PageID = u16;

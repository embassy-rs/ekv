use core::mem::size_of;

use crate::file::{DataHeader, MetaHeader};

// ======== Flash parameters -- TODO unhardcode
pub const WRITE_SIZE: usize = 4;
pub const PAGE_SIZE: usize = 256;
pub const PAGE_COUNT: usize = 128;
pub const ERASE_VALUE: u8 = 0xFF;

pub const MAX_HEADER_SIZE: usize = {
    let a = size_of::<MetaHeader>();
    let b = size_of::<DataHeader>();
    if a > b {
        a
    } else {
        b
    }
};

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

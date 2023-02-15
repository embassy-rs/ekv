use core::mem::size_of;

use crate::file::{DataHeader, MetaHeader, PAGE_MAX_PAYLOAD_SIZE};
use crate::record::record_size;

mod raw {
    #![allow(unused)]
    include!(concat!(env!("OUT_DIR"), "/config.rs"));
}

// ======== Flash parameters
pub const ALIGN: usize = raw::ALIGN;
pub const PAGE_SIZE: usize = raw::PAGE_SIZE;
pub const MAX_PAGE_COUNT: usize = raw::MAX_PAGE_COUNT;
pub const ERASE_VALUE: u8 = match raw::ERASE_VALUE {
    0x00 => 0x00,
    0xFF => 0xFF,
    _ => core::panic!("invalid ERASE_VALUE"),
};

pub(crate) const MAX_HEADER_SIZE: usize = {
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
/// Substract 2 because we normally won't have a single file spanning the entire flash.
/// Assuming it'll span 1/4th is reasonable, and if it's larger it'll still work,
/// just doing 1-2 extra binary search steps.
pub(crate) const SKIPLIST_LEN: usize = MAX_PAGE_COUNT.ilog2() as usize - 2;
/// Shift of the first entry of the skiplist. Ideal value is ceil(log2(PAGE_SIZE))
pub(crate) const SKIPLIST_SHIFT: usize = PAGE_MAX_PAYLOAD_SIZE.ilog2() as usize + 1;

// ======== File tree parameters
pub(crate) const BRANCHING_FACTOR: usize = 3; // must be 2 or higher
pub(crate) const LEVEL_COUNT: usize = MAX_PAGE_COUNT.ilog(BRANCHING_FACTOR) as usize;
pub(crate) const FILE_COUNT: usize = BRANCHING_FACTOR * LEVEL_COUNT + 1;

// ======== Key-value database parameters
pub const MAX_KEY_SIZE: usize = raw::MAX_KEY_SIZE;
pub const MAX_VALUE_SIZE: usize = raw::MAX_VALUE_SIZE;

pub const SCRATCH_PAGE_COUNT: usize = raw::SCRATCH_PAGE_COUNT;

// Compaction will be stopped when there's this amount of free pages left.
// We need at least one page free, in case file commit needs to write a new meta page.
// There's no point in leaving more pages.
pub(crate) const MIN_FREE_PAGE_COUNT_COMPACT: usize = 1;

// Compaction will be triggered when there's thisamount of free pages left or less.
// there's some lower bound to this that guarantees progressive compaction will never get stuck. it's something like:
// FREE_PAGE_BUFFER_COMMIT + BRANCHING_FACTOR + ceil(max_record_size / page_max_payload_size)
// TODO: figure out exact formula, prove it
pub(crate) const MIN_FREE_PAGE_COUNT: usize = 1
    + SCRATCH_PAGE_COUNT
    + MIN_FREE_PAGE_COUNT_COMPACT
    + BRANCHING_FACTOR
    + (record_size(MAX_KEY_SIZE, MAX_VALUE_SIZE) + PAGE_MAX_PAYLOAD_SIZE - 1) / PAGE_MAX_PAYLOAD_SIZE;

pub type FileID = u8;

#[allow(clippy::assertions_on_constants)]
const _CHECKS: () = {
    // using core::assert to avoid using defmt, because it doesn't work in const.

    // Only align 1, 2, 4 is supported for now.
    // We only align data. Header sizes are aligned to 4 but not 8.
    // Supporting higher aligns would require aligning the headers as well.
    core::assert!(ALIGN == 1 || ALIGN == 2 || ALIGN == 4);

    // assert MIN_FREE_PAGE_COUNT is reasonable.
    // If it's too big relative to the total flash size, we'll waste a lot of space!
    core::assert!(MIN_FREE_PAGE_COUNT < MAX_PAGE_COUNT / 2);
};

pub fn dump() {
    debug!("ekv config dump:");
    debug!(
        "page_size={}, max_page_count={}, max_total_size={}",
        PAGE_SIZE,
        MAX_PAGE_COUNT,
        MAX_PAGE_COUNT * PAGE_SIZE,
    );
    debug!("align={}, erase_value={:02x}", ALIGN, ERASE_VALUE);
    debug!(
        "sizeof(MetaHeader)={}, sizeof(DataHeader)={}, page_max_payload_size={}",
        size_of::<MetaHeader>(),
        size_of::<DataHeader>(),
        PAGE_MAX_PAYLOAD_SIZE
    );
    debug!("skiplist_len={}, skiplist_shift={}", SKIPLIST_LEN, SKIPLIST_SHIFT);
    debug!(
        "branching_factor={}, level_count={}, file_count={}",
        BRANCHING_FACTOR, LEVEL_COUNT, FILE_COUNT
    );
    let max_record_size = record_size(MAX_KEY_SIZE, MAX_VALUE_SIZE);
    debug!(
        "max_key_size={}, max_value_size={}, max_record_size={} ({} pages)",
        MAX_KEY_SIZE,
        MAX_VALUE_SIZE,
        max_record_size,
        (max_record_size + PAGE_MAX_PAYLOAD_SIZE - 1) / PAGE_MAX_PAYLOAD_SIZE
    );
    debug!(
        "scratch_page_count={}, min_free_page_count={}, min_free_page_count_compact={}",
        SCRATCH_PAGE_COUNT, MIN_FREE_PAGE_COUNT, MIN_FREE_PAGE_COUNT_COMPACT
    );
}

//! Compile-time configuration.
//!
//! `ekv` has some configuration settings that are set at compile time.
//!
//! They can be set in two ways:
//!
//! - Via Cargo features: enable a feature like `<name>-<value>`. `name` must be in lowercase and
//!   use dashes instead of underscores. For example. `max-page-count-1024`. Only a selection of values
//!   is available, check `Cargo.toml` for the list.
//! - Via environment variables at build time: set the variable named `EKV_<value>`. For example
//!   `EKV_MAX_PAGE_COUNT=1024 cargo build`. You can also set them in the `[env]` section of `.cargo/config.toml`.
//!   Any value can be set, unlike with Cargo features.
//!
//! Environment variables take precedence over Cargo features. If two Cargo features are enabled for the same setting
//! with different values, compilation fails.
//!
//! ## Compatibility warning
//!
//! Changing ANY of these configuration settings changes the on-disk format of the database. If you change
//! them, you won't be able to read databases written with a different configuration.
//!
//! Currently, mounting doesn't check the on-disk database uses the same configuration. Mounting a database
//! with a different configuration might succeed and then cause fun errors later, perhaps very rarely.
//! Always remember to format your flash device every time you change them.

use core::mem::size_of;

use crate::file::{DataHeader, MetaHeader, PAGE_MAX_PAYLOAD_SIZE};
use crate::record::RecordHeader;

mod raw {
    #![allow(unused)]
    include!(concat!(env!("OUT_DIR"), "/config.rs"));

    #[cfg(feature = "crc")]
    pub const CRC: bool = true;
    #[cfg(not(feature = "crc"))]
    pub const CRC: bool = false;
}

// ======== Flash parameters

/// Protect integrity of the data in flash with CRCs.
///
/// If enabled, CRCs are appended to page and chunk headers, calculated
/// on write and verified on read. Verification failures are returned as `Corrupted` errors.
pub const CRC: bool = raw::CRC;

/// Flash alignment for reads and writes.
///
/// All flash `read` and `write` operations will be done with address and size
/// multiples of this value. Useful when the flash supports writing with 16-bit
/// or 32-bit word granularity.
///
/// Supported values: 1, 2 or 4.
///
/// Default: 4
pub const ALIGN: usize = raw::ALIGN;

/// Flash page size
///
/// This is the size of a flash page. A page is the smallest unit that can be
/// erased at once, sometimes called a "sector" or "erase block".
///
/// Doesn't necessarily have to be a power of two.
///
/// Default: 4096.
pub const PAGE_SIZE: usize = raw::PAGE_SIZE;

/// Maximum flash page count supported.
///
/// The actual page count is given at runtime by the [`Flash`](crate::flash::Flash) in use.
/// This value is just a compile-time upper limit, used to size some in-memory and on-disk data
/// structures. This allows supporting different memory sizes with the same binary.
///
/// Default: 256
pub const MAX_PAGE_COUNT: usize = raw::MAX_PAGE_COUNT;

/// Value of flash memory bytes after erasing.
///
/// This must be set to the value that all bytes in a page become after erasing it. For most
/// NOR flash, it is 0xFF. However, some are "inverted", and the erase value is 0x00.
///
/// Supported values: 0x00, 0xFF.
///
/// Default: 0xFF.
pub const ERASE_VALUE: u8 = match raw::ERASE_VALUE {
    0x00 => 0x00,
    0xFF => 0xFF,
    _ => core::panic!("invalid ERASE_VALUE"),
};

/// Maximum chunk size supported.
///
/// The chunk size controls how big chunks of data is read and written from/to flash. A low
/// value reduces the memory usage of EKV at the expense of more reads/writes.
///
/// Default: 4096
pub const MAX_CHUNK_SIZE: usize = raw::MAX_CHUNK_SIZE;

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

/// Branching factor of the file tree.
///
/// This sets how many files are in each level. When a level gets full,
/// the `BRANCHING_FACTOR` files in that level are compacted to a single
/// file in the upper level.
///
/// For most use cases, the default of `2` is likely to be the best choice. Higher values might
/// help making writes faster thanks to having to compact less, but will make reads
/// slower. This is unlikely to be a good tradeoff if reads are more common, since in
/// practice reads are already likely slower.
///
/// Do not change this from the default of `2` unless you have donen benchmarks and
/// are sure the non-default setting is better for your use case.
///
/// Supported values: 2 or higher.
///
/// Default: 2.
pub const BRANCHING_FACTOR: usize = raw::BRANCHING_FACTOR;

pub(crate) const LEVEL_COUNT: usize = MAX_PAGE_COUNT.ilog(BRANCHING_FACTOR) as usize;
pub(crate) const FILE_COUNT: usize = BRANCHING_FACTOR * LEVEL_COUNT + 1;

// ======== Key-value database parameters

/// Maximum supported key size.
///
/// Keys can be any length, between 0 and this value, both included.
///
/// Default: 64.
pub const MAX_KEY_SIZE: usize = raw::MAX_KEY_SIZE;

/// Maximum supported value size.
///
/// Values can be any length, between 0 and this value, both included.
///
/// Default: 1024.
pub const MAX_VALUE_SIZE: usize = raw::MAX_VALUE_SIZE;

pub(crate) const KEY_SIZE_BITS: u32 = (MAX_KEY_SIZE + 1).next_power_of_two().ilog2();
pub(crate) const VALUE_SIZE_BITS: u32 = (MAX_VALUE_SIZE + 1).next_power_of_two().ilog2();
const RECORD_HEADER_BITS: u32 = 1 + KEY_SIZE_BITS + VALUE_SIZE_BITS;
pub(crate) const RECORD_HEADER_SIZE: usize = (RECORD_HEADER_BITS as usize + 7) / 8;

/// Amount of scratch pages reserved for compaction.
///
/// Note that `ekv` already reserves a bare-minimum amount of pages to guarantee
/// compaction can always make forward progress, so it's technically fine to
/// set this to `0`. However, setting it too low can cause write amplification
/// due to having to do many smaller compactions instead of fewer larger ones, so
/// it is not recommended.
///
/// Default: 4.
pub const SCRATCH_PAGE_COUNT: usize = raw::SCRATCH_PAGE_COUNT;

// Compaction will be stopped when there's this amount of free pages left.
// We need at least one page free, in case file commit needs to write a new meta page.
// There's no point in leaving more pages.
pub(crate) const MIN_FREE_PAGE_COUNT_COMPACT: usize = 1;

const MAX_RECORD_SIZE: usize = RecordHeader {
    is_delete: false,
    key_len: MAX_KEY_SIZE,
    value_len: MAX_VALUE_SIZE,
}
.record_size();

// Compaction will be triggered when there's this amount of free pages left or less.
// The calculation here guarantees progressive compaction will never get stuck.
pub(crate) const MIN_FREE_PAGE_COUNT: usize = 1
    + SCRATCH_PAGE_COUNT
    + MIN_FREE_PAGE_COUNT_COMPACT
    + BRANCHING_FACTOR
    + (MAX_RECORD_SIZE + PAGE_MAX_PAYLOAD_SIZE - 1) / PAGE_MAX_PAYLOAD_SIZE; // ceil(MAX_RECORD_SIZE/PAGE_MAX_PAYLOAD_SIZE)

#[allow(clippy::assertions_on_constants)]
const _CHECKS: () = {
    // using core::assert to avoid using defmt, because it doesn't work in const.

    core::assert!(BRANCHING_FACTOR >= 2 && BRANCHING_FACTOR <= 4);

    // Only align 1, 2, 4 is supported for now.
    // We only align data. Header sizes are aligned to 4 but not 8.
    // Supporting higher aligns would require aligning the headers as well.
    core::assert!(ALIGN == 1 || ALIGN == 2 || ALIGN == 4);

    // assert MIN_FREE_PAGE_COUNT is reasonable.
    // If it's too big relative to the total flash size, we'll waste a lot of space!
    core::assert!(MIN_FREE_PAGE_COUNT < MAX_PAGE_COUNT / 2);

    // We use u16 for chunk sizes.
    core::assert!(PAGE_MAX_PAYLOAD_SIZE <= u16::MAX as _);

    core::assert!(MAX_KEY_SIZE > 0);
    core::assert!(MAX_VALUE_SIZE > 0);

    core::assert!(RECORD_HEADER_SIZE <= 4);

    core::assert!(MAX_CHUNK_SIZE % ALIGN == 0);
};

/// Dump the compile-time configuration to `log` or `defmt`.
///
/// Useful for seeing the active configuration, and for reporting bugs.
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
    debug!(
        "max_key_size={}, max_value_size={}, record_header_size={}, max_record_size={} ({} pages)",
        MAX_KEY_SIZE,
        MAX_VALUE_SIZE,
        MAX_RECORD_SIZE,
        RECORD_HEADER_SIZE,
        (MAX_RECORD_SIZE + PAGE_MAX_PAYLOAD_SIZE - 1) / PAGE_MAX_PAYLOAD_SIZE
    );
    debug!(
        "scratch_page_count={}, min_free_page_count={}, min_free_page_count_compact={}",
        SCRATCH_PAGE_COUNT, MIN_FREE_PAGE_COUNT, MIN_FREE_PAGE_COUNT_COMPACT
    );
}

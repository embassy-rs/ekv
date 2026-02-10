use core::marker::PhantomData;
use core::mem::size_of;

use crate::config::{self, ALIGN, ERASE_VALUE, MAX_HEADER_SIZE, PAGE_SIZE};
use crate::errors::Error;
use crate::flash::Flash;
use crate::types::PageID;

const CHUNK_MAGIC: u16 = 0x59C5;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[repr(C)]
#[cfg_attr(
    any(
        all(feature = "crc", feature = "align-8", not(feature = "align-16")),
        all(not(feature = "crc"), feature = "align-8"),
    ),
    repr(align(8))
)]
#[cfg_attr(
    any(
        all(feature = "crc", feature = "align-16"),
        all(not(feature = "crc"), feature = "align-16"),
    ),
    repr(align(16))
)]
pub struct PageHeader {
    magic: u32,
    page_id: u32,
    #[cfg(feature = "crc")]
    crc: u32,

    // Note: The repr(align(N)) attribute above automatically pads the struct
    // to ensure its size is a multiple of N. The manual padding fields below
    // are technically redundant but kept for explicitness.

    // Without CRC: 8 bytes → add 8 bytes for ALIGN=16
    #[cfg(all(not(feature = "crc"), feature = "align-16"))]
    _padding: [u8; 8],

    // With CRC: 12 bytes → add 4 bytes for ALIGN=8/16
    #[cfg(all(feature = "crc", any(feature = "align-8", feature = "align-16")))]
    _padding: [u8; 4],
}
impl_bytes!(PageHeader);

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[repr(C)]
pub struct ChunkHeader {
    magic: u16,
    len: u16,
    #[cfg(feature = "crc")]
    crc: u32,
}
impl_bytes!(ChunkHeader);

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ReadError<E> {
    Flash(E),
    Eof,
    Corrupted,
}

impl<E> From<Error<E>> for ReadError<E> {
    fn from(err: Error<E>) -> Self {
        match err {
            Error::Flash(e) => Self::Flash(e),
            Error::Corrupted => Self::Corrupted,
        }
    }
}

/// Higher-layer header.
///
/// # Safety
///
/// Must allow transmute to/from [u8;N]
pub unsafe trait Header: Sized {
    const MAGIC: u32;
}

pub(crate) const MAX_CHUNK_SIZE: usize = if config::MAX_CHUNK_SIZE > (PAGE_SIZE - PageHeader::SIZE - ChunkHeader::SIZE)
{
    PAGE_SIZE - PageHeader::SIZE - ChunkHeader::SIZE
} else {
    config::MAX_CHUNK_SIZE
};

async fn write_header<F: Flash, H: Header>(flash: &mut F, page_id: PageID, header: H) -> Result<(), F::Error> {
    assert!(size_of::<H>() <= MAX_HEADER_SIZE);
    let mut buf = [0u8; PageHeader::SIZE + MAX_HEADER_SIZE];
    let buf = &mut buf[..PageHeader::SIZE + size_of::<H>()];

    unsafe {
        buf.as_mut_ptr()
            .add(PageHeader::SIZE)
            .cast::<H>()
            .write_unaligned(header)
    };

    let page_header = PageHeader {
        magic: H::MAGIC,
        page_id: page_id.index() as u32,
        #[cfg(feature = "crc")]
        crc: crc32(&buf[PageHeader::SIZE..]),
        #[cfg(all(not(feature = "crc"), feature = "align-16"))]
        _padding: [ERASE_VALUE; 8],
        #[cfg(all(feature = "crc", any(feature = "align-8", feature = "align-16")))]
        _padding: [ERASE_VALUE; 4],
    };
    buf[..PageHeader::SIZE].copy_from_slice(&page_header.to_bytes());

    flash.write(page_id, 0, buf).await?;
    Ok(())
}

pub async fn read_header<F: Flash, H: Header>(flash: &mut F, page_id: PageID) -> Result<H, Error<F::Error>> {
    assert!(size_of::<H>() <= MAX_HEADER_SIZE);
    let mut buf = [0u8; PageHeader::SIZE + MAX_HEADER_SIZE];
    let buf = &mut buf[..PageHeader::SIZE + size_of::<H>()];

    flash.read(page_id as _, 0, buf).await.map_err(Error::Flash)?;

    let page_header = PageHeader::from_bytes(buf[..PageHeader::SIZE].try_into().unwrap());
    if page_header.magic != H::MAGIC || page_header.page_id != page_id.index() as u32 {
        // don't use `corrupted!()` here, this can happen during normal
        // operation while searching for meta pages, for mount/format.
        return Err(Error::Corrupted);
    }

    #[cfg(feature = "crc")]
    {
        let got_crc = crc32(&buf[PageHeader::SIZE..]);
        if got_crc != page_header.crc {
            return Err(Error::Corrupted);
        }
    }

    let header = unsafe { buf.as_ptr().add(PageHeader::SIZE).cast::<H>().read_unaligned() };
    Ok(header)
}

#[derive(Clone)]
struct ChunkIter {
    page_id: PageID,

    /// true if we've reached the end of the page.
    at_end: bool,
    /// sum of lengths of all previous chunks (not counting current one)
    prev_chunks_len: usize,
    /// Offset where the chunk we're currently writing starts.
    chunk_offset: usize,
    /// Data bytes in the current chunk.
    chunk_len: usize,
    /// CRC
    #[cfg(feature = "crc")]
    chunk_crc: u32,
}

impl ChunkIter {
    async fn next_chunk<F: Flash>(&mut self, flash: &mut F) -> Result<bool, Error<F::Error>> {
        // With the new packing approach, chunk size is align_up(header + data)
        self.chunk_offset += align_up(ChunkHeader::SIZE + self.chunk_len);
        self.open_chunk(flash).await
    }

    async fn open_chunk<F: Flash>(&mut self, flash: &mut F) -> Result<bool, Error<F::Error>> {
        // Read enough to get the full header (and possibly some initial data).
        // The header is now packed with data at the start of an aligned block.
        let mut buf = [0u8; align_up(ChunkHeader::SIZE)];
        if self.chunk_offset + buf.len() > PAGE_SIZE {
            // Not enough space to read the header
            self.at_end = true;
            return Ok(false);
        }
        flash
            .read(self.page_id as _, self.chunk_offset, &mut buf)
            .await
            .map_err(Error::Flash)?;

        let header = ChunkHeader::from_bytes(buf[..ChunkHeader::SIZE].try_into().unwrap());

        if header.magic != CHUNK_MAGIC {
            self.at_end = true;
            return Ok(false);
        }

        if header.len as usize > MAX_CHUNK_SIZE {
            corrupted!();
        }

        let data_start = self.chunk_offset + ChunkHeader::SIZE;
        let Some(data_end) = data_start.checked_add(header.len as usize) else {
            corrupted!();
        };

        if data_end > PAGE_SIZE {
            corrupted!();
        }

        trace!("open chunk at offs={} len={}", self.chunk_offset, header.len);

        self.chunk_len = header.len as usize;
        #[cfg(feature = "crc")]
        {
            self.chunk_crc = header.crc;
        }

        Ok(true)
    }
}

pub struct PageReader {
    ch: ChunkIter,
    /// pos within the current chunk.
    chunk_pos: usize,

    /// Data in the current chunk.
    buf: [u8; MAX_CHUNK_SIZE],
}

#[derive(Clone)]
pub struct DehydratedPageReader {
    ch: ChunkIter,
    chunk_pos: usize,
}

impl PageReader {
    pub const fn new() -> Self {
        PageReader {
            ch: ChunkIter {
                page_id: PageID::zero(),
                prev_chunks_len: 0,
                at_end: false,
                chunk_offset: 0,
                chunk_len: 0,
                #[cfg(feature = "crc")]
                chunk_crc: 0,
            },
            chunk_pos: 0,
            buf: [0u8; MAX_CHUNK_SIZE],
        }
    }

    pub fn dehydrate(&self) -> DehydratedPageReader {
        DehydratedPageReader {
            ch: self.ch.clone(),
            chunk_pos: self.chunk_pos,
        }
    }

    pub async fn rehydrate_from<F: Flash>(
        &mut self,
        flash: &mut F,
        dehydrated: &DehydratedPageReader,
    ) -> Result<(), Error<F::Error>> {
        self.ch = dehydrated.ch.clone();
        self.chunk_pos = dehydrated.chunk_pos;
        self.load_chunk(flash).await
    }

    pub async fn open<F: Flash, H: Header>(&mut self, flash: &mut F, page_id: PageID) -> Result<H, Error<F::Error>> {
        trace!("page: read {:?}", page_id);
        let header = read_header(flash, page_id).await?;

        self.ch.page_id = page_id;
        self.ch.prev_chunks_len = 0;
        self.ch.at_end = false;
        self.ch.chunk_offset = PageHeader::SIZE + size_of::<H>();
        self.ch.chunk_len = 0;
        self.ch.open_chunk(flash).await?;
        self.chunk_pos = 0;
        self.load_chunk(flash).await?;
        Ok(header)
    }

    async fn load_chunk<F: Flash>(&mut self, flash: &mut F) -> Result<(), Error<F::Error>> {
        // Layout: First align_up(ChunkHeader::SIZE) bytes contain header + initial data,
        // rest follows at chunk_offset + align_up(ChunkHeader::SIZE)
        // open_chunk() guarantees we have space for at least align_up(ChunkHeader::SIZE) bytes
        const FIRST_BLOCK_SIZE: usize = align_up(ChunkHeader::SIZE);

        // Read the first block (contains header + initial data)
        let mut first_block = [0u8; FIRST_BLOCK_SIZE];
        flash
            .read(self.ch.page_id as _, self.ch.chunk_offset, &mut first_block)
            .await
            .map_err(Error::Flash)?;

        // Extract the data portion (skip header bytes)
        let data_in_first_block = (FIRST_BLOCK_SIZE - ChunkHeader::SIZE).min(self.ch.chunk_len);
        self.buf[..data_in_first_block]
            .copy_from_slice(&first_block[ChunkHeader::SIZE..ChunkHeader::SIZE + data_in_first_block]);

        // Read remaining data if any
        if data_in_first_block < self.ch.chunk_len {
            let remaining = self.ch.chunk_len - data_in_first_block;
            let remaining_aligned = align_up(remaining);
            flash
                .read(
                    self.ch.page_id as _,
                    self.ch.chunk_offset + FIRST_BLOCK_SIZE,
                    &mut self.buf[data_in_first_block..data_in_first_block + remaining_aligned],
                )
                .await
                .map_err(Error::Flash)?;
        }

        #[cfg(feature = "crc")]
        {
            let got_crc = crc32(&self.buf[..self.ch.chunk_len]);
            if got_crc != self.ch.chunk_crc {
                return Err(Error::Corrupted);
            }
        }

        Ok(())
    }

    async fn next_chunk<F: Flash>(&mut self, flash: &mut F) -> Result<bool, Error<F::Error>> {
        if !self.ch.next_chunk(flash).await? {
            return Ok(false);
        }
        self.chunk_pos = 0;
        self.load_chunk(flash).await?;
        Ok(true)
    }

    pub fn page_id(&self) -> PageID {
        self.ch.page_id
    }

    /// Read up to data.len() bytes of data or until the end of the current chunk.
    ///
    /// May return less bytes than the buffer if not available.
    pub async fn read<F: Flash>(&mut self, flash: &mut F, data: &mut [u8]) -> Result<usize, Error<F::Error>> {
        trace!("PageReader({:?}): read({})", self.ch.page_id, data.len());
        if self.is_at_eof(flash).await? || data.is_empty() {
            trace!("read: at end or zero len");
            return Ok(0);
        }

        let n = data.len().min(self.ch.chunk_len - self.chunk_pos);
        data[..n].copy_from_slice(&self.buf[self.chunk_pos..][..n]);
        self.chunk_pos += n;
        trace!("read: done, n={}", n);
        Ok(n)
    }

    /// Skip up to len bytes in the reader or until the end of the last chunk
    ///
    /// Skips across chunks within the page.
    pub async fn skip<F: Flash>(&mut self, flash: &mut F, mut len: usize) -> Result<usize, Error<F::Error>> {
        trace!("PageReader({:?}): skip({})", self.ch.page_id, len);
        if self.ch.at_end || len == 0 {
            trace!("skip: at end or zero len");
            return Ok(0);
        }

        let start = len;
        loop {
            if self.is_at_eof(flash).await? {
                trace!("skip: no next chunk, we're at end.");
                return Ok(start - len);
            }

            let n = len.min(self.ch.chunk_len - self.chunk_pos);
            self.ch.prev_chunks_len += n;
            self.chunk_pos += n;
            len -= n;
            if len == 0 {
                trace!("skip: done, n={}", start - len);
                return Ok(start - len);
            }
        }
    }

    pub async fn is_at_eof<F: Flash>(&mut self, flash: &mut F) -> Result<bool, Error<F::Error>> {
        if self.ch.at_end {
            return Ok(true);
        }
        if self.chunk_pos == self.ch.chunk_len && !self.next_chunk(flash).await? {
            return Ok(true);
        }
        Ok(false)
    }
}

pub struct PageWriter<H: Header> {
    _phantom: PhantomData<H>,

    page_id: PageID,
    needs_erase: bool,

    #[cfg(feature = "crc")]
    crc: Crc32,
    align_buf: [u8; ALIGN],

    /// Buffer for header + first data bytes.
    /// This allows packing the header with data to avoid padding waste.
    /// Size is align_up(ChunkHeader::SIZE) to ensure we can always fit the header.
    header_buf: [u8; align_up(ChunkHeader::SIZE)],
    /// Number of data bytes currently in header_buf (not including header space).
    header_buf_len: usize,

    /// Total data bytes in page (all chunks)
    total_pos: usize,

    /// Offset where the chunk we're currently writing starts.
    chunk_offset: usize,
    /// Data bytes in the chunk we're currently writing.
    chunk_pos: usize,
}

impl<H: Header> PageWriter<H> {
    pub fn new() -> Self {
        Self {
            _phantom: PhantomData,
            page_id: PageID::from_raw(0).unwrap(),
            needs_erase: true,
            align_buf: [0; ALIGN],
            header_buf: [0; align_up(ChunkHeader::SIZE)],
            header_buf_len: 0,
            total_pos: 0,
            chunk_offset: PageHeader::SIZE + size_of::<H>(),
            chunk_pos: 0,
            #[cfg(feature = "crc")]
            crc: Crc32::new(),
        }
    }

    pub async fn open<F: Flash>(&mut self, _flash: &mut F, page_id: PageID) {
        trace!("page: write {:?}", page_id);
        self.page_id = page_id;
        self.needs_erase = true;
        self.align_buf = [0; ALIGN];
        self.header_buf = [0; align_up(ChunkHeader::SIZE)];
        self.header_buf_len = 0;
        self.total_pos = 0;
        self.chunk_offset = PageHeader::SIZE + size_of::<H>();
        self.chunk_pos = 0;
        #[cfg(feature = "crc")]
        self.crc.reset();
    }

    pub async fn open_append<F: Flash>(&mut self, flash: &mut F, page_id: PageID) -> Result<(), Error<F::Error>> {
        trace!("page: write_append {:?}", page_id);

        let mut r = ChunkIter {
            page_id,
            prev_chunks_len: 0,
            at_end: false,
            chunk_offset: PageHeader::SIZE + size_of::<H>(),
            chunk_len: 0,
            #[cfg(feature = "crc")]
            chunk_crc: 0,
        };
        r.open_chunk(flash).await?;
        while !r.at_end {
            r.next_chunk(flash).await?;
        }

        // Check all space after `r.chunk_offset` is erased.
        if r.chunk_offset != PAGE_SIZE {
            const CHUNK_LEN: usize = 128;
            let mut buf = [ERASE_VALUE; CHUNK_LEN];

            let mut ok = true;
            for start in (r.chunk_offset..PAGE_SIZE).step_by(CHUNK_LEN) {
                let end = (start + CHUNK_LEN).min(PAGE_SIZE);
                let len = end - start;
                flash
                    .read(page_id as _, start, &mut buf[..len])
                    .await
                    .map_err(Error::Flash)?;
                if !buf[..len].iter().all(|&x| x == ERASE_VALUE) {
                    ok = false;
                    break;
                }
            }

            if !ok {
                // setting this will make the writer fail writing as if the page was full.
                r.chunk_offset = PAGE_SIZE;
            }
        }

        self.page_id = page_id;
        self.needs_erase = false;
        self.align_buf = [0; ALIGN];
        self.header_buf = [0; align_up(ChunkHeader::SIZE)];
        self.header_buf_len = 0;
        self.total_pos = r.prev_chunks_len;
        self.chunk_offset = r.chunk_offset;
        self.chunk_pos = 0;
        #[cfg(feature = "crc")]
        self.crc.reset();

        Ok(())
    }

    #[allow(clippy::len_without_is_empty)]
    pub fn len(&self) -> usize {
        self.total_pos
    }

    pub fn page_id(&self) -> PageID {
        self.page_id
    }

    fn is_chunk_full(&self) -> bool {
        self.chunk_pos >= MAX_CHUNK_SIZE
    }

    /// Write n bytes of data to the page.
    ///
    /// If the current chunk is full, it will commit it.
    pub async fn write<F: Flash>(&mut self, flash: &mut F, data: &[u8]) -> Result<usize, Error<F::Error>> {
        // Calculate available space in the page.
        // The current chunk will occupy: align_up(ChunkHeader::SIZE + chunk_pos + new_data) bytes.
        // This must fit within: PAGE_SIZE - chunk_offset.
        // To maximize space usage: ChunkHeader::SIZE + chunk_pos + new_data <= align_down(PAGE_SIZE - chunk_offset)
        // where align_down(x) is the largest multiple of ALIGN that is <= x.
        let available_space = PAGE_SIZE.saturating_sub(self.chunk_offset);
        let aligned_space = available_space - (available_space % ALIGN);
        let max_write = aligned_space
            .saturating_sub(ChunkHeader::SIZE)
            .saturating_sub(self.chunk_pos)
            .min(MAX_CHUNK_SIZE.saturating_sub(self.chunk_pos));
        let total_n = data.len().min(max_write);
        if total_n == 0 {
            return Ok(0);
        }
        let mut data = &data[..total_n];

        #[cfg(feature = "crc")]
        self.crc.update(data);

        self.erase_if_needed(flash).await.map_err(Error::Flash)?;

        // First, fill header_buf with initial data bytes.
        // header_buf will be written together with the header at commit time.
        // Buffer up to (align_up(ChunkHeader::SIZE) - ChunkHeader::SIZE) bytes.
        const FIRST_BLOCK_SIZE: usize = align_up(ChunkHeader::SIZE);
        let header_buf_capacity = FIRST_BLOCK_SIZE - ChunkHeader::SIZE;
        if self.header_buf_len < header_buf_capacity {
            let n = (header_buf_capacity - self.header_buf_len).min(data.len());
            self.header_buf[ChunkHeader::SIZE + self.header_buf_len..][..n].copy_from_slice(&data[..n]);
            self.header_buf_len += n;
            data = &data[n..];
            self.total_pos += n;
            self.chunk_pos += n;
        }

        // Now handle the remaining data that goes after the header buffer.
        // This data is written starting at (chunk_offset + FIRST_BLOCK_SIZE).
        // The position within this region is (chunk_pos - header_buf_len).

        let data_offset_in_region = (self.chunk_pos - self.header_buf_len) % ALIGN;
        if data_offset_in_region != 0 {
            let left = ALIGN - data_offset_in_region;
            let n = left.min(data.len());

            self.align_buf[data_offset_in_region..][..n].copy_from_slice(&data[..n]);
            data = &data[n..];
            self.total_pos += n;
            self.chunk_pos += n;

            if n == left {
                // Write the completed align_buf
                let flash_offset =
                    self.chunk_offset + FIRST_BLOCK_SIZE + (self.chunk_pos - self.header_buf_len - ALIGN);
                flash
                    .write(self.page_id as _, flash_offset, &self.align_buf)
                    .await
                    .map_err(Error::Flash)?;
            }
        }

        // Write aligned portion
        let n = data.len() - (data.len() % ALIGN);
        if n != 0 {
            let flash_offset = self.chunk_offset + FIRST_BLOCK_SIZE + (self.chunk_pos - self.header_buf_len);
            flash
                .write(self.page_id as _, flash_offset, &data[..n])
                .await
                .map_err(Error::Flash)?;
            data = &data[n..];
            self.total_pos += n;
            self.chunk_pos += n;
        }

        // Buffer remaining unaligned bytes
        let n = data.len();
        assert!(n < ALIGN);
        self.align_buf[..n].copy_from_slice(data);
        self.total_pos += n;
        self.chunk_pos += n;

        if self.is_chunk_full() {
            self.commit(flash).await?;
        }

        Ok(total_n)
    }

    async fn erase_if_needed<F: Flash>(&mut self, flash: &mut F) -> Result<(), F::Error> {
        if self.needs_erase {
            flash.erase(self.page_id as _).await?;
            self.needs_erase = false;
        }
        Ok(())
    }

    pub async fn write_header<F: Flash>(&mut self, flash: &mut F, header: H) -> Result<(), F::Error> {
        self.erase_if_needed(flash).await?;

        write_header(flash, self.page_id, header).await?;

        Ok(())
    }

    pub async fn commit<F: Flash>(&mut self, flash: &mut F) -> Result<(), Error<F::Error>> {
        if self.chunk_pos == 0 {
            // nothing to commit.
            return Ok(());
        }
        self.erase_if_needed(flash).await.map_err(Error::Flash)?;

        // Flush any remaining data in align_buf (data after header_buf).
        const FIRST_BLOCK_SIZE: usize = align_up(ChunkHeader::SIZE);
        let data_after_header_buf = self.chunk_pos - self.header_buf_len;
        let align_offs = data_after_header_buf % ALIGN;
        if align_offs != 0 {
            let flash_offset = self.chunk_offset + FIRST_BLOCK_SIZE + data_after_header_buf - align_offs;
            flash
                .write(self.page_id as _, flash_offset, &self.align_buf)
                .await
                .map_err(Error::Flash)?;
        }

        // Create the chunk header.
        let h = ChunkHeader {
            magic: CHUNK_MAGIC,
            len: self.chunk_pos as u16,
            #[cfg(feature = "crc")]
            crc: self.crc.finish(),
        };

        // Copy header bytes into the beginning of header_buf.
        let header_bytes = h.to_bytes();
        self.header_buf[..ChunkHeader::SIZE].copy_from_slice(&header_bytes);

        // Pad header_buf to ALIGN if needed.
        let header_plus_data_len = ChunkHeader::SIZE + self.header_buf_len;
        let aligned_len = if header_plus_data_len % ALIGN != 0 {
            header_plus_data_len + ALIGN - (header_plus_data_len % ALIGN)
        } else {
            header_plus_data_len
        };

        // Write the header_buf (header + initial data bytes, padded to ALIGN).
        flash
            .write(self.page_id as _, self.chunk_offset, &self.header_buf[..aligned_len])
            .await
            .map_err(Error::Flash)?;

        // Prepare for next chunk.
        // Total chunk size is now: align_up(ChunkHeader::SIZE + chunk_pos)
        self.chunk_offset += align_up(ChunkHeader::SIZE + self.chunk_pos);
        self.chunk_pos = 0;
        self.header_buf_len = 0;
        self.header_buf = [0; align_up(ChunkHeader::SIZE)];
        #[cfg(feature = "crc")]
        self.crc.reset();

        Ok(())
    }
}

pub const fn align_up(n: usize) -> usize {
    if n % ALIGN != 0 {
        n + ALIGN - n % ALIGN
    } else {
        n
    }
}

#[allow(unused)]
#[derive(Clone, Copy)]
struct Crc32 {
    crc: u32,
}

#[allow(unused)]
impl Crc32 {
    fn new() -> Self {
        Self { crc: 0xffffffff }
    }

    fn reset(&mut self) {
        self.crc = 0xffffffff;
    }

    // TODO: use a faster implementation. Probably a 4-bit lookup table (16 entries),
    // because the usual 8-bit look up table (256 entries) is quite big (1kb).
    fn update(&mut self, data: &[u8]) {
        let mut crc = self.crc;
        for &b in data {
            crc ^= b as u32;
            for _ in 0..8 {
                if crc & 1 != 0 {
                    crc = crc >> 1 ^ 0xedb88320;
                } else {
                    crc >>= 1;
                }
            }
        }
        self.crc = crc
    }

    fn finish(self) -> u32 {
        !self.crc
    }
}

#[allow(unused)]
fn crc32(data: &[u8]) -> u32 {
    let mut crc = Crc32::new();
    crc.update(data);
    crc.finish()
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::flash::MemFlash;

    const PAGE: PageID = match PageID::from_raw(0) {
        Some(x) => x,
        None => panic!("none"),
    };

    #[derive(Clone, Copy, PartialEq, Eq, Debug)]
    #[repr(C)]
    #[cfg_attr(feature = "align-8", repr(align(8)))]
    #[cfg_attr(feature = "align-16", repr(align(16)))]
    pub struct TestHeader {
        foo: u32,

        // Note: repr(align) ensures proper alignment; manual padding for explicitness
        #[cfg(feature = "align-8")]
        _padding: [u8; 4],
        #[cfg(feature = "align-16")]
        _padding: [u8; 12],
    }

    unsafe impl Header for TestHeader {
        const MAGIC: u32 = 0x470b635c;
    }

    const HEADER: TestHeader = TestHeader {
        foo: 123456,
        #[cfg(feature = "align-8")]
        _padding: [0; 4],
        #[cfg(feature = "align-16")]
        _padding: [0; 12],
    };
    const MAX_PAYLOAD: usize = PAGE_SIZE - PageHeader::SIZE - size_of::<TestHeader>() - ChunkHeader::SIZE;

    #[test_log::test]
    fn test_crc32() {
        assert_eq!(crc32(b""), 0x00000000);
        assert_eq!(crc32(b"a"), 0xE8B7BE43);
        assert_eq!(crc32(b"Hello World!"), 0x1C291CA3);
    }

    #[test_log::test(tokio::test)]
    async fn test_header() {
        let f = &mut MemFlash::new();

        write_header(f, PAGE, HEADER).await.unwrap();
        let h = read_header::<_, TestHeader>(f, PAGE).await.unwrap();
        assert_eq!(h, HEADER)
    }

    #[test_log::test(tokio::test)]
    async fn test_header_read_unwritten() {
        let f = &mut MemFlash::new();

        let res = read_header::<_, TestHeader>(f, PAGE).await;
        assert!(matches!(res, Err(Error::Corrupted)))
    }

    #[test_log::test(tokio::test)]
    async fn test_read_unwritten() {
        let f = &mut MemFlash::new();

        // Read
        let mut r = PageReader::new();
        let res = r.open::<_, TestHeader>(f, PAGE).await;
        assert!(matches!(res, Err(Error::Corrupted)));
    }

    #[test_log::test(tokio::test)]
    async fn test_read_uncommitted() {
        let f = &mut MemFlash::new();

        let data = dummy_data(13);

        // Write
        let mut w: PageWriter<TestHeader> = PageWriter::new();
        w.open(f, PAGE).await;
        w.write(f, &data).await.unwrap();
        // don't commit

        // Read
        let mut r = PageReader::new();
        let res = r.open::<_, TestHeader>(f, PAGE).await;
        assert!(matches!(res, Err(Error::Corrupted)));
    }

    #[test_log::test(tokio::test)]
    async fn test_write_short() {
        let f = &mut MemFlash::new();

        let data = dummy_data(13);

        // Write
        let mut w = PageWriter::new();
        w.open(f, PAGE).await;
        let n = w.write(f, &data).await.unwrap();
        assert_eq!(n, 13);
        w.write_header(f, HEADER).await.unwrap();
        w.commit(f).await.unwrap();

        // Read
        let mut r = PageReader::new();
        let h = r.open::<_, TestHeader>(f, PAGE).await.unwrap();
        assert_eq!(h, HEADER);
        let mut buf = vec![0; data.len()];
        let n = r.read(f, &mut buf).await.unwrap();
        assert_eq!(n, 13);
        assert_eq!(data, buf);

        // Remount

        // Read
        let mut r = PageReader::new();
        let h = r.open::<_, TestHeader>(f, PAGE).await.unwrap();
        assert_eq!(h, HEADER);
        let mut buf = vec![0; data.len()];
        let n = r.read(f, &mut buf).await.unwrap();
        assert_eq!(n, 13);
        assert_eq!(data, buf);
    }

    #[test_log::test(tokio::test)]
    async fn test_overread() {
        let f = &mut MemFlash::new();

        let data = dummy_data(13);

        // Write
        let mut w = PageWriter::new();
        w.open(f, PAGE).await;
        w.write(f, &data).await.unwrap();
        w.write_header(f, HEADER).await.unwrap();
        w.commit(f).await.unwrap();

        // Read
        let mut r = PageReader::new();
        let h = r.open::<_, TestHeader>(f, PAGE).await.unwrap();
        assert_eq!(h, HEADER);
        let mut buf = vec![0; 1024];
        let n = r.read(f, &mut buf).await.unwrap();
        assert_eq!(n, 13);
        assert_eq!(data, buf[..13]);
    }

    #[test_log::test(tokio::test)]
    async fn test_overwrite() {
        let f = &mut MemFlash::new();

        let data = dummy_data(65536);

        // Write
        let mut w = PageWriter::new();
        w.open(f, PAGE).await;
        let mut total = 0;
        let mut writes = 0;
        while total < data.len() {
            let n = w.write(f, &data[total..]).await.unwrap();
            if n == 0 {
                break;
            }
            total += n;
            writes += 1;
        }

        let expected = PAGE_SIZE - PageHeader::SIZE - size_of::<TestHeader>() - (ChunkHeader::SIZE * writes);
        assert_eq!(total, expected, "writes: {}", writes);
        w.write_header(f, HEADER).await.unwrap();
        w.commit(f).await.unwrap();

        // Read
        let mut r = PageReader::new();
        let h = r.open::<_, TestHeader>(f, PAGE).await.unwrap();
        assert_eq!(h, HEADER);
        let mut buf = vec![];
        loop {
            let mut chunk = [0u8; MAX_CHUNK_SIZE];
            let n = r.read(f, &mut chunk).await.unwrap();
            if n == 0 {
                break;
            }
            buf.extend_from_slice(&chunk[..n]);
        }
        assert_eq!(buf.len(), expected);
        assert_eq!(data[..13], buf[..13]);
    }

    #[test_log::test(tokio::test)]
    async fn test_write_many() {
        let f = &mut MemFlash::new();

        // Write
        let mut w = PageWriter::new();
        w.open(f, PAGE).await;
        let n = w.write(f, &[1, 2, 3]).await.unwrap();
        assert_eq!(n, 3);
        let n = w.write(f, &[4, 5, 6, 7, 8, 9]).await.unwrap();
        assert_eq!(n, 6);
        w.write_header(f, HEADER).await.unwrap();
        w.commit(f).await.unwrap();

        // Read
        let mut r = PageReader::new();
        let h = r.open::<_, TestHeader>(f, PAGE).await.unwrap();
        assert_eq!(h, HEADER);
        let mut buf = vec![0; MAX_PAYLOAD];
        let n = r.read(f, &mut buf).await.unwrap();
        assert_eq!(n, 9);
        assert_eq!(buf[..9], [1, 2, 3, 4, 5, 6, 7, 8, 9]);
    }

    #[test_log::test(tokio::test)]
    async fn test_read_many() {
        let f = &mut MemFlash::new();

        // Write
        let mut w = PageWriter::new();
        w.open(f, PAGE).await;
        let n = w.write(f, &[1, 2, 3, 4, 5, 6, 7, 8, 9]).await.unwrap();
        assert_eq!(n, 9);
        w.write_header(f, HEADER).await.unwrap();
        w.commit(f).await.unwrap();

        // Read
        let mut r = PageReader::new();
        let h = r.open::<_, TestHeader>(f, PAGE).await.unwrap();
        assert_eq!(h, HEADER);
        let mut buf = vec![0; MAX_PAYLOAD];

        let n = r.read(f, &mut buf[..3]).await.unwrap();
        assert_eq!(n, 3);
        assert_eq!(buf[..3], [1, 2, 3]);

        let n = r.read(f, &mut buf).await.unwrap();
        assert_eq!(n, 6);
        assert_eq!(buf[..6], [4, 5, 6, 7, 8, 9]);

        let n = r.read(f, &mut buf).await.unwrap();
        assert_eq!(n, 0);
    }

    #[test_log::test(tokio::test)]
    async fn test_multichunk() {
        let f = &mut MemFlash::new();

        // Write
        let mut w = PageWriter::new();
        w.open(f, PAGE).await;
        let n = w.write(f, &[1, 2, 3, 4, 5, 6, 7, 8, 9]).await.unwrap();
        assert_eq!(n, 9);
        w.write_header(f, HEADER).await.unwrap();
        w.commit(f).await.unwrap();
        let n = w.write(f, &[10, 11, 12]).await.unwrap();
        assert_eq!(n, 3);
        w.commit(f).await.unwrap();

        // Read
        let mut r = PageReader::new();
        let h = r.open::<_, TestHeader>(f, PAGE).await.unwrap();
        assert_eq!(h, HEADER);
        let mut buf = vec![0; MAX_PAYLOAD];

        let n = r.read(f, &mut buf[..3]).await.unwrap();
        assert_eq!(n, 3);
        assert_eq!(buf[..3], [1, 2, 3]);

        let n = r.read(f, &mut buf).await.unwrap();
        assert_eq!(n, 6);
        assert_eq!(buf[..6], [4, 5, 6, 7, 8, 9]);

        let n = r.read(f, &mut buf).await.unwrap();
        assert_eq!(n, 3);
        assert_eq!(buf[..3], [10, 11, 12]);

        let n = r.read(f, &mut buf).await.unwrap();
        assert_eq!(n, 0);
    }

    #[test_log::test(tokio::test)]
    async fn test_multichunk_no_commit() {
        let f = &mut MemFlash::new();

        // Write
        let mut w = PageWriter::new();
        w.open(f, PAGE).await;
        let n = w.write(f, &[1, 2, 3, 4, 5, 6, 7, 8, 9]).await.unwrap();
        assert_eq!(n, 9);
        w.write_header(f, HEADER).await.unwrap();
        w.commit(f).await.unwrap();
        let n = w.write(f, &[10, 11, 12]).await.unwrap();
        assert_eq!(n, 3);
        // no commit!

        // Read
        let mut r = PageReader::new();
        let h = r.open::<_, TestHeader>(f, PAGE).await.unwrap();
        assert_eq!(h, HEADER);
        let mut buf = vec![0; MAX_PAYLOAD];

        let n = r.read(f, &mut buf).await.unwrap();
        assert_eq!(n, 9);
        assert_eq!(buf[..9], [1, 2, 3, 4, 5, 6, 7, 8, 9]);

        let n = r.read(f, &mut buf).await.unwrap();
        assert_eq!(n, 0);
    }

    #[test_log::test(tokio::test)]
    async fn test_multichunk_append() {
        let f = &mut MemFlash::new();

        // Write
        let mut w = PageWriter::new();
        w.open(f, PAGE).await;
        let n = w.write(f, &[1, 2, 3, 4, 5, 6, 7, 8, 9]).await.unwrap();
        assert_eq!(n, 9);
        w.write_header(f, HEADER).await.unwrap();
        w.commit(f).await.unwrap();

        w.open_append(f, PAGE).await.unwrap();
        let n = w.write(f, &[10, 11, 12]).await.unwrap();
        assert_eq!(n, 3);
        w.commit(f).await.unwrap();

        // Read
        let mut r = PageReader::new();
        let h = r.open::<_, TestHeader>(f, PAGE).await.unwrap();
        assert_eq!(h, HEADER);
        let mut buf = vec![0; MAX_PAYLOAD];

        let n = r.read(f, &mut buf).await.unwrap();
        assert_eq!(n, 9);
        assert_eq!(buf[..9], [1, 2, 3, 4, 5, 6, 7, 8, 9]);

        let n = r.read(f, &mut buf).await.unwrap();
        assert_eq!(n, 3);
        assert_eq!(buf[..3], [10, 11, 12]);

        let n = r.read(f, &mut buf).await.unwrap();
        assert_eq!(n, 0);
    }

    #[test_log::test(tokio::test)]
    async fn test_multichunk_append_no_commit() {
        let f = &mut MemFlash::new();

        // Write
        let mut w = PageWriter::new();
        w.open(f, PAGE).await;
        let n = w.write(f, &[1, 2, 3, 4, 5, 6, 7, 8, 9]).await.unwrap();
        assert_eq!(n, 9);
        w.write_header(f, HEADER).await.unwrap();
        w.commit(f).await.unwrap();

        w.open_append(f, PAGE).await.unwrap();
        let n = w.write(f, &[10, 11, 12]).await.unwrap();
        assert_eq!(n, 3);
        // no commit!

        // Read
        let mut r = PageReader::new();
        let h = r.open::<_, TestHeader>(f, PAGE).await.unwrap();
        assert_eq!(h, HEADER);
        let mut buf = vec![0; MAX_PAYLOAD];

        let n = r.read(f, &mut buf).await.unwrap();
        assert_eq!(n, 9);
        assert_eq!(buf[..9], [1, 2, 3, 4, 5, 6, 7, 8, 9]);

        let n = r.read(f, &mut buf).await.unwrap();
        assert_eq!(n, 0);
    }

    #[test_log::test(tokio::test)]
    #[cfg(not(any(feature = "align-8", feature = "align-16")))]
    async fn test_multichunk_append_no_commit_then_retry() {
        let f = &mut MemFlash::new();

        // Write
        let mut w = PageWriter::new();
        w.open(f, PAGE).await;
        let n = w.write(f, &[1, 2, 3, 4, 5, 6, 7, 8, 9]).await.unwrap();
        assert_eq!(n, 9);
        w.write_header(f, HEADER).await.unwrap();
        w.commit(f).await.unwrap();

        // Append but don't commit
        w.open_append(f, PAGE).await.unwrap();
        let n = w.write(f, &[10, 11, 12, 13, 14, 15]).await.unwrap();
        assert_eq!(n, 6);
        // no commit!

        // Even though we didn't commit the appended stuff, it did get written to flash.
        // If there's "left over garbage" we can non longer append to this page. It must
        // behave as if it was full.
        w.open_append(f, PAGE).await.unwrap();
        let n = w.write(f, &[13, 14, 15]).await.unwrap();
        assert_eq!(n, 0);

        // Read
        let mut r = PageReader::new();
        let h = r.open::<_, TestHeader>(f, PAGE).await.unwrap();
        assert_eq!(h, HEADER);
        let mut buf = vec![0; MAX_PAYLOAD];

        let n = r.read(f, &mut buf).await.unwrap();
        assert_eq!(n, 9);
        assert_eq!(buf[..9], [1, 2, 3, 4, 5, 6, 7, 8, 9]);

        let n = r.read(f, &mut buf).await.unwrap();
        assert_eq!(n, 0);
    }

    #[test_log::test(tokio::test)]
    #[cfg(feature = "align-16")]
    async fn test_multichunk_append_no_commit_then_retry_align16() {
        let f = &mut MemFlash::new();

        // Write
        let mut w = PageWriter::new();
        w.open(f, PAGE).await;
        let n = w.write(f, &[1, 2, 3, 4, 5, 6, 7, 8, 9]).await.unwrap();
        assert_eq!(n, 9);
        w.write_header(f, HEADER).await.unwrap();
        w.commit(f).await.unwrap();

        // Test 1: Small uncommitted write (fits in header_buf)
        // With align-16, header_buf_capacity = align_up(ChunkHeader::SIZE) - ChunkHeader::SIZE
        //                                     = 16 - 6 = 10 bytes
        // A 6-byte write fits entirely in header_buf and leaves no garbage in flash.
        w.open_append(f, PAGE).await.unwrap();
        let n = w.write(f, &[10, 11, 12, 13, 14, 15]).await.unwrap();
        assert_eq!(n, 6);
        // no commit!

        // Since the write was fully buffered, no garbage was written to flash.
        // open_append should succeed and allow more writes.
        w.open_append(f, PAGE).await.unwrap();
        let n = w.write(f, &[16, 17, 18]).await.unwrap();
        assert!(n > 0, "Should allow writing after small uncommitted write");

        // Test 2: Larger uncommitted write (exceeds header_buf)
        // Write more than 10 bytes so it writes to flash beyond header_buf.
        const PAGE2: PageID = match PageID::from_raw(1) {
            Some(p) => p,
            None => panic!(),
        };

        let mut w2 = PageWriter::new();
        w2.open(f, PAGE2).await;
        let n = w2.write(f, &[1, 2, 3, 4, 5]).await.unwrap();
        assert_eq!(n, 5);
        w2.write_header(f, HEADER).await.unwrap();
        w2.commit(f).await.unwrap();

        w2.open_append(f, PAGE2).await.unwrap();
        // Write 30 bytes - more than header_buf_capacity (10) + ALIGN (16)
        // This ensures data is written to flash beyond the buffering.
        let large_data = [
            10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36,
            37, 38, 39,
        ];
        let n = w2.write(f, &large_data).await.unwrap();
        assert_eq!(n, 30);
        // no commit!

        // This larger write should have written data to flash beyond header_buf,
        // leaving detectable garbage. Retry should fail.
        w2.open_append(f, PAGE2).await.unwrap();
        let n = w2.write(f, &[22, 23, 24]).await.unwrap();
        assert_eq!(n, 0, "Should not allow writing after large uncommitted write");

        // Verify original committed data is still readable
        let mut r = PageReader::new();
        let h = r.open::<_, TestHeader>(f, PAGE).await.unwrap();
        assert_eq!(h, HEADER);
        let mut buf = vec![0; MAX_PAYLOAD];

        let n = r.read(f, &mut buf).await.unwrap();
        assert_eq!(n, 9);
        assert_eq!(buf[..9], [1, 2, 3, 4, 5, 6, 7, 8, 9]);

        let n = r.read(f, &mut buf).await.unwrap();
        assert_eq!(n, 0);
    }

    #[test_log::test(tokio::test)]
    async fn test_hydration() {
        let f = &mut MemFlash::new();

        // Write
        let mut w = PageWriter::new();
        w.open(f, PAGE).await;
        let n = w
            .write(f, &[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17])
            .await
            .unwrap();
        assert_eq!(n, 17);
        w.write_header(f, HEADER).await.unwrap();
        w.commit(f).await.unwrap();

        // Read
        let mut r = PageReader::new();
        let h = r.open::<_, TestHeader>(f, PAGE).await.unwrap();
        assert_eq!(h, HEADER);
        let mut buf = vec![0; MAX_PAYLOAD];

        let dehydrated_start = r.dehydrate();

        let n = r.read(f, &mut buf[..5]).await.unwrap();
        assert_eq!(n, 5);
        assert_eq!(buf[..5], [1, 2, 3, 4, 5]);

        let dehydrated_middle = r.dehydrate();

        let n = r.read(f, &mut buf).await.unwrap();
        assert_eq!(n, 12);
        assert_eq!(buf[..12], [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]);

        let dehydrated_end = r.dehydrate();

        let n = r.read(f, &mut buf).await.unwrap();
        assert_eq!(n, 0);

        r.rehydrate_from(f, &dehydrated_start).await.unwrap();
        let n = r.read(f, &mut buf).await.unwrap();
        assert_eq!(n, 17);
        assert_eq!(buf[..17], [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]);

        r.rehydrate_from(f, &dehydrated_middle).await.unwrap();
        let n = r.read(f, &mut buf).await.unwrap();
        assert_eq!(n, 12);
        assert_eq!(buf[..12], [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]);
        let n = r.read(f, &mut buf).await.unwrap();
        assert_eq!(n, 0);

        r.rehydrate_from(f, &dehydrated_end).await.unwrap();
        let n = r.read(f, &mut buf).await.unwrap();
        assert_eq!(n, 0);
    }

    #[test_log::test(tokio::test)]
    async fn test_hydration_multichunk() {
        let f = &mut MemFlash::new();

        // Write
        let mut w = PageWriter::new();
        w.open(f, PAGE).await;
        let n = w.write(f, &[1, 2, 3, 4, 5, 6, 7, 8, 9]).await.unwrap();
        assert_eq!(n, 9);
        w.write_header(f, HEADER).await.unwrap();
        w.commit(f).await.unwrap();

        w.open_append(f, PAGE).await.unwrap();
        let n = w.write(f, &[10, 11, 12, 13, 14, 15, 16, 17]).await.unwrap();
        assert_eq!(n, 8);
        w.commit(f).await.unwrap();

        // Read
        let mut r = PageReader::new();
        let h = r.open::<_, TestHeader>(f, PAGE).await.unwrap();
        assert_eq!(h, HEADER);
        let mut buf = vec![0; MAX_PAYLOAD];

        let dehydrated_start = r.dehydrate();

        let n = r.read(f, &mut buf[..5]).await.unwrap();
        assert_eq!(n, 5);
        assert_eq!(buf[..5], [1, 2, 3, 4, 5]);

        let dehydrated_middle_chunk1 = r.dehydrate();

        let n = r.read(f, &mut buf).await.unwrap();
        assert_eq!(n, 4);
        assert_eq!(buf[..4], [6, 7, 8, 9]);

        let dehydrated_middle = r.dehydrate();

        let n = r.read(f, &mut buf[..4]).await.unwrap();
        assert_eq!(n, 4);
        assert_eq!(buf[..4], [10, 11, 12, 13]);

        let dehydrated_middle_chunk2 = r.dehydrate();

        let n = r.read(f, &mut buf).await.unwrap();
        assert_eq!(n, 4);
        assert_eq!(buf[..4], [14, 15, 16, 17]);

        let dehydrated_end = r.dehydrate();

        let n = r.read(f, &mut buf).await.unwrap();
        assert_eq!(n, 0);

        r.rehydrate_from(f, &dehydrated_start).await.unwrap();
        let n = r.read(f, &mut buf).await.unwrap();
        assert_eq!(n, 9);
        assert_eq!(buf[..9], [1, 2, 3, 4, 5, 6, 7, 8, 9]);
        let n = r.read(f, &mut buf).await.unwrap();
        assert_eq!(n, 8);
        assert_eq!(buf[..8], [10, 11, 12, 13, 14, 15, 16, 17]);
        let n = r.read(f, &mut buf).await.unwrap();
        assert_eq!(n, 0);

        r.rehydrate_from(f, &dehydrated_middle_chunk1).await.unwrap();
        let n = r.read(f, &mut buf).await.unwrap();
        assert_eq!(n, 4);
        assert_eq!(buf[..4], [6, 7, 8, 9]);
        let n = r.read(f, &mut buf).await.unwrap();
        assert_eq!(n, 8);
        assert_eq!(buf[..8], [10, 11, 12, 13, 14, 15, 16, 17]);
        let n = r.read(f, &mut buf).await.unwrap();
        assert_eq!(n, 0);

        r.rehydrate_from(f, &dehydrated_middle).await.unwrap();
        let n = r.read(f, &mut buf).await.unwrap();
        assert_eq!(n, 8);
        assert_eq!(buf[..8], [10, 11, 12, 13, 14, 15, 16, 17]);
        let n = r.read(f, &mut buf).await.unwrap();
        assert_eq!(n, 0);

        r.rehydrate_from(f, &dehydrated_middle_chunk2).await.unwrap();
        let n = r.read(f, &mut buf).await.unwrap();
        assert_eq!(n, 4);
        assert_eq!(buf[..4], [14, 15, 16, 17]);
        let n = r.read(f, &mut buf).await.unwrap();
        assert_eq!(n, 0);

        r.rehydrate_from(f, &dehydrated_end).await.unwrap();
        let n = r.read(f, &mut buf).await.unwrap();
        assert_eq!(n, 0);
    }

    #[test]
    fn test_header_alignment() {
        use core::mem::size_of;
        assert_eq!(size_of::<PageHeader>() % ALIGN, 0, "PageHeader not aligned to ALIGN");
    }

    #[test]
    fn test_chunk_offset_alignment() {
        use core::mem::size_of;

        use crate::file::{DataHeader, MetaHeader};

        // MetaHeader
        let meta_offset = PageHeader::SIZE + size_of::<MetaHeader>();
        assert_eq!(meta_offset % ALIGN, 0, "First chunk offset not aligned for MetaHeader");

        // DataHeader
        let data_offset = PageHeader::SIZE + size_of::<DataHeader>();
        assert_eq!(data_offset % ALIGN, 0, "First chunk offset not aligned for DataHeader");
    }

    fn dummy_data(len: usize) -> Vec<u8> {
        let mut res = vec![0; len];
        for (i, v) in res.iter_mut().enumerate() {
            *v = i as u8 ^ (i >> 8) as u8 ^ (i >> 16) as u8 ^ (i >> 24) as u8;
        }
        res
    }
}

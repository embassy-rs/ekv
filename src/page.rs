use core::marker::PhantomData;
use core::mem::size_of;

use crate::config::*;
use crate::flash::Flash;
use crate::types::PageID;
use crate::Error;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[repr(C)]
pub struct PageHeader {
    magic: u32,
}
impl_bytes!(PageHeader);

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[repr(C)]
pub struct ChunkHeader {
    len: u32,
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

pub const MAX_CHUNK_SIZE: usize = PAGE_SIZE - PageHeader::SIZE - ChunkHeader::SIZE;

pub struct PageManager<F: Flash> {
    _phantom: PhantomData<F>,
}

impl<F: Flash> PageManager<F> {
    pub fn new() -> Self {
        Self { _phantom: PhantomData }
    }

    async fn write_header<H: Header>(flash: &mut F, page_id: PageID, header: H) -> Result<(), Error<F::Error>> {
        assert!(size_of::<H>() <= MAX_HEADER_SIZE);
        let mut buf = [0u8; PageHeader::SIZE + MAX_HEADER_SIZE];
        let buf = &mut buf[..PageHeader::SIZE + size_of::<H>()];

        let page_header = PageHeader { magic: H::MAGIC };
        buf[..PageHeader::SIZE].copy_from_slice(&page_header.to_bytes());
        unsafe {
            buf.as_mut_ptr()
                .add(PageHeader::SIZE)
                .cast::<H>()
                .write_unaligned(header)
        };

        flash.write(page_id as _, 0, buf).await.map_err(Error::Flash)?;
        Ok(())
    }

    pub async fn read_header<H: Header>(&mut self, flash: &mut F, page_id: PageID) -> Result<H, Error<F::Error>> {
        assert!(size_of::<H>() <= MAX_HEADER_SIZE);
        let mut buf = [0u8; PageHeader::SIZE + MAX_HEADER_SIZE];
        let buf = &mut buf[..PageHeader::SIZE + size_of::<H>()];

        flash.read(page_id as _, 0, buf).await.map_err(Error::Flash)?;

        let page_header = PageHeader::from_bytes(buf[..PageHeader::SIZE].try_into().unwrap());
        if page_header.magic != H::MAGIC {
            // don't use `corrupted!()` here, this can happen during normal
            // operation while searching for meta pages, for mount/format.
            return Err(Error::Corrupted);
        }

        let header = unsafe { buf.as_ptr().add(PageHeader::SIZE).cast::<H>().read_unaligned() };
        Ok(header)
    }

    pub async fn read<H: Header>(
        &mut self,
        flash: &mut F,
        page_id: PageID,
    ) -> Result<(H, PageReader), Error<F::Error>> {
        trace!("page: read {:?}", page_id);
        let header = self.read_header(flash, page_id).await?;
        let mut r = PageReader {
            page_id,
            prev_chunks_len: 0,
            at_end: false,
            chunk_offset: PageHeader::SIZE + size_of::<H>(),
            chunk_len: 0,
            chunk_pos: 0,
            buf: [0u8; MAX_CHUNK_SIZE],
        };
        r.open_chunk(flash).await?;
        Ok((header, r))
    }

    pub async fn write<H: Header>(&mut self, _flash: &mut F, page_id: PageID) -> PageWriter<H> {
        trace!("page: write {:?}", page_id);
        PageWriter {
            _phantom: PhantomData,
            page_id,
            needs_erase: true,
            align_buf: [0; WRITE_SIZE],
            total_pos: 0,
            chunk_offset: PageHeader::SIZE + size_of::<H>(),
            chunk_pos: 0,
        }
    }

    pub async fn write_append<H: Header>(
        &mut self,
        flash: &mut F,
        page_id: PageID,
    ) -> Result<(H, PageWriter<H>), Error<F::Error>> {
        trace!("page: write_append {:?}", page_id);
        let (header, mut r) = self.read(flash, page_id).await?;
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

        let w = PageWriter {
            _phantom: PhantomData,
            page_id,
            needs_erase: false,
            align_buf: [0; WRITE_SIZE],
            total_pos: r.prev_chunks_len,
            chunk_offset: r.chunk_offset,
            chunk_pos: 0,
        };

        Ok((header, w))
    }
}

pub struct PageReader {
    page_id: PageID,

    /// sum of lengths of all previous chunks (not counting current one)
    prev_chunks_len: usize,

    /// true if we've reached the end of the page.
    at_end: bool,

    /// Offset where the chunk we're currently writing starts.
    chunk_offset: usize,
    /// pos within the current chunk.
    chunk_pos: usize,
    /// Data bytes in the chunk we're currently writing.
    chunk_len: usize,

    /// Data in the current chunk.
    buf: [u8; MAX_CHUNK_SIZE],
}

impl PageReader {
    pub fn page_id(&self) -> PageID {
        self.page_id
    }
}

impl PageReader {
    async fn next_chunk<F: Flash>(&mut self, flash: &mut F) -> Result<bool, Error<F::Error>> {
        self.chunk_offset += ChunkHeader::SIZE + align_up(self.chunk_len);
        self.open_chunk(flash).await
    }

    async fn open_chunk<F: Flash>(&mut self, flash: &mut F) -> Result<bool, Error<F::Error>> {
        let data_start = self.chunk_offset + ChunkHeader::SIZE;
        if data_start > PAGE_SIZE {
            self.at_end = true;
            return Ok(false);
        }

        let mut header = [0u8; ChunkHeader::SIZE];
        flash
            .read(self.page_id as _, self.chunk_offset, &mut header)
            .await
            .map_err(Error::Flash)?;
        let header = ChunkHeader::from_bytes(header);

        // TODO make this more robust against written but not committed garbage.
        if header.len == 0xFFFF_FFFF {
            self.at_end = true;
            return Ok(false);
        }

        let Some(data_end) = data_start.checked_add(header.len as usize) else {
            corrupted!()
        };
        if data_end > PAGE_SIZE {
            corrupted!();
        }

        trace!("open chunk at offs={} len={}", self.chunk_offset, header.len);

        self.chunk_pos = 0;
        self.chunk_len = header.len as usize;

        let n = align_up(self.chunk_len);
        flash
            .read(
                self.page_id as _,
                self.chunk_offset + ChunkHeader::SIZE,
                &mut self.buf[..n],
            )
            .await
            .map_err(Error::Flash)?;

        Ok(true)
    }

    pub async fn read<F: Flash>(&mut self, flash: &mut F, data: &mut [u8]) -> Result<usize, Error<F::Error>> {
        trace!("PageReader({:?}): read({})", self.page_id, data.len());
        if self.at_end || data.is_empty() {
            trace!("read: at end or zero len");
            return Ok(0);
        }

        if self.chunk_pos == self.chunk_len {
            trace!("read: at end of chunk");
            if !self.next_chunk(flash).await? {
                trace!("read: no next chunk, we're at end.");
                return Ok(0);
            }
        }

        let n = data.len().min(self.chunk_len - self.chunk_pos);
        data[..n].copy_from_slice(&self.buf[self.chunk_pos..][..n]);
        self.chunk_pos += n;
        trace!("read: done, n={}", n);
        Ok(n)
    }

    pub async fn skip<F: Flash>(&mut self, flash: &mut F, len: usize) -> Result<usize, Error<F::Error>> {
        trace!("PageReader({:?}): skip({})", self.page_id, len);
        if self.at_end || len == 0 {
            trace!("skip: at end or zero len");
            return Ok(0);
        }

        if self.chunk_pos == self.chunk_len {
            trace!("skip: at end of chunk");
            if !self.next_chunk(flash).await? {
                trace!("skip: no next chunk, we're at end.");
                return Ok(0);
            }
        }

        let n = len.min(self.chunk_len - self.chunk_pos);
        self.prev_chunks_len += n;
        self.chunk_pos += n;
        trace!("skip: done, n={}", n);
        Ok(n)
    }

    pub async fn is_at_eof<F: Flash>(&mut self, flash: &mut F) -> Result<bool, Error<F::Error>> {
        if self.at_end {
            return Ok(true);
        }
        if self.chunk_pos == self.chunk_len && !self.next_chunk(flash).await? {
            return Ok(true);
        }
        Ok(false)
    }
}

pub struct PageWriter<H: Header> {
    _phantom: PhantomData<H>,

    page_id: PageID,
    needs_erase: bool,

    align_buf: [u8; WRITE_SIZE],

    /// Total data bytes in page (all chunks)
    total_pos: usize,

    /// Offset where the chunk we're currently writing starts.
    chunk_offset: usize,
    /// Data bytes in the chunk we're currently writing.
    chunk_pos: usize,
}

impl<H: Header> PageWriter<H> {
    pub fn len(&self) -> usize {
        self.total_pos
    }

    pub fn page_id(&self) -> PageID {
        self.page_id
    }

    pub async fn write<F: Flash>(&mut self, flash: &mut F, data: &[u8]) -> Result<usize, Error<F::Error>> {
        let max_write = PAGE_SIZE.saturating_sub(self.chunk_offset + ChunkHeader::SIZE + self.chunk_pos);
        let total_n = data.len().min(max_write);
        if total_n == 0 {
            return Ok(0);
        }
        let mut data = &data[..total_n];

        self.erase_if_needed(flash).await?;

        let align_offs = self.chunk_pos % WRITE_SIZE;
        if align_offs != 0 {
            let left = WRITE_SIZE - align_offs;
            let n = left.min(data.len());

            self.align_buf[align_offs..][..n].copy_from_slice(&data[..n]);
            data = &data[n..];
            self.total_pos += n;
            self.chunk_pos += n;

            if n == left {
                flash
                    .write(
                        self.page_id as _,
                        self.chunk_offset + ChunkHeader::SIZE + self.chunk_pos - WRITE_SIZE,
                        &self.align_buf,
                    )
                    .await
                    .map_err(Error::Flash)?;
            }
        }

        let n = data.len() - (data.len() % WRITE_SIZE);
        if n != 0 {
            flash
                .write(
                    self.page_id as _,
                    self.chunk_offset + ChunkHeader::SIZE + self.chunk_pos,
                    &data[..n],
                )
                .await
                .map_err(Error::Flash)?;
            data = &data[n..];
            self.total_pos += n;
            self.chunk_pos += n;
        }

        let n = data.len();
        assert!(n < WRITE_SIZE);
        self.align_buf[..n].copy_from_slice(data);
        self.total_pos += n;
        self.chunk_pos += n;

        Ok(total_n)
    }

    async fn erase_if_needed<F: Flash>(&mut self, flash: &mut F) -> Result<(), Error<F::Error>> {
        if self.needs_erase {
            flash.erase(self.page_id as _).await.map_err(Error::Flash)?;
            self.needs_erase = false;
        }
        Ok(())
    }

    pub async fn write_header<F: Flash>(&mut self, flash: &mut F, header: H) -> Result<(), Error<F::Error>> {
        self.erase_if_needed(flash).await?;

        PageManager::write_header(flash, self.page_id, header).await?;

        Ok(())
    }

    pub async fn commit<F: Flash>(&mut self, flash: &mut F) -> Result<(), Error<F::Error>> {
        if self.chunk_pos == 0 {
            // nothing to commit.
            return Ok(());
        }

        self.erase_if_needed(flash).await?;

        // flush align buf.
        let align_offs = self.chunk_pos % WRITE_SIZE;
        if align_offs != 0 {
            flash
                .write(
                    self.page_id as _,
                    self.chunk_offset + ChunkHeader::SIZE + self.chunk_pos - align_offs,
                    &self.align_buf,
                )
                .await
                .map_err(Error::Flash)?;
        }

        let h = ChunkHeader {
            len: self.chunk_pos as u32,
        };
        flash
            .write(self.page_id as _, self.chunk_offset, &h.to_bytes())
            .await
            .map_err(Error::Flash)?;

        // Prepare for next chunk.
        self.chunk_offset += ChunkHeader::SIZE + align_up(self.chunk_pos);
        self.chunk_pos = 0;

        Ok(())
    }
}

fn align_up(n: usize) -> usize {
    if n % WRITE_SIZE != 0 {
        n + WRITE_SIZE - n % WRITE_SIZE
    } else {
        n
    }
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
    pub struct TestHeader {
        foo: u32,
    }

    unsafe impl Header for TestHeader {
        const MAGIC: u32 = 0x470b635c;
    }

    const HEADER: TestHeader = TestHeader { foo: 123456 };
    const MAX_PAYLOAD: usize = PAGE_SIZE - PageHeader::SIZE - size_of::<TestHeader>() - ChunkHeader::SIZE;

    #[test_log::test(tokio::test)]
    async fn test_header() {
        let f = &mut MemFlash::new();
        let mut m = PageManager::new();

        PageManager::write_header(f, PAGE, HEADER).await.unwrap();
        let h = m.read_header::<TestHeader>(f, PAGE).await.unwrap();
        assert_eq!(h, HEADER)
    }

    #[test_log::test(tokio::test)]
    async fn test_header_read_unwritten() {
        let f = &mut MemFlash::new();
        let mut m = PageManager::new();

        let res = m.read_header::<TestHeader>(f, PAGE).await;
        assert!(matches!(res, Err(Error::Corrupted)))
    }

    #[test_log::test(tokio::test)]
    async fn test_read_unwritten() {
        let f = &mut MemFlash::new();
        let mut b = PageManager::new();

        // Read
        let res = b.read::<TestHeader>(f, PAGE).await;
        assert!(matches!(res, Err(Error::Corrupted)));
    }

    #[test_log::test(tokio::test)]
    async fn test_read_uncommitted() {
        let f = &mut MemFlash::new();
        let mut b = PageManager::new();

        let data = dummy_data(13);

        // Write
        let mut w = b.write::<TestHeader>(f, PAGE).await;
        w.write(f, &data).await.unwrap();
        drop(w); // don't commit

        // Read
        let res = b.read::<TestHeader>(f, PAGE).await;
        assert!(matches!(res, Err(Error::Corrupted)));
    }

    #[test_log::test(tokio::test)]
    async fn test_write_short() {
        let f = &mut MemFlash::new();
        let mut b = PageManager::new();

        let data = dummy_data(13);

        // Write
        let mut w = b.write::<TestHeader>(f, PAGE).await;
        let n = w.write(f, &data).await.unwrap();
        assert_eq!(n, 13);
        w.write_header(f, HEADER).await.unwrap();
        w.commit(f).await.unwrap();

        // Read
        let (h, mut r) = b.read::<TestHeader>(f, PAGE).await.unwrap();
        assert_eq!(h, HEADER);
        let mut buf = vec![0; data.len()];
        let n = r.read(f, &mut buf).await.unwrap();
        assert_eq!(n, 13);
        assert_eq!(data, buf);

        // Remount
        let mut b = PageManager::new();

        // Read
        let (h, mut r) = b.read::<TestHeader>(f, PAGE).await.unwrap();
        assert_eq!(h, HEADER);
        let mut buf = vec![0; data.len()];
        let n = r.read(f, &mut buf).await.unwrap();
        assert_eq!(n, 13);
        assert_eq!(data, buf);
    }

    #[test_log::test(tokio::test)]
    async fn test_overread() {
        let f = &mut MemFlash::new();
        let mut b = PageManager::new();

        let data = dummy_data(13);

        // Write
        let mut w = b.write::<TestHeader>(f, PAGE).await;
        w.write(f, &data).await.unwrap();
        w.write_header(f, HEADER).await.unwrap();
        w.commit(f).await.unwrap();

        // Read
        let (h, mut r) = b.read::<TestHeader>(f, PAGE).await.unwrap();
        assert_eq!(h, HEADER);
        let mut buf = vec![0; 1024];
        let n = r.read(f, &mut buf).await.unwrap();
        assert_eq!(n, 13);
        assert_eq!(data, buf[..13]);
    }

    #[test_log::test(tokio::test)]
    async fn test_overwrite() {
        let f = &mut MemFlash::new();
        let mut b = PageManager::new();

        let data = dummy_data(65536);

        // Write
        let mut w = b.write::<TestHeader>(f, PAGE).await;
        let n = w.write(f, &data).await.unwrap();
        assert_eq!(n, MAX_PAYLOAD);
        w.write_header(f, HEADER).await.unwrap();
        w.commit(f).await.unwrap();

        // Read
        let (h, mut r) = b.read::<TestHeader>(f, PAGE).await.unwrap();
        assert_eq!(h, HEADER);
        let mut buf = vec![0; MAX_PAYLOAD];
        let n = r.read(f, &mut buf).await.unwrap();
        assert_eq!(n, MAX_PAYLOAD);
        assert_eq!(data[..13], buf[..13]);
    }

    #[test_log::test(tokio::test)]
    async fn test_write_many() {
        let f = &mut MemFlash::new();
        let mut b = PageManager::new();

        // Write
        let mut w = b.write::<TestHeader>(f, PAGE).await;
        let n = w.write(f, &[1, 2, 3]).await.unwrap();
        assert_eq!(n, 3);
        let n = w.write(f, &[4, 5, 6, 7, 8, 9]).await.unwrap();
        assert_eq!(n, 6);
        w.write_header(f, HEADER).await.unwrap();
        w.commit(f).await.unwrap();

        // Read
        let (h, mut r) = b.read::<TestHeader>(f, PAGE).await.unwrap();
        assert_eq!(h, HEADER);
        let mut buf = vec![0; MAX_PAYLOAD];
        let n = r.read(f, &mut buf).await.unwrap();
        assert_eq!(n, 9);
        assert_eq!(buf[..9], [1, 2, 3, 4, 5, 6, 7, 8, 9]);
    }

    #[test_log::test(tokio::test)]
    async fn test_read_many() {
        let f = &mut MemFlash::new();
        let mut b = PageManager::new();

        // Write
        let mut w = b.write::<TestHeader>(f, PAGE).await;
        let n = w.write(f, &[1, 2, 3, 4, 5, 6, 7, 8, 9]).await.unwrap();
        assert_eq!(n, 9);
        w.write_header(f, HEADER).await.unwrap();
        w.commit(f).await.unwrap();

        // Read
        let (h, mut r) = b.read::<TestHeader>(f, PAGE).await.unwrap();
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
        let mut b = PageManager::new();

        // Write
        let mut w = b.write::<TestHeader>(f, PAGE).await;
        let n = w.write(f, &[1, 2, 3, 4, 5, 6, 7, 8, 9]).await.unwrap();
        assert_eq!(n, 9);
        w.write_header(f, HEADER).await.unwrap();
        w.commit(f).await.unwrap();
        let n = w.write(f, &[10, 11, 12]).await.unwrap();
        assert_eq!(n, 3);
        w.commit(f).await.unwrap();

        // Read
        let (h, mut r) = b.read::<TestHeader>(f, PAGE).await.unwrap();
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
        let mut b = PageManager::new();

        // Write
        let mut w = b.write::<TestHeader>(f, PAGE).await;
        let n = w.write(f, &[1, 2, 3, 4, 5, 6, 7, 8, 9]).await.unwrap();
        assert_eq!(n, 9);
        w.write_header(f, HEADER).await.unwrap();
        w.commit(f).await.unwrap();
        let n = w.write(f, &[10, 11, 12]).await.unwrap();
        assert_eq!(n, 3);
        // no commit!

        // Read
        let (h, mut r) = b.read::<TestHeader>(f, PAGE).await.unwrap();
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
        let mut b = PageManager::new();

        // Write
        let mut w = b.write::<TestHeader>(f, PAGE).await;
        let n = w.write(f, &[1, 2, 3, 4, 5, 6, 7, 8, 9]).await.unwrap();
        assert_eq!(n, 9);
        w.write_header(f, HEADER).await.unwrap();
        w.commit(f).await.unwrap();

        let (_, mut w) = b.write_append::<TestHeader>(f, PAGE).await.unwrap();
        let n = w.write(f, &[10, 11, 12]).await.unwrap();
        assert_eq!(n, 3);
        w.commit(f).await.unwrap();

        // Read
        let (h, mut r) = b.read::<TestHeader>(f, PAGE).await.unwrap();
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
        let mut b = PageManager::new();

        // Write
        let mut w = b.write::<TestHeader>(f, PAGE).await;
        let n = w.write(f, &[1, 2, 3, 4, 5, 6, 7, 8, 9]).await.unwrap();
        assert_eq!(n, 9);
        w.write_header(f, HEADER).await.unwrap();
        w.commit(f).await.unwrap();

        let (_, mut w) = b.write_append::<TestHeader>(f, PAGE).await.unwrap();
        let n = w.write(f, &[10, 11, 12]).await.unwrap();
        assert_eq!(n, 3);
        // no commit!

        // Read
        let (h, mut r) = b.read::<TestHeader>(f, PAGE).await.unwrap();
        assert_eq!(h, HEADER);
        let mut buf = vec![0; MAX_PAYLOAD];

        let n = r.read(f, &mut buf).await.unwrap();
        assert_eq!(n, 9);
        assert_eq!(buf[..9], [1, 2, 3, 4, 5, 6, 7, 8, 9]);

        let n = r.read(f, &mut buf).await.unwrap();
        assert_eq!(n, 0);
    }

    #[test_log::test(tokio::test)]
    async fn test_multichunk_append_no_commit_then_retry() {
        let f = &mut MemFlash::new();
        let mut b = PageManager::new();

        // Write
        let mut w = b.write::<TestHeader>(f, PAGE).await;
        let n = w.write(f, &[1, 2, 3, 4, 5, 6, 7, 8, 9]).await.unwrap();
        assert_eq!(n, 9);
        w.write_header(f, HEADER).await.unwrap();
        w.commit(f).await.unwrap();

        // Append but don't commit
        let (_, mut w) = b.write_append::<TestHeader>(f, PAGE).await.unwrap();
        let n = w.write(f, &[10, 11, 12, 13, 14, 15]).await.unwrap();
        assert_eq!(n, 6);
        // no commit!

        // Even though we didn't commit the appended stuff, it did get written to flash.
        // If there's "left over garbage" we can non longer append to this page. It must
        // behave as if it was full.
        let (_, mut w) = b.write_append::<TestHeader>(f, PAGE).await.unwrap();
        let n = w.write(f, &[13, 14, 15]).await.unwrap();
        assert_eq!(n, 0);

        // Read
        let (h, mut r) = b.read::<TestHeader>(f, PAGE).await.unwrap();
        assert_eq!(h, HEADER);
        let mut buf = vec![0; MAX_PAYLOAD];

        let n = r.read(f, &mut buf).await.unwrap();
        assert_eq!(n, 9);
        assert_eq!(buf[..9], [1, 2, 3, 4, 5, 6, 7, 8, 9]);

        let n = r.read(f, &mut buf).await.unwrap();
        assert_eq!(n, 0);
    }

    fn dummy_data(len: usize) -> Vec<u8> {
        let mut res = vec![0; len];
        for (i, v) in res.iter_mut().enumerate() {
            *v = i as u8 ^ (i >> 8) as u8 ^ (i >> 16) as u8 ^ (i >> 24) as u8;
        }
        res
    }
}

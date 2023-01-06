use core::mem;

use crate::alloc::Allocator;
use crate::config::*;
use crate::flash::Flash;
use crate::page::{PageManager, PageReader, PageWriter, ReadError};
use crate::Error;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum SeekDirection {
    Left,
    Right,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[repr(C)]
pub struct Header {
    seq: Seq,

    /// skiplist[0] = previous page, always.
    /// skiplist[i] = latest page that contains a byte with seq multiple of 2**(SKIPLIST_SHIFT+i)
    skiplist: [PageID; SKIPLIST_LEN],

    /// Offset of the first record boundary within this page.
    /// u16::MAX if there's no boundary within the page. This can happen if a very big record
    /// starts at a previous page, and ends at a later page.
    record_boundary: u16,
}

impl Header {
    #[cfg(test)]
    pub const DUMMY: Self = Self {
        seq: Seq(3),
        skiplist: [4; SKIPLIST_LEN],
        record_boundary: 5,
    };

    fn meta(seq: Seq) -> Self {
        Self {
            seq,
            skiplist: [PageID::MAX - 1; SKIPLIST_LEN],
            record_boundary: 0,
        }
    }

    fn is_meta(&self) -> bool {
        self.skiplist[0] == PageID::MAX - 1
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[repr(C)]
pub struct FileMeta {
    file_id: FileID,
    last_page_id: PageID,
    first_seq: Seq,
}
impl_bytes!(FileMeta);

#[derive(Debug)]
struct FileState {
    last_page: Option<PagePointer>,
    first_seq: Seq,
    last_seq: Seq,
}

pub struct FileManager<F: Flash> {
    flash: F,
    pages: PageManager<F>,
    files: [FileState; FILE_COUNT],
    meta_page_id: PageID,
    meta_seq: Seq,

    alloc: Allocator,
}

impl<F: Flash> FileManager<F> {
    pub fn new(flash: F) -> Self {
        const DUMMY_FILE: FileState = FileState {
            last_page: None,
            first_seq: Seq::ZERO,
            last_seq: Seq::ZERO,
        };
        Self {
            flash,
            meta_page_id: 0,
            meta_seq: Seq::ZERO,
            pages: PageManager::new(),
            files: [DUMMY_FILE; FILE_COUNT],
            alloc: Allocator::new(),
        }
    }

    pub fn flash_mut(&mut self) -> &mut F {
        &mut self.flash
    }

    pub fn is_empty(&mut self, file_id: FileID) -> bool {
        self.files[file_id as usize].last_page.is_none()
    }

    pub fn read(&mut self, file_id: FileID) -> FileReader {
        FileReader::new(self, file_id)
    }

    pub fn write(&mut self, file_id: FileID) -> FileWriter {
        FileWriter::new(self, file_id)
    }

    pub fn format(&mut self) {
        // Erase all meta pages.
        for page_id in 0..PAGE_COUNT {
            if let Ok(h) = self.read_header(page_id as _) {
                if h.is_meta() {
                    self.flash.erase(page_id);
                }
            }
        }

        // Write initial meta page.
        let w = self.write_page(0);
        w.commit(&mut self.flash, Header::meta(Seq(1)));
    }

    pub fn mount(&mut self) -> Result<(), Error> {
        self.alloc.reset();

        let mut meta_page_id = None;
        let mut meta_seq = Seq::ZERO;
        for page_id in 0..PAGE_COUNT {
            if let Ok(h) = self.read_header(page_id as _) {
                if h.is_meta() && h.seq > meta_seq {
                    meta_page_id = Some(page_id as PageID);
                    meta_seq = h.seq;
                }
            }
        }

        let Some(meta_page_id) = meta_page_id else {
            debug!("Meta page not found");
            return Err(Error::Corrupted)
        };
        self.meta_page_id = meta_page_id;
        self.meta_seq = meta_seq;
        self.alloc.mark_used(meta_page_id);

        #[derive(Clone, Copy)]
        struct FileInfo {
            last_page_id: PageID,
            first_seq: Seq,
        }

        let (_, mut r) = self.read_page(meta_page_id).inspect_err(|e| {
            debug!("failed read meta_page_id={}: {:?}", meta_page_id, e);
        })?;
        let mut files = [FileInfo {
            last_page_id: PageID::MAX,
            first_seq: Seq::ZERO,
        }; FILE_COUNT];
        loop {
            let mut meta = [0; FileMeta::SIZE];
            let n = r.read(&mut self.flash, &mut meta);
            if n == 0 {
                break;
            }
            if n != FileMeta::SIZE {
                debug!("meta page last entry incomplete, size {}", n);
                return Err(Error::Corrupted);
            }

            let meta = FileMeta::from_bytes(meta);
            if meta.file_id >= FILE_COUNT as _ {
                debug!("meta file_id out of range: {}", meta.file_id);
                return Err(Error::Corrupted);
            }

            if meta.last_page_id >= PAGE_COUNT as _ && meta.last_page_id != PageID::MAX {
                debug!("meta last_page_id out of range: {}", meta.file_id);
                return Err(Error::Corrupted);
            }

            files[meta.file_id as usize] = FileInfo {
                last_page_id: meta.last_page_id,
                first_seq: meta.first_seq,
            }
        }

        for file_id in 0..FILE_COUNT as FileID {
            let fi = files[file_id as usize];
            if fi.last_page_id == PageID::MAX {
                continue;
            }

            let (h, mut r) = self.read_page(fi.last_page_id).inspect_err(|e| {
                debug!("read last_page_id={} file_id={}: {:?}", file_id, fi.last_page_id, e);
            })?;
            let page_len = r.skip(PAGE_SIZE);
            let last_seq = h.seq.add(page_len)?;

            let mut p = Some(PagePointer {
                page_id: fi.last_page_id,
                header: h,
            });

            // note: first_seq == last_seq is corruption too, because in that case what we do is delete the file.
            if fi.first_seq >= last_seq {
                debug!(
                    "meta: file {} first_seq {:?} not smaller than last_seq {:?}",
                    file_id, fi.first_seq, last_seq
                );
                return Err(Error::Corrupted);
            }

            self.files[file_id as usize] = FileState {
                last_page: p,
                first_seq: fi.first_seq,
                last_seq,
            };

            while let Some(pp) = p {
                if self.alloc.is_used(pp.page_id) {
                    info!("page used by multiple files at the same time. page_id={}", pp.page_id);
                    return Err(Error::Corrupted);
                }
                self.alloc.mark_used(pp.page_id);
                p = pp.prev(self, fi.first_seq)?;
            }
        }

        Ok(())
    }

    // TODO remove this
    pub fn rename(&mut self, from: FileID, to: FileID) -> Result<(), Error> {
        self.files.swap(from as usize, to as usize);
        self.commit_and_truncate(None, &[])
    }

    pub fn commit(&mut self, w: &mut FileWriter) -> Result<(), Error> {
        self.commit_and_truncate(Some(w), &[])
    }

    pub fn commit_and_truncate(
        &mut self,
        w: Option<&mut FileWriter>,
        truncate: &[(FileID, usize)],
    ) -> Result<(), Error> {
        if let Some(w) = w {
            w.do_commit(self)?;
        }

        for &(file_id, trunc_len) in truncate {
            let f = &mut self.files[file_id as usize];

            let len = f.last_seq.sub(f.first_seq);
            let seq = f.first_seq.add(len.min(trunc_len))?;

            let old_seq = f.first_seq;
            let p = if seq == f.last_seq {
                f.last_page
            } else {
                self.get_file_page(file_id, seq)?.unwrap().prev(self, old_seq)?
            };
            self.free_between(p, None, old_seq)?;

            let f = &mut self.files[file_id as usize];
            if seq == f.last_seq {
                f.first_seq = Seq::ZERO;
                f.last_seq = Seq::ZERO;
                f.last_page = None;
            } else {
                f.first_seq = seq;
            }
        }

        let page_id = self.alloc.allocate();
        let mut w = self.write_page(page_id);
        for file_id in 0..FILE_COUNT as FileID {
            let f = &self.files[file_id as usize];
            if let Some(last) = f.last_page {
                let meta = FileMeta {
                    file_id,
                    first_seq: f.first_seq,
                    last_page_id: last.page_id,
                };
                let n = w.write(&mut self.flash, &meta.to_bytes());
                assert_eq!(n, FileMeta::SIZE);
            }
        }

        self.meta_seq = self.meta_seq.add(1)?; // TODO handle wraparound
        w.commit(&mut self.flash, Header::meta(self.meta_seq));

        self.alloc.free(self.meta_page_id);
        self.meta_page_id = page_id;

        Ok(())
    }

    fn get_file_page(&mut self, file_id: FileID, seq: Seq) -> Result<Option<PagePointer>, Error> {
        let f = &self.files[file_id as usize];
        let Some(last) = f.last_page else {
            return Ok(None)
        };
        if seq < f.first_seq || seq >= f.last_seq {
            Ok(None)
        } else {
            Ok(Some(last.prev_seq(self, seq)?))
        }
    }

    fn free_between(
        &mut self,
        mut from: Option<PagePointer>,
        to: Option<PagePointer>,
        seq_limit: Seq,
    ) -> Result<(), Error> {
        while let Some(pp) = from {
            if let Some(to) = to {
                if pp.page_id == to.page_id {
                    break;
                }
            }
            self.alloc.free(pp.page_id);
            from = pp.prev(self, seq_limit)?;
        }
        Ok(())
    }

    fn read_page(&mut self, page_id: PageID) -> Result<(Header, PageReader), Error> {
        self.pages.read(&mut self.flash, page_id)
    }

    fn read_header(&mut self, page_id: PageID) -> Result<Header, Error> {
        self.pages.read_header(&mut self.flash, page_id)
    }

    fn write_page(&mut self, page_id: PageID) -> PageWriter {
        self.pages.write(&mut self.flash, page_id)
    }

    fn dump(&mut self) {
        for (file_id, f) in self.files.iter().enumerate() {
            debug!("==== FILE {}", file_id);
            debug!("{:?}", f);
        }
    }
}

/// "cursor" pointing to a page within a file.
#[derive(Clone, Copy, Debug)]
struct PagePointer {
    page_id: PageID,
    header: Header,
}

impl PagePointer {
    fn prev(self, m: &mut FileManager<impl Flash>, seq_limit: Seq) -> Result<Option<PagePointer>, Error> {
        if self.header.seq <= seq_limit {
            return Ok(None);
        }

        let p2 = self.header.skiplist[0];
        if p2 == PageID::MAX {
            return Ok(None);
        }
        if p2 >= PAGE_COUNT as _ {
            debug!("prev page out of range {}", p2);
            return Err(Error::Corrupted);
        }

        let h2 = m.read_header(p2)?;

        // Check seq always decreases. This avoids infinite loops
        // TODO we can make this check stricter: h2.seq == self.header.seq - page_len
        if h2.seq >= self.header.seq {
            debug!(
                "seq not decreasing when walking back: curr={:?} prev={:?}",
                self.header.seq, h2.seq
            );
            return Err(Error::Corrupted);
        }
        Ok(Some(PagePointer {
            page_id: p2,
            header: h2,
        }))
    }

    fn prev_seq(mut self, m: &mut FileManager<impl Flash>, seq: Seq) -> Result<PagePointer, Error> {
        while self.header.seq > seq {
            let i = skiplist_index(seq, self.header.seq);
            let p2 = self.header.skiplist[i];
            if p2 == PageID::MAX {
                debug!("no prev page??");
                return Err(Error::Corrupted);
            }
            if p2 >= PAGE_COUNT as _ {
                debug!("prev page out of range {}", p2);
                return Err(Error::Corrupted);
            }

            let h2 = m.read_header(p2)?;

            // Check seq always decreases. This avoids infinite loops
            if h2.seq >= self.header.seq {
                debug!(
                    "seq not decreasing when walking back: curr={:?} prev={:?}",
                    self.header.seq, h2.seq
                );
                return Err(Error::Corrupted);
            }
            self = PagePointer {
                page_id: p2,
                header: h2,
            }
        }
        Ok(self)
    }
}

pub struct FileReader {
    file_id: FileID,
    state: ReaderState,
}

enum ReaderState {
    Created,
    Reading(ReaderStateReading),
    Finished,
}
struct ReaderStateReading {
    seq: Seq,
    reader: PageReader,
}

impl FileReader {
    fn new(_m: &mut FileManager<impl Flash>, file_id: FileID) -> Self {
        Self {
            file_id,
            state: ReaderState::Created,
        }
    }

    pub fn binary_search_start(&mut self, _m: &mut FileManager<impl Flash>) {
        // TODO
    }

    pub fn binary_search_seek(&mut self, _m: &mut FileManager<impl Flash>, _direction: SeekDirection) -> bool {
        // TODO
        false
    }

    fn next_page(&mut self, m: &mut FileManager<impl Flash>) -> Result<(), Error> {
        let seq = match &self.state {
            ReaderState::Created => m.files[self.file_id as usize].first_seq,
            ReaderState::Reading(s) => s.seq,
            ReaderState::Finished => unreachable!(),
        };
        self.seek_seq(m, seq)
    }

    fn seek_seq(&mut self, m: &mut FileManager<impl Flash>, seq: Seq) -> Result<(), Error> {
        self.state = match m.get_file_page(self.file_id, seq)? {
            Some(pp) => {
                let (h, mut r) = m.read_page(pp.page_id).inspect_err(|e| {
                    debug!("failed read next page={}: {:?}", pp.page_id, e);
                })?;
                if r.available() <= seq.sub(h.seq) {
                    debug!(
                        "found seq hole in file. page={} h.seq={:?} seq={:?} avail={}",
                        pp.page_id,
                        h.seq,
                        seq,
                        r.available()
                    );
                    return Err(Error::Corrupted);
                }
                r.seek((seq.sub(h.seq)) as usize);
                ReaderState::Reading(ReaderStateReading { seq, reader: r })
            }
            None => ReaderState::Finished,
        };
        Ok(())
    }

    pub fn read(&mut self, m: &mut FileManager<impl Flash>, mut data: &mut [u8]) -> Result<(), ReadError> {
        while !data.is_empty() {
            match &mut self.state {
                ReaderState::Finished => return Err(ReadError::Eof),
                ReaderState::Created => {
                    self.next_page(m)?;
                    continue;
                }
                ReaderState::Reading(s) => {
                    let n = s.reader.read(&mut m.flash, data);
                    data = &mut data[n..];
                    s.seq = s.seq.add(n)?;
                    if n == 0 {
                        self.next_page(m)?;
                    }
                }
            }
        }
        Ok(())
    }

    pub fn skip(&mut self, m: &mut FileManager<impl Flash>, mut len: usize) -> Result<(), ReadError> {
        // advance within the current page.
        if let ReaderState::Reading(s) = &mut self.state {
            // Only worth trying if the skip might not exhaust the current page
            if len < PAGE_MAX_PAYLOAD_SIZE {
                let n = s.reader.skip(len);
                len -= n;
                s.seq = s.seq.add(n).unwrap();
            }
        }

        // If we got more to skip
        if len != 0 {
            let seq = match &self.state {
                ReaderState::Created => m.files[self.file_id as usize].first_seq,
                ReaderState::Reading(s) => s.seq,
                ReaderState::Finished => unreachable!(),
            };

            let new_seq = seq.add(len).map_err(|_| ReadError::Eof)?;
            if new_seq > m.files[self.file_id as usize].last_seq {
                return Err(ReadError::Eof);
            }

            self.seek_seq(m, new_seq)?;
        }

        Ok(())
    }

    pub fn seek(&mut self, m: &mut FileManager<impl Flash>, offs: usize) -> Result<(), ReadError> {
        let first_seq = m.files[self.file_id as usize].first_seq;
        let new_seq = first_seq.add(offs).map_err(|_| ReadError::Eof)?;
        if new_seq > m.files[self.file_id as usize].last_seq {
            return Err(ReadError::Eof);
        }

        self.seek_seq(m, new_seq)?;
        Ok(())
    }
}

pub struct FileWriter {
    file_id: FileID,
    last_page: Option<PagePointer>,
    seq: Seq,
    record_boundary_seq: Seq,
    writer: Option<PageWriter>,
}

impl FileWriter {
    fn new(m: &mut FileManager<impl Flash>, file_id: FileID) -> Self {
        let f = &m.files[file_id as usize];

        Self {
            file_id,
            last_page: f.last_page,
            seq: f.last_seq,
            record_boundary_seq: Seq(0),
            writer: None,
        }
    }

    fn flush_header(&mut self, m: &mut FileManager<impl Flash>, w: PageWriter) -> Result<(), Error> {
        let page_size = w.offset();
        let page_id = w.page_id();
        let mut skiplist = [PageID::MAX; SKIPLIST_LEN];
        if let Some(last_page) = &self.last_page {
            skiplist = last_page.header.skiplist;

            let top = skiplist_index(last_page.header.seq, self.seq) + 1;
            skiplist[..top].fill(last_page.page_id);
        }

        let next_seq = self.seq.add(page_size)?;

        let record_boundary = if self.record_boundary_seq >= self.seq && self.record_boundary_seq < next_seq {
            self.record_boundary_seq.sub(self.seq).try_into().unwrap()
        } else {
            u16::MAX
        };
        let header = Header {
            seq: self.seq,
            skiplist,
            record_boundary,
        };
        w.commit(&mut m.flash, header);

        self.seq = next_seq;
        self.last_page = Some(PagePointer { page_id, header });

        Ok(())
    }

    fn next_page(&mut self, m: &mut FileManager<impl Flash>) -> Result<(), Error> {
        if let Some(w) = mem::replace(&mut self.writer, None) {
            self.flush_header(m, w)?;
        }

        let page_id = m.alloc.allocate();
        self.writer = Some(m.write_page(page_id));
        Ok(())
    }

    pub fn write(&mut self, m: &mut FileManager<impl Flash>, mut data: &[u8]) -> Result<(), Error> {
        while !data.is_empty() {
            match &mut self.writer {
                None => {
                    self.next_page(m)?;
                    continue;
                }
                Some(w) => {
                    let n = w.write(&mut m.flash, data);
                    data = &data[n..];
                    if n == 0 {
                        self.next_page(m)?;
                    }
                }
            }
        }
        Ok(())
    }

    fn do_commit(&mut self, m: &mut FileManager<impl Flash>) -> Result<(), Error> {
        if let Some(w) = mem::replace(&mut self.writer, None) {
            self.flush_header(m, w)?;
            let f = &mut m.files[self.file_id as usize];
            f.last_page = self.last_page;
            f.last_seq = self.seq;
        }
        Ok(())
    }

    pub fn discard(&mut self, m: &mut FileManager<impl Flash>) {
        if let Some(w) = &self.writer {
            // Free the page we're writing now (not yet committed)
            let page_id = w.page_id();
            m.alloc.free(page_id);

            // Free previous pages, if any
            let f = &m.files[self.file_id as usize];
            m.free_between(self.last_page, f.last_page, Seq::ZERO).unwrap();
        };
    }

    pub fn record_end(&mut self) {
        let offs = self.writer.as_mut().unwrap().offset();
        self.record_boundary_seq = self.seq.add(offs).unwrap()
    }
}

#[repr(transparent)]
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub struct Seq(u32);

impl Seq {
    pub const ZERO: Self = Self(0);
    pub const MAX: Self = Self(u32::MAX);

    fn sub(self, other: Self) -> usize {
        self.0.checked_sub(other.0).unwrap() as _
    }

    fn add(self, offs: usize) -> Result<Self, Error> {
        let Ok(offs_u32) = offs.try_into() else {
            debug!("seq add overflow, offs doesn't fit u32: {}", offs);
            return Err(Error::Corrupted);
        };
        let Some(res) = self.0.checked_add(offs_u32) else {
            debug!("seq add overflow, self={} offs={}", self.0, offs_u32);
            return Err(Error::Corrupted);
        };
        Ok(Self(res))
    }
}

/// Find the highest amount of trailing zeros in all numbers in `a..b`.
///
/// Requires a < b.
/// Thanks @jannic for figuring out the beautiful bitwise hack!
fn max_trailing_zeros_between(a: u32, b: u32) -> u32 {
    assert!(a < b);

    if a == 0 {
        return 32;
    }

    31u32 - ((a - 1) ^ (b - 1)).leading_zeros()
}

fn skiplist_index(from: Seq, to: Seq) -> usize {
    let bits = max_trailing_zeros_between(from.0, to.0) as usize;
    bits.saturating_sub(SKIPLIST_SHIFT).min(SKIPLIST_LEN - 1)
}

#[cfg(test)]
mod tests {

    use rand::Rng;

    use super::*;
    use crate::flash::MemFlash;

    #[test]
    fn test_read_write() {
        let mut f = MemFlash::new();
        let mut m = FileManager::new(&mut f);
        m.format();
        m.mount().unwrap();

        let data = dummy_data(24);

        let mut w = m.write(0);
        w.write(&mut m, &data).unwrap();
        m.commit(&mut w).unwrap();

        let mut r = m.read(0);
        let mut buf = vec![0; data.len()];
        r.read(&mut m, &mut buf).unwrap();
        assert_eq!(data, buf);

        // Remount
        m.mount().unwrap();

        let mut r = m.read(0);
        let mut buf = vec![0; data.len()];
        r.read(&mut m, &mut buf).unwrap();
        assert_eq!(data, buf);
    }

    #[test]
    fn test_read_write_long() {
        let mut f = MemFlash::new();
        let mut m = FileManager::new(&mut f);
        m.format();
        m.mount().unwrap();

        let data = dummy_data(23456);

        let mut w = m.write(0);
        w.write(&mut m, &data).unwrap();
        m.commit(&mut w).unwrap();
        w.discard(&mut m);

        let mut r = m.read(0);
        let mut buf = vec![0; data.len()];
        r.read(&mut m, &mut buf).unwrap();
        assert_eq!(data, buf);

        // Remount
        m.mount().unwrap();

        let mut r = m.read(0);
        let mut buf = vec![0; data.len()];
        r.read(&mut m, &mut buf).unwrap();
        assert_eq!(data, buf);
    }

    #[test]
    fn test_append() {
        let mut f = MemFlash::new();
        let mut m = FileManager::new(&mut f);
        m.format();
        m.mount().unwrap();

        let mut w = m.write(0);
        w.write(&mut m, &[1, 2, 3, 4, 5]).unwrap();
        m.commit(&mut w).unwrap();

        let mut w = m.write(0);
        w.write(&mut m, &[6, 7, 8, 9]).unwrap();
        m.commit(&mut w).unwrap();

        let mut r = m.read(0);
        let mut buf = vec![0; 9];
        r.read(&mut m, &mut buf).unwrap();
        assert_eq!(buf, [1, 2, 3, 4, 5, 6, 7, 8, 9]);

        // Remount
        m.mount().unwrap();

        let mut r = m.read(0);
        r.read(&mut m, &mut buf).unwrap();
        assert_eq!(buf, [1, 2, 3, 4, 5, 6, 7, 8, 9]);
    }

    #[test]
    fn test_truncate() {
        let mut f = MemFlash::new();
        let mut m = FileManager::new(&mut f);
        m.format();
        m.mount().unwrap();

        let mut w = m.write(0);
        w.write(&mut m, &[1, 2, 3, 4, 5]).unwrap();
        m.commit(&mut w).unwrap();

        m.commit_and_truncate(None, &[(0, 2)]).unwrap();

        let mut r = m.read(0);
        let mut buf = [0; 3];
        r.read(&mut m, &mut buf).unwrap();
        assert_eq!(buf, [3, 4, 5]);

        m.commit_and_truncate(None, &[(0, 1)]).unwrap();

        let mut r = m.read(0);
        let mut buf = [0; 2];
        r.read(&mut m, &mut buf).unwrap();
        assert_eq!(buf, [4, 5]);

        // Remount
        m.mount().unwrap();

        let mut r = m.read(0);
        let mut buf = [0; 2];
        r.read(&mut m, &mut buf).unwrap();
        assert_eq!(buf, [4, 5]);
    }

    #[test]
    fn test_append_truncate() {
        let mut f = MemFlash::new();
        let mut m = FileManager::new(&mut f);
        m.format();
        m.mount().unwrap();

        let mut w = m.write(0);
        w.write(&mut m, &[1, 2, 3, 4, 5]).unwrap();
        m.commit(&mut w).unwrap();

        let mut w = m.write(0);
        w.write(&mut m, &[6, 7, 8, 9]).unwrap();

        m.commit_and_truncate(Some(&mut w), &[(0, 2)]).unwrap();

        let mut r = m.read(0);
        let mut buf = [0; 7];
        r.read(&mut m, &mut buf).unwrap();
        assert_eq!(buf, [3, 4, 5, 6, 7, 8, 9]);

        m.commit_and_truncate(None, &[(0, 1)]).unwrap();

        let mut r = m.read(0);
        let mut buf = [0; 6];
        r.read(&mut m, &mut buf).unwrap();
        assert_eq!(buf, [4, 5, 6, 7, 8, 9]);

        m.commit_and_truncate(None, &[(0, 5)]).unwrap();

        let mut r = m.read(0);
        let mut buf = [0; 1];
        r.read(&mut m, &mut buf).unwrap();
        assert_eq!(buf, [9]);

        // Remount
        m.mount().unwrap();

        let mut r = m.read(0);
        let mut buf = [0; 1];
        r.read(&mut m, &mut buf).unwrap();
        assert_eq!(buf, [9]);

        let mut w = m.write(0);
        w.write(&mut m, &[10, 11, 12]).unwrap();
        m.commit(&mut w).unwrap();

        let mut r = m.read(0);
        let mut buf = [0; 4];
        r.read(&mut m, &mut buf).unwrap();
        assert_eq!(buf, [9, 10, 11, 12]);
    }

    #[test]
    fn test_delete() {
        let mut f = MemFlash::new();
        let mut m = FileManager::new(&mut f);
        m.format();
        m.mount().unwrap();

        let mut w = m.write(0);
        w.write(&mut m, &[1, 2, 3, 4, 5]).unwrap();
        m.commit(&mut w).unwrap();

        assert_eq!(m.alloc.is_used(1), true);

        m.commit_and_truncate(None, &[(0, 5)]).unwrap();

        assert_eq!(m.alloc.is_used(1), false);

        // Remount
        m.mount().unwrap();

        assert_eq!(m.alloc.is_used(1), false);

        let mut r = m.read(0);
        let mut buf = [0; 1];
        let res = r.read(&mut m, &mut buf);
        assert!(matches!(res, Err(ReadError::Eof)));
    }

    #[test]
    fn test_truncate_alloc() {
        let mut f = MemFlash::new();
        let mut m = FileManager::new(&mut f);
        m.format();
        m.mount().unwrap();

        assert_eq!(m.alloc.is_used(1), false);

        let mut w = m.write(0);
        w.write(&mut m, &[1, 2, 3, 4, 5]).unwrap();
        m.commit(&mut w).unwrap();

        assert_eq!(m.alloc.is_used(1), true);

        m.commit_and_truncate(None, &[(0, 5)]).unwrap();

        assert_eq!(m.alloc.is_used(1), false);

        // Remount
        m.mount().unwrap();

        assert_eq!(m.alloc.is_used(1), false);

        let mut r = m.read(0);
        let mut buf = [0; 1];
        let res = r.read(&mut m, &mut buf);
        assert!(matches!(res, Err(ReadError::Eof)));
    }

    #[test]
    fn test_truncate_alloc_2() {
        let mut f = MemFlash::new();
        let mut m = FileManager::new(&mut f);
        m.format();
        m.mount().unwrap();

        assert_eq!(m.alloc.is_used(1), false);

        let data = dummy_data(PAGE_MAX_PAYLOAD_SIZE);

        let mut w = m.write(0);
        w.write(&mut m, &data).unwrap();
        w.write(&mut m, &data).unwrap();
        m.commit(&mut w).unwrap();

        assert_eq!(m.alloc.is_used(1), true);
        assert_eq!(m.alloc.is_used(2), true);

        m.commit_and_truncate(None, &[(0, PAGE_MAX_PAYLOAD_SIZE)]).unwrap();
        assert_eq!(m.alloc.is_used(1), false);
        assert_eq!(m.alloc.is_used(2), true);

        m.commit_and_truncate(None, &[(0, PAGE_MAX_PAYLOAD_SIZE)]).unwrap();
        assert_eq!(m.alloc.is_used(1), false);
        assert_eq!(m.alloc.is_used(2), false);

        // Remount
        m.mount().unwrap();

        assert_eq!(m.alloc.is_used(1), false);
        assert_eq!(m.alloc.is_used(2), false);

        let mut r = m.read(0);
        let mut buf = [0; 1];
        let res = r.read(&mut m, &mut buf);
        assert!(matches!(res, Err(ReadError::Eof)));
    }

    #[test]
    fn test_append_no_commit() {
        let mut f = MemFlash::new();
        let mut m = FileManager::new(&mut f);
        m.format();
        m.mount().unwrap();

        let mut w = m.write(0);
        w.write(&mut m, &[1, 2, 3, 4, 5]).unwrap();
        m.commit(&mut w).unwrap();

        let mut w = m.write(0);
        w.write(&mut m, &[6, 7, 8, 9]).unwrap();
        w.discard(&mut m);

        let mut r = m.read(0);
        let mut buf = [0; 5];
        r.read(&mut m, &mut buf).unwrap();
        assert_eq!(buf, [1, 2, 3, 4, 5]);
        let mut buf = [0; 1];
        let res = r.read(&mut m, &mut buf);
        assert!(matches!(res, Err(ReadError::Eof)));

        let mut w = m.write(0);
        w.write(&mut m, &[10, 11]).unwrap();
        m.commit(&mut w).unwrap();

        let mut r = m.read(0);
        let mut buf = [0; 7];
        r.read(&mut m, &mut buf).unwrap();
        assert_eq!(buf, [1, 2, 3, 4, 5, 10, 11]);
    }

    #[test]
    fn test_read_unwritten() {
        let mut f = MemFlash::new();
        let mut m = FileManager::new(&mut f);
        m.format();
        m.mount().unwrap();

        let mut r = m.read(0);
        let mut buf = vec![0; 1024];
        let res = r.read(&mut m, &mut buf);
        assert!(matches!(res, Err(ReadError::Eof)));
    }

    #[test]
    fn test_read_uncommitted() {
        let mut f = MemFlash::new();
        let mut m = FileManager::new(&mut f);
        m.format();
        m.mount().unwrap();

        let data = dummy_data(1234);

        let mut w = m.write(0);
        w.write(&mut m, &data).unwrap();
        w.discard(&mut m); // don't commit

        let mut r = m.read(0);
        let mut buf = vec![0; 1024];
        let res = r.read(&mut m, &mut buf);
        assert!(matches!(res, Err(ReadError::Eof)));
    }

    #[test]
    fn test_alloc_commit() {
        let mut f = MemFlash::new();
        let mut m = FileManager::new(&mut f);
        m.format();
        m.mount().unwrap();

        assert_eq!(m.alloc.is_used(1), false);
        assert_eq!(m.alloc.is_used(2), false);

        let data = dummy_data(PAGE_MAX_PAYLOAD_SIZE);
        let mut w = m.write(0);

        w.write(&mut m, &data).unwrap();
        assert_eq!(m.alloc.is_used(0), true); // old meta
        assert_eq!(m.alloc.is_used(1), true);
        assert_eq!(m.alloc.is_used(2), false);
        assert_eq!(m.alloc.is_used(3), false);

        w.write(&mut m, &data).unwrap();
        assert_eq!(m.alloc.is_used(0), true); // old meta
        assert_eq!(m.alloc.is_used(1), true);
        assert_eq!(m.alloc.is_used(2), true);
        assert_eq!(m.alloc.is_used(3), false);

        m.commit(&mut w).unwrap();
        assert_eq!(m.alloc.is_used(0), false); // old meta
        assert_eq!(m.alloc.is_used(1), true);
        assert_eq!(m.alloc.is_used(2), true);
        assert_eq!(m.alloc.is_used(3), true); // new meta

        // Remount
        m.mount().unwrap();
        assert_eq!(m.alloc.is_used(1), true);
        assert_eq!(m.alloc.is_used(2), true);
        assert_eq!(m.alloc.is_used(3), true); // new meta
    }

    #[test]
    fn test_alloc_discard_1page() {
        let mut f = MemFlash::new();
        let mut m = FileManager::new(&mut f);
        m.format();
        m.mount().unwrap();

        assert_eq!(m.alloc.is_used(0), true);
        assert_eq!(m.alloc.is_used(1), false);
        assert_eq!(m.alloc.is_used(2), false);

        let data = dummy_data(PAGE_MAX_PAYLOAD_SIZE);
        let mut w = m.write(0);

        w.write(&mut m, &data).unwrap();
        assert_eq!(m.alloc.is_used(0), true);
        assert_eq!(m.alloc.is_used(1), true);
        assert_eq!(m.alloc.is_used(2), false);

        w.discard(&mut m);
        assert_eq!(m.alloc.is_used(0), true);
        assert_eq!(m.alloc.is_used(1), false);
        assert_eq!(m.alloc.is_used(2), false);

        // Remount
        m.mount().unwrap();
        assert_eq!(m.alloc.is_used(0), true);
        assert_eq!(m.alloc.is_used(1), false);
        assert_eq!(m.alloc.is_used(2), false);
    }

    #[test]
    fn test_alloc_discard_2page() {
        let mut f = MemFlash::new();
        let mut m = FileManager::new(&mut f);
        m.format();
        m.mount().unwrap();

        assert_eq!(m.alloc.is_used(0), true);
        assert_eq!(m.alloc.is_used(1), false);

        let data = dummy_data(PAGE_MAX_PAYLOAD_SIZE);
        let mut w = m.write(0);

        w.write(&mut m, &data).unwrap();
        assert_eq!(m.alloc.is_used(0), true);
        assert_eq!(m.alloc.is_used(1), true);
        assert_eq!(m.alloc.is_used(2), false);

        w.write(&mut m, &data).unwrap();
        assert_eq!(m.alloc.is_used(0), true);
        assert_eq!(m.alloc.is_used(1), true);
        assert_eq!(m.alloc.is_used(2), true);
        assert_eq!(m.alloc.is_used(3), false);

        w.discard(&mut m);
        assert_eq!(m.alloc.is_used(0), true);
        assert_eq!(m.alloc.is_used(1), false);
        assert_eq!(m.alloc.is_used(2), false);
        assert_eq!(m.alloc.is_used(3), false);

        // Remount
        m.mount().unwrap();
        assert_eq!(m.alloc.is_used(0), true);
        assert_eq!(m.alloc.is_used(1), false);
        assert_eq!(m.alloc.is_used(2), false);
        assert_eq!(m.alloc.is_used(3), false);
    }

    #[test]
    fn test_alloc_discard_3page() {
        let mut f = MemFlash::new();
        let mut m = FileManager::new(&mut f);
        m.format();
        m.mount().unwrap();

        assert_eq!(m.alloc.is_used(0), true);
        assert_eq!(m.alloc.is_used(1), false);
        assert_eq!(m.alloc.is_used(2), false);
        assert_eq!(m.alloc.is_used(3), false);

        let data = dummy_data(PAGE_MAX_PAYLOAD_SIZE * 3);
        let mut w = m.write(0);
        w.write(&mut m, &data).unwrap();
        assert_eq!(m.alloc.is_used(0), true);
        assert_eq!(m.alloc.is_used(1), true);
        assert_eq!(m.alloc.is_used(2), true);
        assert_eq!(m.alloc.is_used(3), true);
        assert_eq!(m.alloc.is_used(4), false);

        w.discard(&mut m);
        assert_eq!(m.alloc.is_used(0), true);
        assert_eq!(m.alloc.is_used(1), false);
        assert_eq!(m.alloc.is_used(2), false);
        assert_eq!(m.alloc.is_used(3), false);
        assert_eq!(m.alloc.is_used(4), false);

        // Remount
        m.mount().unwrap();
        assert_eq!(m.alloc.is_used(0), true);
        assert_eq!(m.alloc.is_used(1), false);
        assert_eq!(m.alloc.is_used(2), false);
        assert_eq!(m.alloc.is_used(3), false);
        assert_eq!(m.alloc.is_used(4), false);
    }

    #[test]
    fn test_append_alloc_discard() {
        let mut f = MemFlash::new();
        let mut m = FileManager::new(&mut f);
        m.format();
        m.mount().unwrap();

        assert_eq!(m.alloc.is_used(0), true);
        assert_eq!(m.alloc.is_used(1), false);

        let data = dummy_data(24);
        let mut w = m.write(0);
        w.write(&mut m, &data).unwrap();
        m.commit(&mut w).unwrap();
        assert_eq!(m.alloc.is_used(0), false); // old meta
        assert_eq!(m.alloc.is_used(1), true);
        assert_eq!(m.alloc.is_used(2), true); // new meta
        assert_eq!(m.alloc.is_used(3), false);

        let mut w = m.write(0);
        w.write(&mut m, &data).unwrap();
        assert_eq!(m.alloc.is_used(0), false);
        assert_eq!(m.alloc.is_used(1), true);
        assert_eq!(m.alloc.is_used(2), true);
        assert_eq!(m.alloc.is_used(3), true);

        w.discard(&mut m);
        assert_eq!(m.alloc.is_used(0), false);
        assert_eq!(m.alloc.is_used(1), true);
        assert_eq!(m.alloc.is_used(2), true);
        assert_eq!(m.alloc.is_used(3), false);

        // Remount
        m.mount().unwrap();
        assert_eq!(m.alloc.is_used(0), false);
        assert_eq!(m.alloc.is_used(1), true);
        assert_eq!(m.alloc.is_used(2), true);
        assert_eq!(m.alloc.is_used(3), false);
    }

    #[test]
    fn test_write_2_files() {
        let mut f = MemFlash::new();
        let mut m = FileManager::new(&mut f);
        m.format();
        m.mount().unwrap();

        let data = dummy_data(32);

        let mut w1 = m.write(1);
        w1.write(&mut m, &data).unwrap();

        let mut w2 = m.write(2);
        w2.write(&mut m, &data).unwrap();

        m.commit(&mut w2).unwrap();
        m.commit(&mut w1).unwrap();

        let mut r = m.read(1);
        let mut buf = [0; 32];
        r.read(&mut m, &mut buf).unwrap();
        assert_eq!(buf[..], data[..]);

        let mut r = m.read(2);
        let mut buf = [0; 32];
        r.read(&mut m, &mut buf).unwrap();
        assert_eq!(buf[..], data[..]);

        // Remount
        m.mount().unwrap();

        let mut r = m.read(1);
        let mut buf = [0; 32];
        r.read(&mut m, &mut buf).unwrap();
        assert_eq!(buf[..], data[..]);

        let mut r = m.read(2);
        let mut buf = [0; 32];
        r.read(&mut m, &mut buf).unwrap();
        assert_eq!(buf[..], data[..]);
    }

    fn dummy_data(len: usize) -> Vec<u8> {
        let mut res = vec![0; len];
        for (i, v) in res.iter_mut().enumerate() {
            *v = i as u8 ^ (i >> 8) as u8 ^ (i >> 16) as u8 ^ (i >> 24) as u8;
        }
        res
    }

    fn rand(max: usize) -> usize {
        rand::thread_rng().gen_range(0..max)
    }

    fn rand_between(from: usize, to: usize) -> usize {
        rand::thread_rng().gen_range(from..=to)
    }

    #[test]
    fn test_smoke() {
        let mut f = MemFlash::new();
        let mut m = FileManager::new(&mut f);
        m.format();
        m.mount().unwrap();

        let mut seq_min = 0;
        let mut seq_max = 0;
        let file_id = 0;

        let max_size = 2000;

        for _ in 0..100000 {
            match rand(20) {
                // truncate
                0 => {
                    let s = rand_between(0, seq_max - seq_min);
                    debug!("{} {}, truncate {}", seq_min, seq_max, s);
                    m.commit_and_truncate(None, &[(file_id, s)]).unwrap();
                    seq_min += s;
                }
                // append
                _ => {
                    let n = rand(1024);
                    if seq_max - seq_min + n > max_size {
                        continue;
                    }

                    debug!("{} {}, append {}", seq_min, seq_max, n);

                    let data: Vec<_> = (0..n).map(|i| (seq_max + i) as u8).collect();

                    let mut w = m.write(file_id);
                    w.write(&mut m, &data).unwrap();
                    m.commit(&mut w).unwrap();

                    seq_max += n;
                }
            }

            // ============ Check read all
            debug!("{} {}, read_all", seq_min, seq_max);

            let mut r = m.read(file_id);
            let mut data = vec![0; seq_max - seq_min];
            r.read(&mut m, &mut data).unwrap();
            let want_data: Vec<_> = (0..seq_max - seq_min).map(|i| (seq_min + i) as u8).collect();
            assert_eq!(data, want_data);

            // Check we're at EOF
            let mut buf = [0; 1];
            assert_eq!(r.read(&mut m, &mut buf), Err(ReadError::Eof));

            // ============ Check read seek
            let s = rand_between(0, seq_max - seq_min);
            debug!("{} {}, read_seek {}", seq_min, seq_max, s);

            let mut r = m.read(file_id);
            r.seek(&mut m, s).unwrap();
            let mut data = vec![0; seq_max - seq_min - s];
            r.read(&mut m, &mut data).unwrap();
            let want_data: Vec<_> = (0..seq_max - seq_min - s).map(|i| (seq_min + s + i) as u8).collect();
            assert_eq!(data, want_data);

            // Check we're at EOF
            let mut buf = [0; 1];
            assert_eq!(r.read(&mut m, &mut buf), Err(ReadError::Eof));

            // ============ Check read skip
            let s1 = rand_between(0, seq_max - seq_min);
            let s2 = rand_between(0, seq_max - seq_min - s1);
            debug!("{} {}, read_skip {} {}", seq_min, seq_max, s1, s2);

            let mut r = m.read(file_id);
            r.skip(&mut m, s1).unwrap();
            r.skip(&mut m, s2).unwrap();
            let mut data = vec![0; seq_max - seq_min - s1 - s2];
            r.read(&mut m, &mut data).unwrap();
            let want_data: Vec<_> = (0..seq_max - seq_min - s1 - s2)
                .map(|i| (seq_min + s1 + s2 + i) as u8)
                .collect();
            assert_eq!(data, want_data);

            // Check we're at EOF
            let mut buf = [0; 1];
            assert_eq!(r.read(&mut m, &mut buf), Err(ReadError::Eof));
        }
    }

    #[test]
    fn test_max_trailing_zeros_between() {
        fn slow(a: u32, b: u32) -> u32 {
            assert!(a < b);
            (a..b).map(|x| x.trailing_zeros()).max().unwrap()
        }

        fn meh(a: u32, b: u32) -> u32 {
            assert!(a < b);

            if a == 0 {
                return 32;
            }

            for i in (0..32).rev() {
                let x = (b - 1) >> i << i;
                if x >= a && x < b {
                    return i;
                }
            }
            0
        }

        // Test slow matches meh and fast.
        for a in 0..100 {
            for b in a + 1..100 {
                assert_eq!(slow(a, b), max_trailing_zeros_between(a, b), "failed at {} {}", a, b);
                assert_eq!(slow(a, b), meh(a, b), "failed at {} {}", a, b);
            }
        }

        // Test meh matches fast, for bigger numbers.
        let interesting = [
            0x0000_0000,
            0x0000_0001,
            0x0000_0002,
            0x3FFF_FFFE,
            0x3FFF_FFFF,
            0x4000_0000,
            0x4000_0001,
            0x7FFF_FFFE,
            0x7FFF_FFFF,
            0x8000_0000,
            0x8000_0001,
            0xBFFF_FFFE,
            0xBFFF_FFFF,
            0xC000_0000,
            0xC000_0001,
            0xFFFF_FFFE,
            0x7FFF_FFFF,
        ];

        for a in interesting {
            for b in interesting {
                if a < b {
                    assert_eq!(meh(a, b), max_trailing_zeros_between(a, b), "failed at {} {}", a, b);
                }
            }
        }
    }
}

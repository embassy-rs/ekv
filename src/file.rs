use core::mem::size_of;
use core::{fmt, mem};

use crate::alloc::Allocator;
use crate::config::*;
use crate::flash::Flash;
pub use crate::page::ReadError;
use crate::page::{ChunkHeader, Header, PageHeader, PageManager, PageReader, PageWriter};
use crate::types::{OptionPageID, PageID};
use crate::{page, Error};

pub const PAGE_MAX_PAYLOAD_SIZE: usize = PAGE_SIZE - PageHeader::SIZE - size_of::<DataHeader>() - ChunkHeader::SIZE;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum SeekDirection {
    Left,
    Right,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[repr(C)]
pub struct MetaHeader {
    seq: Seq,
}

unsafe impl page::Header for MetaHeader {
    const MAGIC: u32 = 0x470b635c;
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[repr(C)]
pub struct DataHeader {
    seq: Seq,

    /// skiplist[0] = previous page, always.
    /// skiplist[i] = latest page that contains a byte with seq multiple of 2**(SKIPLIST_SHIFT+i)
    skiplist: [OptionPageID; SKIPLIST_LEN],

    /// Offset of the first record boundary within this page.
    /// u16::MAX if there's no boundary within the page. This can happen if a very big record
    /// starts at a previous page, and ends at a later page.
    record_boundary: u16,
}

unsafe impl page::Header for DataHeader {
    const MAGIC: u32 = 0xa934c056;
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[repr(C)]
pub struct FileMeta {
    file_id: FileID,
    flags: u8,
    last_page_id: OptionPageID,
    first_seq: Seq,
}
impl_bytes!(FileMeta);

#[derive(Debug, Clone, Copy)]
struct FileState {
    dirty: bool,

    last_page: Option<PagePointer>,
    first_seq: Seq,
    last_seq: Seq,
    flags: u8,
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
            dirty: false,
            last_page: None,
            first_seq: Seq::ZERO,
            last_seq: Seq::ZERO,
            flags: 0,
        };
        Self {
            flash,
            meta_page_id: PageID::from_raw(0).unwrap(),
            meta_seq: Seq::ZERO,
            pages: PageManager::new(),
            files: [DUMMY_FILE; FILE_COUNT],
            alloc: Allocator::new(),
        }
    }

    pub fn used_pages(&self) -> usize {
        self.alloc.used()
    }

    pub fn free_pages(&self) -> usize {
        PAGE_COUNT - self.alloc.used()
    }

    pub fn flash_mut(&mut self) -> &mut F {
        &mut self.flash
    }

    pub fn is_empty(&self, file_id: FileID) -> bool {
        self.files[file_id as usize].last_page.is_none()
    }

    pub fn read(&mut self, file_id: FileID) -> FileReader {
        FileReader::new(self, file_id)
    }

    pub fn write(&mut self, file_id: FileID) -> FileWriter {
        FileWriter::new(self, file_id)
    }

    pub fn file_flags(&self, file_id: FileID) -> u8 {
        self.files[file_id as usize].flags
    }

    pub fn files_with_flag(&self, flag: u8) -> impl Iterator<Item = FileID> + '_ {
        (0..FILE_COUNT as FileID).filter(move |&i| self.file_flags(i) & flag != 0)
    }

    pub fn format(&mut self) {
        // Erase all meta pages.
        for page_id in 0..PAGE_COUNT {
            let page_id = PageID::from_raw(page_id as _).unwrap();
            if let Ok(h) = self.read_header::<MetaHeader>(page_id) {
                self.flash.erase(page_id);
            }
        }

        // Write initial meta page.
        let page_id = PageID::from_raw(0).unwrap();
        let mut w = self.write_page(page_id);
        w.write_header(&mut self.flash, MetaHeader { seq: Seq(1) });
    }

    pub fn mount(&mut self) -> Result<(), Error> {
        self.alloc.reset();

        let mut meta_page_id = None;
        let mut meta_seq = Seq::ZERO;
        for page_id in 0..PAGE_COUNT {
            let page_id = PageID::from_raw(page_id as _).unwrap();
            if let Ok(h) = self.read_header::<MetaHeader>(page_id) {
                if h.seq > meta_seq {
                    meta_page_id = Some(page_id);
                    meta_seq = h.seq;
                }
            }
        }

        let Some(meta_page_id) = meta_page_id else {
            debug!("Meta page not found");
            corrupted!()
        };
        self.meta_page_id = meta_page_id;
        self.meta_seq = meta_seq;
        self.alloc.mark_used(meta_page_id);

        let (_, mut r) = self.read_page::<MetaHeader>(meta_page_id).inspect_err(|e| {
            debug!("failed read meta_page_id={:?}: {:?}", meta_page_id, e);
        })?;

        let mut files = [FileMeta {
            file_id: 0,
            flags: 0,
            last_page_id: OptionPageID::none(),
            first_seq: Seq::ZERO,
        }; FILE_COUNT];
        loop {
            let mut meta = [0; FileMeta::SIZE];
            let n = r.read(&mut self.flash, &mut meta)?;
            if n == 0 {
                break;
            }
            if n != FileMeta::SIZE {
                debug!("meta page last entry incomplete, size {}", n);
                corrupted!();
            }

            let meta = FileMeta::from_bytes(meta);
            if meta.file_id >= FILE_COUNT as _ {
                debug!("meta file_id out of range: {}", meta.file_id);
                corrupted!();
            }

            if let Some(page_id) = meta.last_page_id.into_option() {
                if page_id.index() >= PAGE_COUNT {
                    debug!("meta last_page_id out of range: {}", meta.file_id);
                    corrupted!();
                }
            } else {
                if meta.first_seq.0 != 0 {
                    debug!("meta last_page_id invalid, but first seq nonzero: {}", meta.file_id);
                    corrupted!();
                }
            }

            files[meta.file_id as usize] = meta
        }

        for file_id in 0..FILE_COUNT as FileID {
            let meta = files[file_id as usize];

            let Some(last_page_id) = meta.last_page_id.into_option() else {
                continue;
            };

            let (h, mut r) = self.read_page::<DataHeader>(last_page_id).inspect_err(|e| {
                debug!("read last_page_id={:?} file_id={}: {:?}", last_page_id, file_id, e);
            })?;
            let page_len = r.skip(&mut self.flash, PAGE_SIZE)?;
            let last_seq = h.seq.add(page_len)?;

            let mut p = Some(PagePointer {
                page_id: last_page_id,
                header: h,
            });

            // note: first_seq == last_seq is corruption too, because in that case what we do is delete the file.
            if meta.first_seq >= last_seq {
                debug!(
                    "meta: file {} first_seq {:?} not smaller than last_seq {:?}",
                    file_id, meta.first_seq, last_seq
                );
                corrupted!();
            }

            self.files[file_id as usize] = FileState {
                dirty: false,
                last_page: p,
                first_seq: meta.first_seq,
                last_seq,
                flags: meta.flags,
            };

            while let Some(pp) = p {
                if self.alloc.is_used(pp.page_id) {
                    info!("page used by multiple files at the same time. page_id={:?}", pp.page_id);
                    corrupted!();
                }
                self.alloc.mark_used(pp.page_id);
                p = pp.prev(self, meta.first_seq)?;
            }
        }

        Ok(())
    }

    pub fn transaction(&mut self) -> Transaction<'_, F> {
        Transaction { m: self }
    }

    // convenience method
    pub fn commit(&mut self, w: &mut FileWriter) -> Result<(), Error> {
        let mut tx = self.transaction();
        w.commit(&mut tx)?;
        tx.commit()?;
        Ok(())
    }

    // convenience method
    pub fn truncate(&mut self, file_id: FileID, bytes: usize) -> Result<(), Error> {
        let mut tx = self.transaction();
        tx.truncate(file_id, bytes)?;
        tx.commit()?;
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
            self.free_page(pp.page_id);
            from = pp.prev(self, seq_limit)?;
        }
        Ok(())
    }

    fn read_page<H: Header>(&mut self, page_id: PageID) -> Result<(H, PageReader), Error> {
        self.pages.read(&mut self.flash, page_id)
    }

    fn read_header<H: Header>(&mut self, page_id: PageID) -> Result<H, Error> {
        self.pages.read_header(&mut self.flash, page_id)
    }

    fn write_page<H: Header>(&mut self, page_id: PageID) -> PageWriter<H> {
        self.pages.write(&mut self.flash, page_id)
    }

    fn free_page(&mut self, page_id: PageID) {
        trace!("free page {:?}", page_id);
        self.alloc.free(page_id);
        #[cfg(feature = "_erase-on-free")]
        self.flash.erase(page_id);
    }

    #[cfg(feature = "std")]
    pub fn dump(&mut self) {
        for file_id in 0..FILE_COUNT {
            debug!("====== FILE {} ======", file_id);
            if let Err(e) = self.dump_file(file_id as _) {
                debug!("failed to dump file: {:?}", e);
            }
        }
    }

    #[cfg(feature = "std")]
    pub fn dump_file(&mut self, file_id: FileID) -> Result<(), Error> {
        let f = self.files[file_id as usize];
        debug!(
            "  seq: {:?}..{:?} len {:?} last_page {:?}",
            f.first_seq,
            f.last_seq,
            f.last_seq.sub(f.first_seq),
            f.last_page.map(|p| p.page_id)
        );

        let mut pages = Vec::new();
        let mut pp = f.last_page;
        while let Some(p) = pp {
            pages.push(p);
            pp = p.prev(self, f.first_seq)?;
        }

        let mut buf = [0; 1024];
        for p in pages.iter().rev() {
            let (h, mut r) = self.read_page::<DataHeader>(p.page_id)?;
            let n = r.read(&mut self.flash, &mut buf)?;
            let data = &buf[..n];

            let rb = if h.record_boundary == u16::MAX {
                "None".to_string()
            } else {
                format!(
                    "{} (seq {:?})",
                    h.record_boundary,
                    h.seq.add(h.record_boundary as usize)?
                )
            };

            debug!(
                "  page {:?}: seq {:?}..{:?} len {:?} record_boundary {} skiplist {:?}",
                p.page_id,
                h.seq,
                h.seq.add(n)?,
                n,
                rb,
                h.skiplist
            );

            let mut s = h.seq;
            for c in data.chunks(32) {
                debug!("     {:04}: {:02x?}", s.0, c);
                s = s.add(c.len())?;
            }
        }

        Ok(())
    }
}

pub struct Transaction<'a, F: Flash> {
    m: &'a mut FileManager<F>,
}

impl<'a, F: Flash> Drop for Transaction<'a, F> {
    fn drop(&mut self) {
        // TODO: if a transaction is aborted halfway, mark the FileManager
        // as inconsistent, so that it is remounted at next operation.
    }
}

impl<'a, F: Flash> Transaction<'a, F> {
    pub fn set_flags(&mut self, file_id: FileID, flags: u8) -> Result<(), Error> {
        let f = &mut self.m.files[file_id as usize];
        // flags only stick to nonempty files.
        if f.last_page.is_some() && f.flags != flags {
            f.flags = flags;
            f.dirty = true;
        }
        Ok(())
    }

    pub fn rename(&mut self, from: FileID, to: FileID) -> Result<(), Error> {
        self.m.files.swap(from as usize, to as usize);
        self.m.files[from as usize].dirty = true;
        self.m.files[to as usize].dirty = true;
        Ok(())
    }

    pub fn truncate(&mut self, file_id: FileID, bytes: usize) -> Result<(), Error> {
        if bytes == 0 {
            return Ok(());
        }

        let f = &mut self.m.files[file_id as usize];
        let old_f = *f;

        let len = f.last_seq.sub(f.first_seq);
        let seq = f.first_seq.add(len.min(bytes))?;

        let old_seq = f.first_seq;
        let p = if seq == f.last_seq {
            f.last_page
        } else {
            self.m.get_file_page(file_id, seq)?.unwrap().prev(self.m, old_seq)?
        };
        self.m.free_between(p, None, old_seq)?;

        let f = &mut self.m.files[file_id as usize];
        if seq == f.last_seq {
            f.first_seq = Seq::ZERO;
            f.last_seq = Seq::ZERO;
            f.last_page = None;
            f.flags = 0;
        } else {
            f.first_seq = seq;
        }
        f.dirty = true;

        trace!(
            "truncate file_id={:?} trunc_len={:?} old=(first_seq={:?} last_seq={:?}) new=(first_seq={:?} last_seq={:?})",
            file_id,
            bytes,
            old_f.first_seq,
            old_f.last_seq,
            f.first_seq,
            f.last_seq
        );

        Ok(())
    }

    fn write_file_meta(&mut self, w: &mut PageWriter<MetaHeader>, file_id: FileID) -> Result<(), WriteError> {
        let f = &self.m.files[file_id as usize];
        let meta = FileMeta {
            file_id,
            flags: f.flags,
            first_seq: f.first_seq,
            last_page_id: f.last_page.as_ref().map(|pp| pp.page_id).into(),
        };
        let n = w.write(&mut self.m.flash, &meta.to_bytes());
        if n != FileMeta::SIZE {
            return Err(WriteError::Full);
        }

        Ok(())
    }

    pub fn commit(mut self) -> Result<(), Error> {
        // Try appending to the existing meta page.
        let res: Result<(), WriteError> = try {
            let (_, mut mw) = self.m.pages.write_append(&mut self.m.flash, self.m.meta_page_id)?;
            for file_id in 0..FILE_COUNT {
                if self.m.files[file_id].dirty {
                    self.write_file_meta(&mut mw, file_id as FileID)?;
                }
            }
            mw.commit(&mut self.m.flash);
        };

        match res {
            Ok(()) => Ok(()),
            Err(WriteError::Corrupted) => corrupted!(),
            Err(WriteError::Full) => {
                // Existing meta page was full. Write a new one.

                let page_id = self.m.alloc.allocate();
                trace!("meta: allocated page {:?}", page_id);
                let mut w = self.m.write_page(page_id);
                for file_id in 0..FILE_COUNT as FileID {
                    // Since we're writing a new page from scratch, no need to
                    // write metas for empty files.
                    if self.m.files[file_id as usize].last_page.is_some() {
                        self.write_file_meta(&mut w, file_id).unwrap();
                    }
                }

                self.m.meta_seq = self.m.meta_seq.add(1)?; // TODO handle wraparound
                w.write_header(&mut self.m.flash, MetaHeader { seq: self.m.meta_seq });
                w.commit(&mut self.m.flash);

                // free the old one.
                self.m.free_page(self.m.meta_page_id);
                self.m.meta_page_id = page_id;

                Ok(())
            }
        }
    }
}

/// "cursor" pointing to a page within a file.
#[derive(Clone, Copy, Debug)]
struct PagePointer {
    page_id: PageID,
    header: DataHeader,
}

impl PagePointer {
    fn prev(self, m: &mut FileManager<impl Flash>, seq_limit: Seq) -> Result<Option<PagePointer>, Error> {
        if self.header.seq <= seq_limit {
            return Ok(None);
        }

        let Some(p2) = self.header.skiplist[0].into_option() else {
            return Ok(None);
        };

        if p2.index() >= PAGE_COUNT {
            debug!("prev page out of range {:?}", p2);
            corrupted!();
        }

        let h2 = check_corrupted!(m.read_header::<DataHeader>(p2));

        // Check seq always decreases. This avoids infinite loops
        // TODO we can make this check stricter: h2.seq == self.header.seq - page_len
        if h2.seq >= self.header.seq {
            debug!(
                "seq not decreasing when walking back: curr={:?} prev={:?}",
                self.header.seq, h2.seq
            );
            corrupted!();
        }
        Ok(Some(PagePointer {
            page_id: p2,
            header: h2,
        }))
    }

    fn prev_seq(mut self, m: &mut FileManager<impl Flash>, seq: Seq) -> Result<PagePointer, Error> {
        while self.header.seq > seq {
            let i = skiplist_index(seq, self.header.seq);
            let Some(p2) = self.header.skiplist[i].into_option() else {
                debug!("no prev page??");
                corrupted!();
            };
            if p2.index() >= PAGE_COUNT {
                debug!("prev page out of range {:?}", p2);
                corrupted!();
            }

            let h2 = check_corrupted!(m.read_header::<DataHeader>(p2));

            // Check seq always decreases. This avoids infinite loops
            if h2.seq >= self.header.seq {
                debug!(
                    "seq not decreasing when walking back: curr={:?} prev={:?}",
                    self.header.seq, h2.seq
                );
                corrupted!();
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

    pub fn curr_seq(&mut self, m: &mut FileManager<impl Flash>) -> Seq {
        match &self.state {
            ReaderState::Created => m.files[self.file_id as usize].first_seq,
            ReaderState::Reading(s) => s.seq,
            ReaderState::Finished => unreachable!(),
        }
    }

    fn page_id(&self) -> Option<PageID> {
        match &self.state {
            ReaderState::Reading(r) => Some(r.reader.page_id()),
            _ => None,
        }
    }
    fn next_page(&mut self, m: &mut FileManager<impl Flash>) -> Result<(), Error> {
        let seq = self.curr_seq(m);

        let prev_page_id = self.page_id();

        self.seek_seq(m, seq)?;

        let curr_page_id = self.page_id();
        if prev_page_id == curr_page_id && curr_page_id.is_some() {
            // prevent infinite loopwhen corrupted zero-len pages.
            corrupted!()
        }

        Ok(())
    }

    fn seek_seq(&mut self, m: &mut FileManager<impl Flash>, seq: Seq) -> Result<(), Error> {
        self.state = match m.get_file_page(self.file_id, seq)? {
            Some(pp) => {
                let (h, mut r) = m.read_page::<DataHeader>(pp.page_id).inspect_err(|e| {
                    debug!("failed read next page={:?}: {:?}", pp.page_id, e);
                })?;
                let n = (seq.sub(h.seq)) as usize;
                let got_n = r.skip(&mut m.flash, n)?;
                let eof = r.is_at_eof(&mut m.flash)?;
                if n != got_n || eof {
                    debug!(
                        "found seq hole in file. page={:?} h.seq={:?} seq={:?} n={} got_n={} eof={}",
                        pp.page_id, h.seq, seq, n, got_n, eof
                    );
                    corrupted!();
                }
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
                    let n = s.reader.read(&mut m.flash, data)?;
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
                let n = s.reader.skip(&mut m.flash, len)?;
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

    pub fn offset(&mut self, m: &mut FileManager<impl Flash>) -> usize {
        let first_seq = m.files[self.file_id as usize].first_seq;
        self.curr_seq(m).sub(first_seq)
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

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub enum SearchSeekError {
    TooMuchLeft,
    Corrupted,
}

impl From<Error> for SearchSeekError {
    fn from(e: Error) -> Self {
        match e {
            Error::Corrupted => Self::Corrupted,
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub enum WriteError {
    Full,
    Corrupted,
}

impl From<Error> for WriteError {
    fn from(e: Error) -> Self {
        match e {
            Error::Corrupted => Self::Corrupted,
        }
    }
}

pub struct FileSearcher {
    r: FileReader,

    result: Seq,

    left: Seq,

    right: Seq,
    right_skiplist: [OptionPageID; SKIPLIST_LEN],

    curr_low: Seq,
    curr_mid: Seq,
    curr_high: Seq,
    curr_page: OptionPageID,
    curr_skiplist: [OptionPageID; SKIPLIST_LEN],
}

impl FileSearcher {
    pub fn new(r: FileReader) -> Self {
        Self {
            r,
            result: Seq::MAX,
            left: Seq::MAX,
            right: Seq::MAX,
            right_skiplist: [OptionPageID::none(); SKIPLIST_LEN],
            curr_low: Seq::MAX,
            curr_mid: Seq::MAX,
            curr_high: Seq::MAX,
            curr_page: OptionPageID::none(),
            curr_skiplist: [OptionPageID::none(); SKIPLIST_LEN],
        }
    }

    pub fn start(&mut self, m: &mut FileManager<impl Flash>) -> Result<bool, Error> {
        let f = &m.files[self.r.file_id as usize];
        self.result = f.first_seq;
        self.left = f.first_seq;
        self.right = f.last_seq;

        match f.last_page {
            Some(pp) => {
                if f.last_seq <= pp.header.seq {
                    corrupted!();
                }

                // Create skiplist.
                self.right_skiplist = pp.header.skiplist;
                let top = skiplist_index(pp.header.seq, f.last_seq) + 1;
                self.right_skiplist[..top].fill(pp.page_id.into());

                trace!(
                    "search start file={:?}: left {:?} right {:?} right_skiplist {:?}",
                    self.r.file_id,
                    self.left,
                    self.right,
                    self.right_skiplist
                );
                self.really_seek(m)
            }
            None => {
                trace!("search start file={:?}: empty file", self.r.file_id);
                Ok(false)
            }
        }
    }

    pub fn reader(&mut self) -> &mut FileReader {
        &mut self.r
    }

    fn really_seek(&mut self, m: &mut FileManager<impl Flash>) -> Result<bool, Error> {
        let left = self.left.add(1).unwrap();
        let mut i = if left >= self.right {
            0
        } else {
            skiplist_index(left, self.right)
        };

        loop {
            if self.right > self.left {
                if let Some(page_id) = self.right_skiplist[i].into_option() {
                    let seq = skiplist_seq(self.right, i);
                    if seq >= self.left {
                        match self.seek_to_page(m, page_id, seq) {
                            Ok(()) => return Ok(true),
                            Err(SearchSeekError::Corrupted) => corrupted!(),
                            Err(SearchSeekError::TooMuchLeft) => {
                                let new_left = seq.add(1).unwrap();
                                assert!(new_left >= self.left);
                                self.left = new_left;
                            }
                        }
                    }
                }
            }

            if i == 0 {
                let seq = self.result;
                self.reader().seek_seq(m, seq)?;
                return Ok(false);
            }

            // Seek failed. Try again less hard.
            i -= 1;
        }
    }

    fn seek_to_page(
        &mut self,
        m: &mut FileManager<impl Flash>,
        mut page_id: PageID,
        target_seq: Seq,
    ) -> Result<(), SearchSeekError> {
        trace!("search: seek_to_page page_id={:?} target_seq={:?}", page_id, target_seq,);

        let mut right_limit = self.right;

        let (h, mut r) = loop {
            if page_id.index() >= PAGE_COUNT {
                corrupted!()
            }
            let (h, r) = m.read_page::<DataHeader>(page_id).inspect_err(|e| {
                debug!("failed read next page={:?}: {:?}", page_id, e);
            })?;

            if h.seq >= right_limit || h.seq > target_seq {
                corrupted!()
            }

            if h.seq <= self.left {
                // previous page is truncated.
                trace!("search: seek_to_page page hit self.left");
                return Err(SearchSeekError::TooMuchLeft);
            }

            if h.record_boundary != u16::MAX {
                break (h, r);
            }

            // otherwise we're guaranteed the previous page is valid, thanks to the
            // 'h.seq <= self.left` check above. so try again with it.

            // No record boundary within this page. Try the previous one.
            if let Some(prev) = h.skiplist[0].into_option() {
                page_id = prev;
                trace!("search: no record boundary, trying again with page {:?}", page_id);
            } else {
                debug!("first page in file has no record boundary!");
                corrupted!()
            }

            // prevent infinite loops on corrupted flash images.
            right_limit = h.seq;
        };

        // seek to record start.
        assert!(h.record_boundary != u16::MAX);

        let b = h.record_boundary as usize;
        if b >= PAGE_MAX_PAYLOAD_SIZE {
            corrupted!()
        }

        let boundary_seq = check_corrupted!(h.seq.add(b));
        if boundary_seq >= right_limit {
            corrupted!()
        }

        // If page has a record boundary, check it's within bounds.
        // It could be that the file has been truncated at a seq that falls in the
        // middle of the page, so the start of the page contains truncated data
        // that we should pretend it's not there.
        if boundary_seq <= self.left {
            trace!("search: seek_to_page: page OK, but record boundary hit self.left");
            return Err(SearchSeekError::TooMuchLeft);
        }

        let n = r.skip(&mut m.flash, b)?;
        if n != b {
            corrupted!()
        }
        self.curr_mid = boundary_seq;
        self.curr_high = target_seq.max(boundary_seq);

        self.r.state = ReaderState::Reading(ReaderStateReading {
            seq: self.curr_mid,
            reader: r,
        });
        self.curr_low = h.seq;
        self.curr_skiplist = h.skiplist;
        self.curr_page = page_id.into();
        trace!(
            "search: curr seq={:?}..{:?}..{:?} page {:?} skiplist={:?}",
            self.curr_low,
            self.curr_mid,
            self.curr_high,
            self.curr_page,
            self.curr_skiplist
        );
        trace!("        result seq={:?}", self.result);
        trace!("        left seq={:?}", self.left);
        trace!(
            "        right seq={:?}   skiplist={:?}",
            self.right,
            self.right_skiplist
        );

        assert!(self.left <= self.curr_low);
        assert!(self.curr_low <= self.curr_mid);
        assert!(self.curr_mid <= self.curr_high);
        assert!(self.curr_high <= self.right);

        Ok(())
    }

    pub fn seek(&mut self, m: &mut FileManager<impl Flash>, dir: SeekDirection) -> Result<bool, Error> {
        match dir {
            SeekDirection::Left => {
                trace!("search seek left");
                self.right = self.curr_low;
                self.right_skiplist = self.curr_skiplist;
            }
            SeekDirection::Right => {
                trace!("search seek right");
                self.left = self.curr_high.add(1).unwrap();
                self.result = self.curr_mid;
            }
        }

        self.really_seek(m)
    }
}

pub struct FileWriter {
    file_id: FileID,
    last_page: Option<PagePointer>,
    seq: Seq,
    writer: Option<PageWriter<DataHeader>>,

    at_record_boundary: bool,
    record_boundary: Option<u16>,
}

impl FileWriter {
    fn new(m: &mut FileManager<impl Flash>, file_id: FileID) -> Self {
        let f = &m.files[file_id as usize];

        Self {
            file_id,
            last_page: f.last_page,
            seq: f.last_seq,
            at_record_boundary: true,
            record_boundary: Some(0),
            writer: None,
        }
    }

    fn curr_seq(&mut self, m: &mut FileManager<impl Flash>) -> Seq {
        let n = self.writer.as_ref().map(|w| w.len()).unwrap_or(0);
        self.seq.add(n).unwrap()
    }

    pub fn offset(&mut self, m: &mut FileManager<impl Flash>) -> usize {
        let first_seq = m.files[self.file_id as usize].first_seq;
        self.curr_seq(m).sub(first_seq)
    }

    fn flush_header(&mut self, m: &mut FileManager<impl Flash>, mut w: PageWriter<DataHeader>) -> Result<(), Error> {
        let page_size = w.len();
        let page_id = w.page_id();
        let mut skiplist = [OptionPageID::none(); SKIPLIST_LEN];
        if let Some(last_page) = &self.last_page {
            skiplist = last_page.header.skiplist;

            let top = skiplist_index(last_page.header.seq, self.seq) + 1;
            skiplist[..top].fill(last_page.page_id.into());
        }

        let next_seq = self.seq.add(page_size)?;

        let record_boundary = match self.record_boundary {
            Some(b) if (b as usize) < page_size => b,
            _ => u16::MAX,
        };
        let header = DataHeader {
            seq: self.seq,
            skiplist,
            record_boundary,
        };
        w.write_header(&mut m.flash, header);
        w.commit(&mut m.flash);

        trace!(
            "flush_header: page={:?} h={:?} record_boundary={:?}",
            page_id,
            header,
            self.record_boundary
        );

        self.seq = next_seq;
        self.last_page = Some(PagePointer { page_id, header });

        self.record_boundary = None;
        if self.at_record_boundary {
            self.record_boundary = Some(0)
        }

        Ok(())
    }

    fn next_page(&mut self, m: &mut FileManager<impl Flash>) -> Result<(), Error> {
        if let Some(w) = mem::replace(&mut self.writer, None) {
            self.flush_header(m, w)?;
        }

        let page_id = m.alloc.allocate();
        trace!("writer: allocated page {:?}", page_id);
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

                    // Wrote some data, we're no longer at a boundary.
                    self.at_record_boundary = false;
                }
            }
        }
        Ok(())
    }

    pub fn commit(&mut self, tx: &mut Transaction<'_, impl Flash>) -> Result<(), Error> {
        if let Some(w) = mem::replace(&mut self.writer, None) {
            self.flush_header(tx.m, w)?;
            let f = &mut tx.m.files[self.file_id as usize];
            let old_f = *f;
            f.last_page = self.last_page;
            f.last_seq = self.seq;
            f.dirty = true;

            trace!(
                "commit file_id={:?} old=(first_seq={:?} last_seq={:?}) new=(first_seq={:?} last_seq={:?})",
                self.file_id,
                old_f.first_seq,
                old_f.last_seq,
                f.first_seq,
                f.last_seq
            );
        }
        Ok(())
    }

    pub fn discard(&mut self, m: &mut FileManager<impl Flash>) {
        if let Some(w) = &self.writer {
            // Free the page we're writing now (not yet committed)
            let page_id = w.page_id();
            m.free_page(page_id);

            // Free previous pages, if any
            let f = &m.files[self.file_id as usize];
            m.free_between(self.last_page, f.last_page, Seq::ZERO).unwrap();
        };
    }

    pub fn record_end(&mut self) {
        if self.record_boundary.is_none() {
            self.record_boundary = Some(self.writer.as_mut().unwrap().len().try_into().unwrap());
        }
        self.at_record_boundary = true;
    }

    pub fn space_left_on_current_page(&self) -> usize {
        match &self.writer {
            None => 0,
            Some(w) => PAGE_MAX_PAYLOAD_SIZE - w.len(),
        }
    }
}

#[repr(transparent)]
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub struct Seq(pub u32);

impl fmt::Display for Seq {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl fmt::Debug for Seq {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Seq {
    pub const ZERO: Self = Self(0);
    pub const MAX: Self = Self(u32::MAX);

    fn sub(self, other: Self) -> usize {
        self.0.checked_sub(other.0).unwrap() as _
    }

    fn add(self, offs: usize) -> Result<Self, Error> {
        let Ok(offs_u32) = offs.try_into() else {
            debug!("seq add overflow, offs doesn't fit u32: {}", offs);
            corrupted!();
        };
        let Some(res) = self.0.checked_add(offs_u32) else {
            debug!("seq add overflow, self={} offs={}", self.0, offs_u32);
            corrupted!();
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

/// Calculate skiplist index.
///
/// Requires `left < right`.
///
/// For building the skiplist: if the previous page has sequence numbers `left..right`,
/// what's the highest index that should be made to point to the previous page?
///
/// For iterating the skiplist: if we're at `right` and we want to seek backwards until
/// `left`, what's the highest index that we can use to jump back, without overshooting?
fn skiplist_index(left: Seq, right: Seq) -> usize {
    let bits = max_trailing_zeros_between(left.0, right.0) as usize;
    bits.saturating_sub(SKIPLIST_SHIFT).min(SKIPLIST_LEN - 1)
}

/// Calculate the destination seq of a skiplist jump.
///
/// Requires `curr` != 0.
///
/// If the current page starts at seq `curr`, and we jump backwards using the skiplist index
/// `index`, what's the sequence number the destination page is guaranteed to contain?
///
/// Note that the destination page will *contain* the returned seq, but it can *start*
/// earlier.
///
/// This is the inverse operation to `skiplist_index`, sort of.
fn skiplist_seq(curr: Seq, index: usize) -> Seq {
    let curr = curr.0.checked_sub(1).unwrap();
    let bits = match index {
        0 => 0,
        _ => index + SKIPLIST_SHIFT,
    };
    Seq(curr >> bits << bits)
}

#[cfg(test)]
mod tests {
    use rand::Rng;
    use test_log::test;

    use super::*;
    use crate::flash::MemFlash;
    use crate::types::RawPageID;

    fn page(p: RawPageID) -> PageID {
        PageID::from_raw(p).unwrap()
    }

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

        m.truncate(0, 2).unwrap();

        let mut r = m.read(0);
        let mut buf = [0; 3];
        r.read(&mut m, &mut buf).unwrap();
        assert_eq!(buf, [3, 4, 5]);

        m.truncate(0, 1).unwrap();

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

        let mut tx = m.transaction();
        w.commit(&mut tx).unwrap();
        tx.truncate(0, 2).unwrap();
        tx.commit().unwrap();

        let mut r = m.read(0);
        let mut buf = [0; 7];
        r.read(&mut m, &mut buf).unwrap();
        assert_eq!(buf, [3, 4, 5, 6, 7, 8, 9]);

        m.truncate(0, 1).unwrap();

        let mut r = m.read(0);
        let mut buf = [0; 6];
        r.read(&mut m, &mut buf).unwrap();
        assert_eq!(buf, [4, 5, 6, 7, 8, 9]);

        m.truncate(0, 5).unwrap();

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

        assert_eq!(m.alloc.is_used(page(1)), true);

        m.truncate(0, 5).unwrap();

        assert_eq!(m.alloc.is_used(page(1)), false);

        // Remount
        m.mount().unwrap();

        assert_eq!(m.alloc.is_used(page(1)), false);

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

        assert_eq!(m.alloc.is_used(page(1)), false);

        let mut w = m.write(0);
        w.write(&mut m, &[1, 2, 3, 4, 5]).unwrap();
        m.commit(&mut w).unwrap();

        assert_eq!(m.alloc.is_used(page(1)), true);

        m.truncate(0, 5).unwrap();

        assert_eq!(m.alloc.is_used(page(1)), false);

        // Remount
        m.mount().unwrap();

        assert_eq!(m.alloc.is_used(page(1)), false);

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

        assert_eq!(m.alloc.is_used(page(1)), false);

        let data = dummy_data(PAGE_MAX_PAYLOAD_SIZE);

        let mut w = m.write(0);
        w.write(&mut m, &data).unwrap();
        w.write(&mut m, &data).unwrap();
        m.commit(&mut w).unwrap();

        assert_eq!(m.alloc.is_used(page(1)), true);
        assert_eq!(m.alloc.is_used(page(2)), true);

        m.truncate(0, PAGE_MAX_PAYLOAD_SIZE).unwrap();
        assert_eq!(m.alloc.is_used(page(1)), false);
        assert_eq!(m.alloc.is_used(page(2)), true);

        m.truncate(0, PAGE_MAX_PAYLOAD_SIZE).unwrap();
        assert_eq!(m.alloc.is_used(page(1)), false);
        assert_eq!(m.alloc.is_used(page(2)), false);

        // Remount
        m.mount().unwrap();

        assert_eq!(m.alloc.is_used(page(1)), false);
        assert_eq!(m.alloc.is_used(page(2)), false);

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

        assert_eq!(m.alloc.is_used(page(1)), false);
        assert_eq!(m.alloc.is_used(page(2)), false);

        let data = dummy_data(PAGE_MAX_PAYLOAD_SIZE);
        let mut w = m.write(0);

        w.write(&mut m, &data).unwrap();
        assert_eq!(m.alloc.is_used(page(0)), true); // old meta
        assert_eq!(m.alloc.is_used(page(1)), true);
        assert_eq!(m.alloc.is_used(page(2)), false);
        assert_eq!(m.alloc.is_used(page(3)), false);

        w.write(&mut m, &data).unwrap();
        assert_eq!(m.alloc.is_used(page(0)), true); // old meta
        assert_eq!(m.alloc.is_used(page(1)), true);
        assert_eq!(m.alloc.is_used(page(2)), true);
        assert_eq!(m.alloc.is_used(page(3)), false);

        m.commit(&mut w).unwrap();
        assert_eq!(m.alloc.is_used(page(0)), true); // old meta, appended in-place.
        assert_eq!(m.alloc.is_used(page(1)), true);
        assert_eq!(m.alloc.is_used(page(2)), true);
        assert_eq!(m.alloc.is_used(page(3)), false);

        // Remount
        m.mount().unwrap();
        assert_eq!(m.alloc.is_used(page(0)), true); // old meta, appended in-place.
        assert_eq!(m.alloc.is_used(page(1)), true);
        assert_eq!(m.alloc.is_used(page(2)), true);
        assert_eq!(m.alloc.is_used(page(3)), false);
    }

    #[test]
    fn test_alloc_discard_1page() {
        let mut f = MemFlash::new();
        let mut m = FileManager::new(&mut f);
        m.format();
        m.mount().unwrap();

        assert_eq!(m.alloc.is_used(page(0)), true);
        assert_eq!(m.alloc.is_used(page(1)), false);
        assert_eq!(m.alloc.is_used(page(2)), false);

        let data = dummy_data(PAGE_MAX_PAYLOAD_SIZE);
        let mut w = m.write(0);

        w.write(&mut m, &data).unwrap();
        assert_eq!(m.alloc.is_used(page(0)), true);
        assert_eq!(m.alloc.is_used(page(1)), true);
        assert_eq!(m.alloc.is_used(page(2)), false);

        w.discard(&mut m);
        assert_eq!(m.alloc.is_used(page(0)), true);
        assert_eq!(m.alloc.is_used(page(1)), false);
        assert_eq!(m.alloc.is_used(page(2)), false);

        // Remount
        m.mount().unwrap();
        assert_eq!(m.alloc.is_used(page(0)), true);
        assert_eq!(m.alloc.is_used(page(1)), false);
        assert_eq!(m.alloc.is_used(page(2)), false);
    }

    #[test]
    fn test_alloc_discard_2page() {
        let mut f = MemFlash::new();
        let mut m = FileManager::new(&mut f);
        m.format();
        m.mount().unwrap();

        assert_eq!(m.alloc.is_used(page(0)), true);
        assert_eq!(m.alloc.is_used(page(1)), false);

        let data = dummy_data(PAGE_MAX_PAYLOAD_SIZE);
        let mut w = m.write(0);

        w.write(&mut m, &data).unwrap();
        assert_eq!(m.alloc.is_used(page(0)), true);
        assert_eq!(m.alloc.is_used(page(1)), true);
        assert_eq!(m.alloc.is_used(page(2)), false);

        w.write(&mut m, &data).unwrap();
        assert_eq!(m.alloc.is_used(page(0)), true);
        assert_eq!(m.alloc.is_used(page(1)), true);
        assert_eq!(m.alloc.is_used(page(2)), true);
        assert_eq!(m.alloc.is_used(page(3)), false);

        w.discard(&mut m);
        assert_eq!(m.alloc.is_used(page(0)), true);
        assert_eq!(m.alloc.is_used(page(1)), false);
        assert_eq!(m.alloc.is_used(page(2)), false);
        assert_eq!(m.alloc.is_used(page(3)), false);

        // Remount
        m.mount().unwrap();
        assert_eq!(m.alloc.is_used(page(0)), true);
        assert_eq!(m.alloc.is_used(page(1)), false);
        assert_eq!(m.alloc.is_used(page(2)), false);
        assert_eq!(m.alloc.is_used(page(3)), false);
    }

    #[test]
    fn test_alloc_discard_3page() {
        let mut f = MemFlash::new();
        let mut m = FileManager::new(&mut f);
        m.format();
        m.mount().unwrap();

        assert_eq!(m.alloc.is_used(page(0)), true);
        assert_eq!(m.alloc.is_used(page(1)), false);
        assert_eq!(m.alloc.is_used(page(2)), false);
        assert_eq!(m.alloc.is_used(page(3)), false);

        let data = dummy_data(PAGE_MAX_PAYLOAD_SIZE * 3);
        let mut w = m.write(0);
        w.write(&mut m, &data).unwrap();
        assert_eq!(m.alloc.is_used(page(0)), true);
        assert_eq!(m.alloc.is_used(page(1)), true);
        assert_eq!(m.alloc.is_used(page(2)), true);
        assert_eq!(m.alloc.is_used(page(3)), true);
        assert_eq!(m.alloc.is_used(page(4)), false);

        w.discard(&mut m);
        assert_eq!(m.alloc.is_used(page(0)), true);
        assert_eq!(m.alloc.is_used(page(1)), false);
        assert_eq!(m.alloc.is_used(page(2)), false);
        assert_eq!(m.alloc.is_used(page(3)), false);
        assert_eq!(m.alloc.is_used(page(4)), false);

        // Remount
        m.mount().unwrap();
        assert_eq!(m.alloc.is_used(page(0)), true);
        assert_eq!(m.alloc.is_used(page(1)), false);
        assert_eq!(m.alloc.is_used(page(2)), false);
        assert_eq!(m.alloc.is_used(page(3)), false);
        assert_eq!(m.alloc.is_used(page(4)), false);
    }

    #[test]
    fn test_append_alloc_discard() {
        let mut f = MemFlash::new();
        let mut m = FileManager::new(&mut f);
        m.format();
        m.mount().unwrap();

        assert_eq!(m.alloc.is_used(page(0)), true);
        assert_eq!(m.alloc.is_used(page(1)), false);

        let data = dummy_data(24);
        let mut w = m.write(0);
        w.write(&mut m, &data).unwrap();
        m.commit(&mut w).unwrap();
        assert_eq!(m.alloc.is_used(page(0)), true); // old meta, appended in-place.
        assert_eq!(m.alloc.is_used(page(1)), true);
        assert_eq!(m.alloc.is_used(page(2)), false);
        assert_eq!(m.alloc.is_used(page(3)), false);

        let mut w = m.write(0);
        w.write(&mut m, &data).unwrap();
        assert_eq!(m.alloc.is_used(page(0)), true);
        assert_eq!(m.alloc.is_used(page(1)), true);
        assert_eq!(m.alloc.is_used(page(2)), true);
        assert_eq!(m.alloc.is_used(page(3)), false);

        w.discard(&mut m);
        assert_eq!(m.alloc.is_used(page(0)), true);
        assert_eq!(m.alloc.is_used(page(1)), true);
        assert_eq!(m.alloc.is_used(page(2)), false);
        assert_eq!(m.alloc.is_used(page(3)), false);

        // Remount
        m.mount().unwrap();
        assert_eq!(m.alloc.is_used(page(0)), true);
        assert_eq!(m.alloc.is_used(page(1)), true);
        assert_eq!(m.alloc.is_used(page(2)), false);
        assert_eq!(m.alloc.is_used(page(3)), false);
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

    #[test]
    fn test_flags() {
        let mut f = MemFlash::new();
        let mut m = FileManager::new(&mut f);
        m.format();
        m.mount().unwrap();

        assert_eq!(m.file_flags(1), 0x00);

        // flags for empty files stay at 0.
        let mut tx = m.transaction();
        tx.set_flags(1, 0x42).unwrap();
        tx.commit().unwrap();
        assert_eq!(m.file_flags(1), 0x00);

        // flags for nonempty files get set properly.
        let mut w = m.write(1);
        w.write(&mut m, &[0x00]).unwrap();
        let mut tx = m.transaction();
        w.commit(&mut tx).unwrap();
        tx.set_flags(1, 0x42).unwrap();
        tx.commit().unwrap();
        assert_eq!(m.file_flags(1), 0x42);

        // when writing to a file, old flags are kept if we don't `.set_flags()`
        let mut w = m.write(1);
        w.write(&mut m, &[0x00]).unwrap();
        m.commit(&mut w).unwrap();
        assert_eq!(m.file_flags(1), 0x42);

        // flags are kept across remounts.
        m.mount().unwrap();
        assert_eq!(m.file_flags(1), 0x42);

        // when truncating the file, flags are kept.
        m.truncate(1, 1).unwrap();
        assert_eq!(m.file_flags(1), 0x42);

        // when deleting the file, flags are gone.
        m.truncate(1, 1).unwrap();
        assert_eq!(m.file_flags(1), 0x00);

        // Remount
        m.mount().unwrap();
        assert_eq!(m.file_flags(1), 0x00);
    }

    #[test]
    fn test_record_boundary_one() {
        let mut f = MemFlash::new();
        let mut m = FileManager::new(&mut f);
        m.format();
        m.mount().unwrap();

        let mut w = m.write(1);
        w.write(&mut m, &[0x00]).unwrap();
        w.record_end();
        m.commit(&mut w).unwrap();

        let h = m.read_header::<DataHeader>(page(1)).unwrap();
        assert_eq!(h.seq, Seq(0));
        assert_eq!(h.record_boundary, 0);
    }

    #[test]
    fn test_record_boundary_two() {
        let mut f = MemFlash::new();
        let mut m = FileManager::new(&mut f);
        m.format();
        m.mount().unwrap();

        let mut w = m.write(1);
        w.write(&mut m, &[0x00]).unwrap();
        w.record_end();
        w.write(&mut m, &[0x00; PAGE_MAX_PAYLOAD_SIZE + 1]).unwrap();
        w.record_end();
        m.commit(&mut w).unwrap();

        let h = m.read_header::<DataHeader>(page(1)).unwrap();
        assert_eq!(h.seq, Seq(0));
        assert_eq!(h.record_boundary, 0);

        let h = m.read_header::<DataHeader>(page(2)).unwrap();
        assert_eq!(h.seq, Seq(PAGE_MAX_PAYLOAD_SIZE as u32));
        assert_eq!(h.record_boundary, u16::MAX);
    }

    #[test]
    fn test_record_boundary_three() {
        let mut f = MemFlash::new();
        let mut m = FileManager::new(&mut f);
        m.format();
        m.mount().unwrap();

        let mut w = m.write(1);
        w.write(&mut m, &[0x00]).unwrap();
        w.record_end();
        w.write(&mut m, &[0x00; PAGE_MAX_PAYLOAD_SIZE + 1]).unwrap();
        w.record_end();
        w.write(&mut m, &[0x00]).unwrap();
        w.record_end();
        m.commit(&mut w).unwrap();

        let h = m.read_header::<DataHeader>(page(1)).unwrap();
        assert_eq!(h.seq, Seq(0));
        assert_eq!(h.record_boundary, 0);

        let h = m.read_header::<DataHeader>(page(2)).unwrap();
        assert_eq!(h.seq, Seq(PAGE_MAX_PAYLOAD_SIZE as u32));
        assert_eq!(h.record_boundary, 2);
    }

    #[test]
    fn test_record_boundary_overlong() {
        let mut f = MemFlash::new();
        let mut m = FileManager::new(&mut f);
        m.format();
        m.mount().unwrap();

        let mut w = m.write(1);
        w.write(&mut m, &[0x00]).unwrap();
        w.record_end();
        w.write(&mut m, &[0x00; PAGE_MAX_PAYLOAD_SIZE * 2 + 1]).unwrap();
        w.record_end();
        m.commit(&mut w).unwrap();

        let h = m.read_header::<DataHeader>(page(1)).unwrap();
        assert_eq!(h.seq, Seq(0));
        assert_eq!(h.record_boundary, 0);

        let h = m.read_header::<DataHeader>(page(2)).unwrap();
        assert_eq!(h.seq, Seq(PAGE_MAX_PAYLOAD_SIZE as u32));
        assert_eq!(h.record_boundary, u16::MAX);

        let h = m.read_header::<DataHeader>(page(3)).unwrap();
        assert_eq!(h.seq, Seq(PAGE_MAX_PAYLOAD_SIZE as u32 * 2));
        assert_eq!(h.record_boundary, u16::MAX);
    }

    #[test]
    fn test_record_boundary_overlong_2() {
        let mut f = MemFlash::new();
        let mut m = FileManager::new(&mut f);
        m.format();
        m.mount().unwrap();

        let mut w = m.write(1);
        w.write(&mut m, &[0x00]).unwrap();
        w.record_end();
        w.write(&mut m, &[0x00; PAGE_MAX_PAYLOAD_SIZE * 2 + 1]).unwrap();
        w.record_end();
        w.write(&mut m, &[0x00; PAGE_MAX_PAYLOAD_SIZE * 2 + 1]).unwrap();
        w.record_end();
        m.commit(&mut w).unwrap();

        let h = m.read_header::<DataHeader>(page(1)).unwrap();
        assert_eq!(h.seq, Seq(0));
        assert_eq!(h.record_boundary, 0);

        let h = m.read_header::<DataHeader>(page(2)).unwrap();
        assert_eq!(h.seq, Seq(PAGE_MAX_PAYLOAD_SIZE as u32));
        assert_eq!(h.record_boundary, u16::MAX);

        let h = m.read_header::<DataHeader>(page(3)).unwrap();
        assert_eq!(h.seq, Seq(PAGE_MAX_PAYLOAD_SIZE as u32 * 2));
        assert_eq!(h.record_boundary, 2);

        let h = m.read_header::<DataHeader>(page(4)).unwrap();
        assert_eq!(h.seq, Seq(PAGE_MAX_PAYLOAD_SIZE as u32 * 3));
        assert_eq!(h.record_boundary, u16::MAX);

        let h = m.read_header::<DataHeader>(page(5)).unwrap();
        assert_eq!(h.seq, Seq(PAGE_MAX_PAYLOAD_SIZE as u32 * 4));
        assert_eq!(h.record_boundary, u16::MAX);
    }

    #[test]
    fn test_record_boundary_overlong_3() {
        let mut f = MemFlash::new();
        let mut m = FileManager::new(&mut f);
        m.format();
        m.mount().unwrap();

        let mut w = m.write(1);
        w.write(&mut m, &[0x00]).unwrap();
        w.record_end();
        w.write(&mut m, &[0x00; PAGE_MAX_PAYLOAD_SIZE * 2 + 1]).unwrap();
        w.record_end();
        w.write(&mut m, &[0x00; PAGE_MAX_PAYLOAD_SIZE * 2 + 1]).unwrap();
        w.record_end();
        w.write(&mut m, &[0x00]).unwrap();
        w.record_end();
        w.write(&mut m, &[0x00]).unwrap();
        w.record_end();
        w.write(&mut m, &[0x00]).unwrap();
        w.record_end();

        m.commit(&mut w).unwrap();

        let h = m.read_header::<DataHeader>(page(1)).unwrap();
        assert_eq!(h.seq, Seq(0));
        assert_eq!(h.record_boundary, 0);

        let h = m.read_header::<DataHeader>(page(2)).unwrap();
        assert_eq!(h.seq, Seq(PAGE_MAX_PAYLOAD_SIZE as u32));
        assert_eq!(h.record_boundary, u16::MAX);

        let h = m.read_header::<DataHeader>(page(3)).unwrap();
        assert_eq!(h.seq, Seq(PAGE_MAX_PAYLOAD_SIZE as u32 * 2));
        assert_eq!(h.record_boundary, 2);

        let h = m.read_header::<DataHeader>(page(4)).unwrap();
        assert_eq!(h.seq, Seq(PAGE_MAX_PAYLOAD_SIZE as u32 * 3));
        assert_eq!(h.record_boundary, u16::MAX);

        let h = m.read_header::<DataHeader>(page(5)).unwrap();
        assert_eq!(h.seq, Seq(PAGE_MAX_PAYLOAD_SIZE as u32 * 4));
        assert_eq!(h.record_boundary, 3);
    }

    #[test]
    fn test_record_boundary_exact_page() {
        let mut f = MemFlash::new();
        let mut m = FileManager::new(&mut f);
        m.format();
        m.mount().unwrap();

        let mut w = m.write(1);
        w.write(&mut m, &[0x00; PAGE_MAX_PAYLOAD_SIZE]).unwrap();
        w.record_end();
        w.write(&mut m, &[0x00; PAGE_MAX_PAYLOAD_SIZE]).unwrap();
        w.record_end();
        w.write(&mut m, &[0x00]).unwrap();
        w.record_end();
        m.commit(&mut w).unwrap();

        let h = m.read_header::<DataHeader>(page(1)).unwrap();
        assert_eq!(h.seq, Seq(0));
        assert_eq!(h.record_boundary, 0);

        let h = m.read_header::<DataHeader>(page(2)).unwrap();
        assert_eq!(h.seq, Seq(PAGE_MAX_PAYLOAD_SIZE as u32));
        assert_eq!(h.record_boundary, 0);

        let h = m.read_header::<DataHeader>(page(3)).unwrap();
        assert_eq!(h.seq, Seq(PAGE_MAX_PAYLOAD_SIZE as u32 * 2));
        assert_eq!(h.record_boundary, 0);
    }

    #[test]
    fn test_search_empty() {
        let mut f = MemFlash::new();
        let mut m = FileManager::new(&mut f);
        m.format();
        m.mount().unwrap();

        let mut s = FileSearcher::new(m.read(1));
        assert_eq!(s.start(&mut m).unwrap(), false);
        assert_eq!(s.reader().offset(&mut m), 0);
    }

    #[test]
    fn test_search_one_page() {
        let mut f = MemFlash::new();
        let mut m = FileManager::new(&mut f);
        m.format();
        m.mount().unwrap();

        let mut w = m.write(1);
        w.write(&mut m, &[0x00]).unwrap();
        m.commit(&mut w).unwrap();

        let mut buf = [0u8; 1];

        // start immediately return false, because there's nothing to bisect.
        // Only possible point to seek is start of the only page.
        let mut s = FileSearcher::new(m.read(1));
        assert_eq!(s.start(&mut m).unwrap(), false);
        assert_eq!(s.reader().offset(&mut m), 0);
    }

    #[test]
    fn test_search_two_pages() {
        let mut f = MemFlash::new();
        let mut m = FileManager::new(&mut f);
        m.format();
        m.mount().unwrap();

        for _ in 0..2 {
            let mut w = m.write(1);
            w.write(&mut m, &[0x00]).unwrap();
            w.record_end();
            m.commit(&mut w).unwrap();
        }

        let mut s = FileSearcher::new(m.read(1));
        assert_eq!(s.start(&mut m).unwrap(), true);
        assert_eq!(s.reader().offset(&mut m), 1);
        assert_eq!(s.seek(&mut m, SeekDirection::Left).unwrap(), false);
        assert_eq!(s.reader().offset(&mut m), 0);

        let mut s = FileSearcher::new(m.read(1));
        assert_eq!(s.start(&mut m).unwrap(), true);
        assert_eq!(s.reader().offset(&mut m), 1);
        assert_eq!(s.seek(&mut m, SeekDirection::Right).unwrap(), false);
        assert_eq!(s.reader().offset(&mut m), 1);
    }

    #[test]
    fn test_search_no_boundary_on_second_page() {
        let mut f = MemFlash::new();
        let mut m = FileManager::new(&mut f);
        m.format();
        m.mount().unwrap();

        let mut w = m.write(1);
        w.write(&mut m, &[0x00; 238]).unwrap();
        w.record_end();
        m.commit(&mut w).unwrap();

        // start immediately return false, because there's nothing to bisect.
        // Only possible point to seek is start of the only page.
        let mut s = FileSearcher::new(m.read(1));
        assert_eq!(s.start(&mut m).unwrap(), false);
        assert_eq!(s.reader().offset(&mut m), 0);
    }

    #[test]
    fn test_search_no_boundary_more_pages() {
        let mut f = MemFlash::new();
        let mut m = FileManager::new(&mut f);
        m.format();
        m.mount().unwrap();

        let mut w = m.write(1);
        w.write(&mut m, &[0x00; 4348]).unwrap();
        w.record_end();
        m.commit(&mut w).unwrap();

        // start immediately return false, because there's nothing to bisect.
        // Only possible point to seek is start of the only page.
        let mut s = FileSearcher::new(m.read(1));
        assert_eq!(s.start(&mut m).unwrap(), false);
        assert_eq!(s.reader().offset(&mut m), 0);
    }

    #[test]
    fn test_search_no_boundary_more_pages_two() {
        let mut f = MemFlash::new();
        let mut m = FileManager::new(&mut f);
        m.format();
        m.mount().unwrap();

        let mut w = m.write(1);
        w.write(&mut m, &[0x00; 4348]).unwrap();
        w.record_end();
        w.write(&mut m, &[0x00; 4348]).unwrap();
        w.record_end();
        m.commit(&mut w).unwrap();

        let mut buf = [0u8; 1];
        // Seek left
        let mut s = FileSearcher::new(m.read(1));
        assert_eq!(s.start(&mut m).unwrap(), true);
        assert_eq!(s.reader().offset(&mut m), 4348);
        s.reader().read(&mut m, &mut buf).unwrap();
        assert_eq!(s.seek(&mut m, SeekDirection::Left).unwrap(), false);
        assert_eq!(s.reader().offset(&mut m), 0);

        // Seek right
        let mut s = FileSearcher::new(m.read(1));
        assert_eq!(s.start(&mut m).unwrap(), true);
        assert_eq!(s.reader().offset(&mut m), 4348);
        s.reader().read(&mut m, &mut buf).unwrap();
        assert_eq!(s.seek(&mut m, SeekDirection::Right).unwrap(), false);
        assert_eq!(s.reader().offset(&mut m), 4348);
    }

    #[test]
    fn test_search_no_boundary_more_pages_three() {
        let mut f = MemFlash::new();
        let mut m = FileManager::new(&mut f);
        m.format();
        m.mount().unwrap();

        let mut w = m.write(1);
        w.write(&mut m, &[0x00; 4348]).unwrap();
        w.record_end();
        w.write(&mut m, &[0x00; 4348]).unwrap();
        w.record_end();
        w.write(&mut m, &[0x00; 4348]).unwrap();
        w.record_end();
        m.commit(&mut w).unwrap();

        let mut buf = [0u8; 1];
        // Seek left
        let mut s = FileSearcher::new(m.read(1));
        assert_eq!(s.start(&mut m).unwrap(), true);
        assert_eq!(s.reader().offset(&mut m), 8696);
        s.reader().read(&mut m, &mut buf).unwrap();
        assert_eq!(s.seek(&mut m, SeekDirection::Left).unwrap(), true);
        assert_eq!(s.reader().offset(&mut m), 4348);
        s.reader().read(&mut m, &mut buf).unwrap();
        assert_eq!(s.seek(&mut m, SeekDirection::Left).unwrap(), false);
        assert_eq!(s.reader().offset(&mut m), 0);

        // Seek less left
        let mut s = FileSearcher::new(m.read(1));
        assert_eq!(s.start(&mut m).unwrap(), true);
        assert_eq!(s.reader().offset(&mut m), 8696);
        s.reader().read(&mut m, &mut buf).unwrap();
        assert_eq!(s.seek(&mut m, SeekDirection::Left).unwrap(), true);
        assert_eq!(s.reader().offset(&mut m), 4348);
        s.reader().read(&mut m, &mut buf).unwrap();
        assert_eq!(s.seek(&mut m, SeekDirection::Left).unwrap(), false);
        assert_eq!(s.reader().offset(&mut m), 0);

        // Seek middle
        let mut s = FileSearcher::new(m.read(1));
        assert_eq!(s.start(&mut m).unwrap(), true);
        assert_eq!(s.reader().offset(&mut m), 8696);
        s.reader().read(&mut m, &mut buf).unwrap();
        assert_eq!(s.seek(&mut m, SeekDirection::Left).unwrap(), true);
        assert_eq!(s.reader().offset(&mut m), 4348);
        s.reader().read(&mut m, &mut buf).unwrap();
        assert_eq!(s.seek(&mut m, SeekDirection::Right).unwrap(), false);
        assert_eq!(s.reader().offset(&mut m), 4348);

        // Seek right
        let mut s = FileSearcher::new(m.read(1));
        assert_eq!(s.start(&mut m).unwrap(), true);
        assert_eq!(s.reader().offset(&mut m), 8696);
        s.reader().read(&mut m, &mut buf).unwrap();
        assert_eq!(s.seek(&mut m, SeekDirection::Right).unwrap(), false);
        assert_eq!(s.reader().offset(&mut m), 8696);
    }

    #[test]
    fn test_search_truncate() {
        let mut f = MemFlash::new();
        let mut m = FileManager::new(&mut f);
        m.format();
        m.mount().unwrap();

        const N: usize = PAGE_MAX_PAYLOAD_SIZE + 3;
        let mut w = m.write(1);
        w.write(&mut m, &[0x00; N]).unwrap();
        w.record_end();
        w.write(&mut m, &[0x00; N]).unwrap();
        w.record_end();
        w.write(&mut m, &[0x00; N]).unwrap();
        w.record_end();
        w.write(&mut m, &[0x00; N]).unwrap();
        w.record_end();
        m.commit(&mut w).unwrap();

        let mut buf = [0u8; 1];
        // Seek left
        let mut s = FileSearcher::new(m.read(1));
        assert_eq!(s.start(&mut m).unwrap(), true);
        assert_eq!(s.reader().offset(&mut m), N * 2);
        s.reader().read(&mut m, &mut buf).unwrap();
        assert_eq!(s.seek(&mut m, SeekDirection::Left).unwrap(), true);
        assert_eq!(s.reader().offset(&mut m), N);
        s.reader().read(&mut m, &mut buf).unwrap();
        assert_eq!(s.seek(&mut m, SeekDirection::Left).unwrap(), false);
        assert_eq!(s.reader().offset(&mut m), 0);

        m.truncate(1, N * 2).unwrap();

        // Seek left
        let mut s = FileSearcher::new(m.read(1));
        assert_eq!(s.start(&mut m).unwrap(), true);
        assert_eq!(s.reader().offset(&mut m), N);
        s.reader().read(&mut m, &mut buf).unwrap();
        assert_eq!(s.seek(&mut m, SeekDirection::Left).unwrap(), false);
        assert_eq!(s.reader().offset(&mut m), 0);

        m.truncate(1, N).unwrap();

        // Seek left
        let mut s = FileSearcher::new(m.read(1));
        assert_eq!(s.start(&mut m).unwrap(), false);
        assert_eq!(s.reader().offset(&mut m), 0);
    }

    #[test]
    fn test_search_long() {
        let mut f = MemFlash::new();
        let mut m = FileManager::new(&mut f);
        m.format();
        m.mount().unwrap();

        let count = 20000 / 4;

        let mut w = m.write(1);
        for i in 1..=count {
            w.write(&mut m, &(i as u32).to_le_bytes()).unwrap();
            // make records not line up with page boundaries.
            w.write(&mut m, &[0x00]).unwrap();
            w.record_end();
        }
        m.commit(&mut w).unwrap();

        for want in 0..count + 1 {
            debug!("searching for {}", want);

            let mut s = FileSearcher::new(m.read(1));
            assert_eq!(s.start(&mut m).unwrap(), true);

            loop {
                let mut record = [0; 4];
                s.reader().read(&mut m, &mut record).unwrap();
                let record = u32::from_le_bytes(record);

                let dir = if record >= want {
                    SeekDirection::Left
                } else {
                    SeekDirection::Right
                };
                let ok = s.seek(&mut m, dir).unwrap();
                if !ok {
                    break;
                }
            }

            let mut record = [0; 4];
            s.reader().read(&mut m, &mut record).unwrap();
            let record = u32::from_le_bytes(record);

            if want != 0 {
                assert!(want >= record);
                assert!(want - record <= PAGE_MAX_PAYLOAD_SIZE as u32 / 4);
            }
        }
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
                    m.truncate(file_id, s).unwrap();
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

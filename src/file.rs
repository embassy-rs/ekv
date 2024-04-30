use core::fmt;
use core::mem::size_of;

use crate::alloc::Allocator;
use crate::config::*;
use crate::errors::*;
use crate::flash::Flash;
use crate::page;
pub use crate::page::ReadError;
use crate::page::{ChunkHeader, DehydratedPageReader, Header, PageHeader, PageReader, PageWriter};
use crate::types::{OptionPageID, PageID};


pub(crate) const CHUNKS_PER_PAGE: usize = (PAGE_SIZE - PageHeader::SIZE - size_of::<DataHeader>()).div_ceil(MAX_CHUNK_SIZE + ChunkHeader::SIZE);
pub const PAGE_MAX_PAYLOAD_SIZE: usize =
    PAGE_SIZE - PageHeader::SIZE - (CHUNKS_PER_PAGE * ChunkHeader::SIZE) - size_of::<DataHeader>();


pub type FileID = u8;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum SeekDirection {
    Left,
    Right,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[repr(C)]
pub struct MetaHeader {
    page_count: u32,
    seq: Seq,
}

unsafe impl page::Header for MetaHeader {
    const MAGIC: u32 = 0x1d81bcde;
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
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
    const MAGIC: u32 = 0x7fcbf35d;
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

impl FileState {
    const EMPTY: Self = Self {
        dirty: false,
        last_page: None,
        first_seq: Seq::ZERO,
        last_seq: Seq::ZERO,
        flags: 0,
    };
}

pub struct FileManager<F: Flash> {
    flash: F,
    files: [FileState; FILE_COUNT],
    meta_page_id: PageID,
    meta_seq: Seq,
    dirty: bool,
    alloc: Allocator,
    random: u32,
}

impl<F: Flash> FileManager<F> {
    pub fn new(flash: F, random_seed: u32) -> Self {
        assert!(FILE_COUNT * FileMeta::SIZE <= page::MAX_CHUNK_SIZE);
        Self {
            flash,
            random: random_seed,
            meta_page_id: PageID::zero(),
            meta_seq: Seq::ZERO,
            files: [FileState::EMPTY; FILE_COUNT],
            dirty: true,
            alloc: Allocator::new(),
        }
    }

    fn random(&mut self) -> u32 {
        const SOME_PRIME: u32 = 1750509587;
        self.random = self.random.wrapping_mul(SOME_PRIME);
        self.random
    }

    fn page_count(&self) -> usize {
        self.alloc.page_count()
    }

    #[allow(unused)]
    pub fn used_pages(&self) -> usize {
        self.alloc.used_pages()
    }

    pub fn free_pages(&self) -> usize {
        self.alloc.free_pages()
    }

    pub fn flash(&self) -> &F {
        &self.flash
    }

    pub fn flash_mut(&mut self) -> &mut F {
        &mut self.flash
    }

    pub fn is_empty(&self, file_id: FileID) -> bool {
        self.files[file_id as usize].last_page.is_none()
    }

    pub fn read<'a>(&mut self, r: &'a mut PageReader, file_id: FileID) -> FileReader<'a> {
        assert!(!self.dirty);
        FileReader::new(self, r, file_id)
    }

    pub async fn write(&mut self, r: &mut PageReader, file_id: FileID) -> Result<FileWriter, Error<F::Error>> {
        assert!(!self.dirty);
        FileWriter::new(self, r, file_id).await
    }

    pub async fn read_rehydrated<'a>(
        &mut self,
        r: &'a mut PageReader,
        dehydrated: &DehydratedFileReader,
    ) -> Result<FileReader<'a>, Error<F::Error>> {
        assert!(!self.dirty);

        Ok(FileReader {
            file_id: dehydrated.file_id,
            state: match &dehydrated.state {
                DehydratedReaderState::Created => ReaderState::Created,
                DehydratedReaderState::Finished => ReaderState::Finished,
                DehydratedReaderState::Reading(s, rs) => {
                    r.rehydrate_from(&mut self.flash, rs).await?;
                    ReaderState::Reading(s.clone())
                }
            },
            r,
        })
    }

    pub fn file_flags(&self, file_id: FileID) -> u8 {
        self.files[file_id as usize].flags
    }

    pub fn files_with_flag(&self, flag: u8) -> impl Iterator<Item = FileID> + '_ {
        (0..FILE_COUNT as FileID).filter(move |&i| self.file_flags(i) & flag != 0)
    }

    pub async fn format(&mut self) -> Result<(), FormatError<F::Error>> {
        self.dirty = true;

        let page_count = self.flash.page_count();

        let random_seed = self.random();
        self.alloc.reset(page_count, random_seed);
        self.files.fill(FileState::EMPTY);
        self.meta_page_id = self.alloc.allocate();
        self.meta_seq = Seq(1);

        // Erase all meta pages.
        for page_id in 0..self.page_count() {
            let page_id = PageID::from_raw(page_id as _).unwrap();
            if self.read_header::<MetaHeader>(page_id).await.is_ok() {
                self.flash.erase(page_id).await.map_err(FormatError::Flash)?;
            }
        }

        // Write initial meta page.
        let mut w = self.write_page(self.meta_page_id).await;
        let h = MetaHeader {
            page_count: self.page_count() as u32,
            seq: self.meta_seq,
        };
        w.write_header(&mut self.flash, h).await.map_err(FormatError::Flash)?;

        self.dirty = false;
        Ok(())
    }

    pub async fn mount(&mut self, r: &mut PageReader) -> Result<(), Error<F::Error>> {
        self.dirty = true;
        self.files.fill(FileState::EMPTY);

        let mut meta_page_id = None;
        let mut meta_seq = Seq::ZERO;
        let mut meta_page_count = 0;
        for page_id in 0..self.flash.page_count() {
            let page_id = PageID::from_raw(page_id as _).unwrap();
            if let Ok(h) = self.read_header::<MetaHeader>(page_id).await {
                if h.seq > meta_seq {
                    meta_page_id = Some(page_id);
                    meta_seq = h.seq;
                    meta_page_count = h.page_count;
                }
            }
        }

        let Some(meta_page_id) = meta_page_id else {
            debug!("Meta page not found");
            corrupted!()
        };
        if meta_page_count == 0 {
            debug!("mount: flash page count zero",);
            corrupted!()
        }
        if meta_page_count as usize > self.flash.page_count() {
            debug!(
                "mount: flash page count {} less than meta page {}. flash image truncated?",
                self.flash.page_count(),
                meta_page_count
            );
            corrupted!()
        };
        if meta_page_id.index() >= meta_page_count as usize {
            debug!(
                "mount: meta page id {} out of bounds for page count {}",
                meta_page_id.index(),
                meta_page_count
            );
            corrupted!()
        };

        self.meta_page_id = meta_page_id;
        self.meta_seq = meta_seq;

        let random_seed = self.random();
        self.alloc.reset(meta_page_count as _, random_seed);
        self.alloc.mark_used(meta_page_id)?;

        r.open::<_, MetaHeader>(&mut self.flash, meta_page_id)
            .await
            .inspect_err(|_| {
                debug!("failed read meta_page_id={:?}", meta_page_id);
            })?;

        let mut files = [FileMeta {
            file_id: 0,
            flags: 0,
            last_page_id: OptionPageID::none(),
            first_seq: Seq::ZERO,
        }; FILE_COUNT];
        loop {
            let mut meta = [0; FileMeta::SIZE];
            let n = r.read(&mut self.flash, &mut meta).await?;
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
                if page_id.index() >= self.page_count() {
                    debug!("meta last_page_id out of range: {}", meta.file_id);
                    corrupted!();
                }
            } else if meta.first_seq.0 != 0 {
                debug!("meta last_page_id invalid, but first seq nonzero: {}", meta.file_id);
                corrupted!();
            }

            files[meta.file_id as usize] = meta
        }

        for file_id in 0..FILE_COUNT as FileID {
            let meta = files[file_id as usize];

            let Some(last_page_id) = meta.last_page_id.into_option() else {
                continue;
            };

            let h = r
                .open::<_, DataHeader>(&mut self.flash, last_page_id)
                .await
                .inspect_err(|_| {
                    debug!("read_page failed: last_page_id={:?} file_id={}", last_page_id, file_id);
                })?;

            let page_len = r.skip(&mut self.flash, PAGE_SIZE).await?;
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
                if self.alloc.mark_used(pp.page_id).is_err() {
                    info!("page used by multiple files at the same time. page_id={:?}", pp.page_id);
                    corrupted!();
                }
                p = pp.prev(self, meta.first_seq).await?;
            }
        }

        self.dirty = false;
        Ok(())
    }

    pub async fn remount_if_dirty(&mut self, r: &mut PageReader) -> Result<(), Error<F::Error>> {
        if self.dirty {
            self.mount(r).await
        } else {
            Ok(())
        }
    }

    pub fn transaction(&mut self) -> Transaction<'_, F> {
        assert!(!self.dirty);
        Transaction { m: self }
    }

    // convenience method
    pub async fn commit(&mut self, w: &mut FileWriter) -> Result<(), Error<F::Error>> {
        let mut tx = self.transaction();
        w.commit(&mut tx).await?;
        tx.commit().await?;
        Ok(())
    }

    // convenience method
    #[allow(unused)]
    pub async fn truncate(&mut self, file_id: FileID, bytes: usize) -> Result<(), Error<F::Error>> {
        let mut tx = self.transaction();
        tx.truncate(file_id, bytes).await?;
        tx.commit().await?;
        Ok(())
    }

    async fn get_file_page(&mut self, file_id: FileID, seq: Seq) -> Result<Option<PagePointer>, Error<F::Error>> {
        let f = &self.files[file_id as usize];
        let Some(last) = f.last_page else { return Ok(None) };
        if seq < f.first_seq || seq >= f.last_seq {
            Ok(None)
        } else {
            Ok(Some(last.prev_seq(self, seq).await?))
        }
    }

    async fn free_between(
        &mut self,
        mut from: Option<PagePointer>,
        to: Option<PagePointer>,
        seq_limit: Seq,
    ) -> Result<(), Error<F::Error>> {
        while let Some(pp) = from {
            if let Some(to) = to {
                if pp.page_id == to.page_id {
                    break;
                }
            }
            self.free_page(pp.page_id)?;
            from = pp.prev(self, seq_limit).await?;
        }
        Ok(())
    }

    async fn read_header<H: Header>(&mut self, page_id: PageID) -> Result<H, Error<F::Error>> {
        page::read_header(&mut self.flash, page_id).await
    }

    async fn write_page<H: Header>(&mut self, page_id: PageID) -> PageWriter<H> {
        let mut w = PageWriter::new();
        w.open(&mut self.flash, page_id).await;
        w
    }

    fn free_page(&mut self, page_id: PageID) -> Result<(), CorruptedError> {
        trace!("free page {:?}", page_id);
        self.alloc.free(page_id)?;
        #[cfg(feature = "_erase-on-free")]
        self.flash.erase(page_id);
        Ok(())
    }

    #[cfg(feature = "std")]
    #[allow(unused)]
    pub async fn dump(&mut self, r: &mut PageReader) {
        info!("============= BEGIN DUMP");

        self.dump_pages(r).await;

        info!("File dump:");
        for file_id in 0..FILE_COUNT {
            if let Err(e) = self.dump_file(r, file_id as _).await {
                info!("failed to dump file: {:?}", e);
            }
        }
    }

    #[cfg(feature = "std")]
    #[allow(unused)]
    pub async fn dump_pages(&mut self, r: &mut PageReader) {
        info!("Page dump:");
        for page_id in 0..self.flash.page_count() {
            self.dump_page(r, PageID::from_raw(page_id as _).unwrap()).await;
        }
    }

    #[cfg(feature = "std")]
    #[allow(unused)]
    pub fn dump_file_header(&mut self, file_id: FileID) {
        let f = self.files[file_id as usize];
        info!(
            "==== FILE {}:  seq: {:?}..{:?} len {:?} last_page {:?} flags {:02x}",
            file_id,
            f.first_seq,
            f.last_seq,
            f.last_seq.sub(f.first_seq),
            f.last_page.map(|p| p.page_id),
            f.flags
        );
    }

    #[cfg(feature = "std")]
    #[allow(unused)]
    pub async fn dump_file(&mut self, r: &mut PageReader, file_id: FileID) -> Result<(), Error<F::Error>> {
        self.dump_file_header(file_id);
        let f = self.files[file_id as usize];
        let mut pages = Vec::new();
        let mut pp = f.last_page;
        while let Some(p) = pp {
            pages.push(p);
            pp = p.prev(self, f.first_seq).await?;
        }

        for p in pages.iter().rev() {
            self.dump_page(r, p.page_id).await;
        }

        Ok(())
    }

    #[cfg(feature = "std")]
    #[allow(unused)]
    pub async fn dump_page(&mut self, r: &mut PageReader, page_id: PageID) {
        if let Ok(h) = r.open::<_, MetaHeader>(&mut self.flash, page_id).await {
            info!(
                "  page {:?}: META seq {:?} page_count {:?}",
                page_id, h.seq, h.page_count,
            );
        } else if let Ok(h) = r.open::<_, DataHeader>(&mut self.flash, page_id).await {
            // Read all chunks
            let mut chunks = Vec::new();
            let mut buf = [0; PAGE_SIZE];
            let mut last_corrupted = false;
            let mut total_len = 0;
            loop {
                let Ok(n) = r.read(&mut self.flash, &mut buf).await else {
                    last_corrupted = true;
                    break;
                };
                if n == 0 {
                    break;
                }
                chunks.push(buf[..n].to_vec());
                total_len += n;
            }

            let rb = if h.record_boundary == u16::MAX {
                "None".to_string()
            } else {
                format!(
                    "{} (seq {})",
                    h.record_boundary,
                    match h.seq.add(h.record_boundary as usize) {
                        Ok(seq) => format!("{:?}", seq),
                        Err(_) => "<overflow>".to_string(),
                    }
                )
            };

            info!(
                "  page {:?}: seq {}..{} len {} record_boundary {} skiplist {:?}",
                page_id,
                h.seq,
                match h.seq.add(total_len) {
                    Ok(seq) => format!("{:?}", seq),
                    Err(_) => "<overflow>".to_string(),
                },
                total_len,
                rb,
                h.skiplist
            );

            let mut s = h.seq;
            for (i, chunk) in chunks.iter().enumerate() {
                info!("   chunk {}: len {}", i, chunk.len());
                for c in chunk.chunks(32) {
                    info!("     {:04}: {:02x?}", s.0, c);
                    match s.add(c.len()) {
                        Ok(s2) => s = s2,
                        Err(_) => info!("    (seq overflow)"),
                    }
                }
            }
            if last_corrupted {
                info!("   last chunk corrupted");
            }
        } else {
            info!("  page {:?}: corrupted", page_id);
        }
    }
}

pub struct Transaction<'a, F: Flash> {
    m: &'a mut FileManager<F>,
}

impl<'a, F: Flash> Transaction<'a, F> {
    pub async fn set_flags(&mut self, file_id: FileID, flags: u8) -> Result<(), Error<F::Error>> {
        self.m.dirty = true;

        let f = &mut self.m.files[file_id as usize];
        // flags only stick to nonempty files.
        if f.last_page.is_some() && f.flags != flags {
            f.flags = flags;
            f.dirty = true;
        }
        Ok(())
    }

    pub async fn rename(&mut self, from: FileID, to: FileID) -> Result<(), Error<F::Error>> {
        self.m.dirty = true;

        self.m.files.swap(from as usize, to as usize);
        self.m.files[from as usize].dirty = true;
        self.m.files[to as usize].dirty = true;
        Ok(())
    }

    pub async fn truncate(&mut self, file_id: FileID, bytes: usize) -> Result<(), Error<F::Error>> {
        if bytes == 0 {
            return Ok(());
        }

        self.m.dirty = true;

        let f = &mut self.m.files[file_id as usize];
        let old_f = *f;

        let len = f.last_seq.sub(f.first_seq);
        let seq = f.first_seq.add(len.min(bytes))?;

        let old_seq = f.first_seq;
        let p = if seq == f.last_seq {
            f.last_page
        } else {
            self.m
                .get_file_page(file_id, seq)
                .await?
                .unwrap()
                .prev(self.m, old_seq)
                .await?
        };
        self.m.free_between(p, None, old_seq).await?;

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

    async fn write_file_meta(
        &mut self,
        w: &mut PageWriter<MetaHeader>,
        file_id: FileID,
    ) -> Result<(), WriteError<F::Error>> {
        let f = &self.m.files[file_id as usize];
        let meta = FileMeta {
            file_id,
            flags: f.flags,
            first_seq: f.first_seq,
            last_page_id: f.last_page.as_ref().map(|pp| pp.page_id).into(),
        };
        let n = w.write(&mut self.m.flash, &meta.to_bytes()).await?;
        if n != FileMeta::SIZE {
            return Err(WriteError::Full);
        }

        Ok(())
    }

    pub async fn commit(mut self) -> Result<(), Error<F::Error>> {
        self.m.dirty = true;

        // Try appending to the existing meta page.
        let res: Result<(), WriteError<F::Error>> = try {
            let mut mw = PageWriter::new();
            mw.open_append(&mut self.m.flash, self.m.meta_page_id).await?;
            for file_id in 0..FILE_COUNT {
                if self.m.files[file_id].dirty {
                    self.write_file_meta(&mut mw, file_id as FileID).await?;
                }
            }
            mw.commit(&mut self.m.flash).await?;
        };

        match res {
            Ok(()) => {
                self.m.dirty = false;
                Ok(())
            }
            Err(WriteError::Flash(e)) => Err(Error::Flash(e)),
            Err(WriteError::Corrupted) => corrupted!(),
            Err(WriteError::Full) => {
                // Existing meta page was full. Write a new one.

                let page_id = self.m.alloc.allocate();
                trace!("meta: allocated page {:?}", page_id);
                let mut w = self.m.write_page(page_id).await;
                for file_id in 0..FILE_COUNT as FileID {
                    // Since we're writing a new page from scratch, no need to
                    // write metas for empty files.
                    if self.m.files[file_id as usize].last_page.is_some() {
                        self.write_file_meta(&mut w, file_id).await.unwrap();
                    }
                }

                self.m.meta_seq = self.m.meta_seq.add(1)?; // TODO handle wraparound
                let h = MetaHeader {
                    page_count: self.m.page_count() as _,
                    seq: self.m.meta_seq,
                };
                w.write_header(&mut self.m.flash, h).await.map_err(Error::Flash)?;
                w.commit(&mut self.m.flash).await?;

                // free the old one.
                self.m.free_page(self.m.meta_page_id)?;
                self.m.meta_page_id = page_id;

                self.m.dirty = false;
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
    async fn prev<F: Flash>(
        self,
        m: &mut FileManager<F>,
        seq_limit: Seq,
    ) -> Result<Option<PagePointer>, Error<F::Error>> {
        if self.header.seq <= seq_limit {
            return Ok(None);
        }

        let Some(p2) = self.header.skiplist[0].into_option() else {
            return Ok(None);
        };

        if p2.index() >= m.page_count() {
            debug!("prev page out of range {:?}", p2);
            corrupted!();
        }

        let h2 = check_corrupted!(m.read_header::<DataHeader>(p2).await);

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

    async fn prev_seq<F: Flash>(mut self, m: &mut FileManager<F>, seq: Seq) -> Result<PagePointer, Error<F::Error>> {
        while self.header.seq > seq {
            let i = skiplist_index(seq, self.header.seq);
            let Some(p2) = self.header.skiplist[i].into_option() else {
                debug!("no prev page??");
                corrupted!();
            };
            if p2.index() >= m.page_count() {
                debug!("prev page out of range {:?}", p2);
                corrupted!();
            }

            let h2 = check_corrupted!(m.read_header::<DataHeader>(p2).await);

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

pub struct FileReader<'a> {
    file_id: FileID,
    r: &'a mut PageReader,
    state: ReaderState,
}

enum ReaderState {
    Created,
    Reading(ReaderStateReading),
    Finished,
}

#[derive(Clone)]
struct ReaderStateReading {
    seq: Seq,
}

#[derive(Clone)]
pub struct DehydratedFileReader {
    file_id: FileID,
    state: DehydratedReaderState,
}

#[derive(Clone)]
enum DehydratedReaderState {
    Created,
    Reading(ReaderStateReading, DehydratedPageReader),
    Finished,
}

impl<'a> FileReader<'a> {
    fn new<F: Flash>(_m: &mut FileManager<F>, r: &'a mut PageReader, file_id: FileID) -> Self {
        Self {
            file_id,
            r,
            state: ReaderState::Created,
        }
    }

    pub fn dehydrate(&self) -> DehydratedFileReader {
        DehydratedFileReader {
            file_id: self.file_id,
            state: match &self.state {
                ReaderState::Created => DehydratedReaderState::Created,
                ReaderState::Finished => DehydratedReaderState::Finished,
                ReaderState::Reading(s) => DehydratedReaderState::Reading(s.clone(), self.r.dehydrate()),
            },
        }
    }

    pub fn curr_seq<F: Flash>(&mut self, m: &FileManager<F>) -> Seq {
        match &self.state {
            ReaderState::Created => m.files[self.file_id as usize].first_seq,
            ReaderState::Reading(s) => s.seq,
            ReaderState::Finished => m.files[self.file_id as usize].last_seq,
        }
    }

    fn page_id(&self) -> Option<PageID> {
        match &self.state {
            ReaderState::Reading(_s) => Some(self.r.page_id()),
            _ => None,
        }
    }
    async fn next_page<F: Flash>(&mut self, m: &mut FileManager<F>) -> Result<(), Error<F::Error>> {
        let seq = self.curr_seq(m);

        let prev_page_id = self.page_id();

        self.seek_seq(m, seq).await?;

        let curr_page_id = self.page_id();
        if prev_page_id == curr_page_id && curr_page_id.is_some() {
            // prevent infinite loopwhen corrupted zero-len pages.
            corrupted!()
        }

        Ok(())
    }

    async fn seek_seq<F: Flash>(&mut self, m: &mut FileManager<F>, seq: Seq) -> Result<(), Error<F::Error>> {
        self.state = match m.get_file_page(self.file_id, seq).await? {
            Some(pp) => {
                let h = self
                    .r
                    .open::<_, DataHeader>(&mut m.flash, pp.page_id)
                    .await
                    .inspect_err(|_| {
                        debug!("failed read next page={:?}", pp.page_id);
                    })?;
                let n = seq.sub(h.seq);
                let got_n = self.r.skip(&mut m.flash, n).await?;
                let eof = self.r.is_at_eof(&mut m.flash).await?;
                if n != got_n || eof {
                    debug!(
                        "found seq hole in file. page={:?} h.seq={:?} seq={:?} n={} got_n={} eof={}",
                        pp.page_id, h.seq, seq, n, got_n, eof
                    );
                    corrupted!();
                }
                ReaderState::Reading(ReaderStateReading { seq })
            }
            None => ReaderState::Finished,
        };
        Ok(())
    }

    /// Read an exact amount of bytes.
    ///
    /// If we're at file end, return Eof.
    /// If there's some data left at the file but not enough to fill `data`, return Corrupted.
    pub async fn read<F: Flash>(
        &mut self,
        m: &mut FileManager<F>,
        mut data: &mut [u8],
    ) -> Result<(), ReadError<F::Error>> {
        let mut read_some = false;

        while !data.is_empty() {
            match &mut self.state {
                ReaderState::Finished => {
                    if read_some {
                        corrupted!() // Unexpected EOF!
                    } else {
                        return Err(ReadError::Eof);
                    }
                }
                ReaderState::Created => {
                    self.next_page(m).await?;
                    continue;
                }
                ReaderState::Reading(s) => {
                    let n = self.r.read(&mut m.flash, data).await?;
                    if n == 0 {
                        self.next_page(m).await?;
                    } else {
                        data = &mut data[n..];
                        s.seq = s.seq.add(n)?;
                        read_some = true;
                    }
                }
            }
        }
        Ok(())
    }

    pub async fn skip<F: Flash>(&mut self, m: &mut FileManager<F>, mut len: usize) -> Result<(), ReadError<F::Error>> {
        // advance within the current page.
        if let ReaderState::Reading(s) = &mut self.state {
            // Only worth trying if the skip might not exhaust the current page
            if len < PAGE_MAX_PAYLOAD_SIZE {
                let n = self.r.skip(&mut m.flash, len).await?;
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

            self.seek_seq(m, new_seq).await?;
        }

        Ok(())
    }

    pub fn offset<F: Flash>(&mut self, m: &FileManager<F>) -> usize {
        let first_seq = m.files[self.file_id as usize].first_seq;
        self.curr_seq(m).sub(first_seq)
    }

    #[allow(unused)]
    pub async fn seek<F: Flash>(&mut self, m: &mut FileManager<F>, offs: usize) -> Result<(), ReadError<F::Error>> {
        let first_seq = m.files[self.file_id as usize].first_seq;
        let new_seq = first_seq.add(offs).map_err(|_| ReadError::Eof)?;
        if new_seq > m.files[self.file_id as usize].last_seq {
            return Err(ReadError::Eof);
        }

        self.seek_seq(m, new_seq).await?;
        Ok(())
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub enum SearchSeekError<E> {
    Flash(E),
    TooMuchLeft,
    Corrupted,
}

impl<E> From<Error<E>> for SearchSeekError<E> {
    fn from(e: Error<E>) -> Self {
        match e {
            Error::Flash(e) => Self::Flash(e),
            Error::Corrupted => Self::Corrupted,
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub enum WriteError<E> {
    Flash(E),
    Full,
    Corrupted,
}

impl<E> From<Error<E>> for WriteError<E> {
    fn from(e: Error<E>) -> Self {
        match e {
            Error::Flash(e) => Self::Flash(e),
            Error::Corrupted => Self::Corrupted,
        }
    }
}

pub struct FileSearcher<'a> {
    r: FileReader<'a>,

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

impl<'a> FileSearcher<'a> {
    pub fn new(r: FileReader<'a>) -> Self {
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

    pub fn reader(&mut self) -> &mut FileReader<'a> {
        &mut self.r
    }

    pub async fn start<F: Flash>(&mut self, m: &mut FileManager<F>) -> Result<bool, Error<F::Error>> {
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
                self.really_seek(m).await
            }
            None => {
                trace!("search start file={:?}: empty file", self.r.file_id);
                Ok(false)
            }
        }
    }

    async fn really_seek<F: Flash>(&mut self, m: &mut FileManager<F>) -> Result<bool, Error<F::Error>> {
        let left = self.left.add(1)?;
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
                        match self.seek_to_page(m, page_id, seq).await {
                            Ok(()) => return Ok(true),
                            Err(SearchSeekError::Flash(e)) => return Err(Error::Flash(e)),
                            Err(SearchSeekError::Corrupted) => corrupted!(),
                            Err(SearchSeekError::TooMuchLeft) => {
                                let new_left = seq.add(1)?;
                                assert!(new_left >= self.left);
                                self.left = new_left;
                            }
                        }
                    }
                }
            }

            if i == 0 {
                let seq = self.result;
                self.reader().seek_seq(m, seq).await?;
                return Ok(false);
            }

            // Seek failed. Try again less hard.
            i -= 1;
        }
    }

    async fn seek_to_page<F: Flash>(
        &mut self,
        m: &mut FileManager<F>,
        mut page_id: PageID,
        target_seq: Seq,
    ) -> Result<(), SearchSeekError<F::Error>> {
        trace!("search: seek_to_page page_id={:?} target_seq={:?}", page_id, target_seq,);

        let mut right_limit = self.right;

        loop {
            if page_id.index() >= m.page_count() {
                corrupted!()
            }
            let h = m.read_header::<DataHeader>(page_id).await.inspect_err(|_| {
                debug!("failed read next page={:?}", page_id);
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
                break;
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
        }

        // Open the page
        let h = self.r.r.open::<_, DataHeader>(&mut m.flash, page_id).await?;

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

        let n = self.r.r.skip(&mut m.flash, b).await?;
        if n != b {
            corrupted!()
        }
        self.curr_mid = boundary_seq;
        self.curr_high = target_seq.max(boundary_seq);

        self.r.state = ReaderState::Reading(ReaderStateReading { seq: self.curr_mid });
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

    pub async fn seek<F: Flash>(
        &mut self,
        m: &mut FileManager<F>,
        dir: SeekDirection,
    ) -> Result<bool, Error<F::Error>> {
        match dir {
            SeekDirection::Left => {
                trace!("search seek left");
                self.right = self.curr_low;
                self.right_skiplist = self.curr_skiplist;
            }
            SeekDirection::Right => {
                trace!("search seek right");
                self.left = self.curr_high.add(1)?;
                self.result = self.curr_mid;
            }
        }

        self.really_seek(m).await
    }
}

pub struct FileWriter {
    file_id: FileID,
    last_page: Option<PagePointer>,
    seq: Seq,
    writer: Option<PageWriter<DataHeader>>,

    // Previous last page of the file, that was copied to a new page because
    // it was not full. Must be freed on commit.
    rewritten_last_page_id: Option<PageID>,

    at_record_boundary: bool,
    record_boundary: Option<u16>,
}

impl FileWriter {
    async fn new<F: Flash>(
        m: &mut FileManager<F>,
        r: &mut PageReader,
        file_id: FileID,
    ) -> Result<Self, Error<F::Error>> {
        let f = m.files[file_id as usize];

        let mut this = Self {
            file_id,
            last_page: f.last_page,
            seq: f.last_seq,
            rewritten_last_page_id: None,
            at_record_boundary: true,
            record_boundary: Some(0),
            writer: None,
        };

        // Ensure last page is full.
        // This is needed to ensure progressive compaction does not actually un-compact
        // the data, due to leaving pages not full in the middle of the file.
        if let Some(pp) = f.last_page {
            r.open::<_, DataHeader>(&mut m.flash, pp.page_id).await?;

            // Measure total page len.
            let mut page_len = 0;
            loop {
                let n = r.skip(&mut m.flash, PAGE_MAX_PAYLOAD_SIZE).await?;
                if n == 0 {
                    break;
                }
                page_len += n;
            }

            if page_len != PAGE_MAX_PAYLOAD_SIZE {
                // Page is not full.
                // Open a new page, copy all the data over, and make that the last file page.
                // TODO: if possible, use PageManager::write_append to avoid the copy.

                // seek again to start.
                r.open::<_, DataHeader>(&mut m.flash, pp.page_id).await?;

                // open new page
                let page_id = m.alloc.try_allocate().ok_or(CorruptedError)?;
                trace!("writer: last page is not full. Copying it to new page {:?}", page_id);
                let mut w = m.write_page(page_id).await;

                let mut buf = [0; 128];
                loop {
                    let n = r.read(&mut m.flash, &mut buf).await?;
                    if n == 0 {
                        break;
                    }
                    let mut data = &buf[..n];
                    while !data.is_empty() {
                        let n = w.write(&mut m.flash, data).await?;
                        data = &data[n..];

                        // the new page can't get full, because we're not writing more
                        // than 1 page worth of data to it.
                        assert!(n != 0);
                    }
                }

                this.writer = Some(w);
                this.seq = pp.header.seq;
                this.at_record_boundary = true;
                this.record_boundary = (pp.header.record_boundary != u16::MAX).then_some(pp.header.record_boundary);
                this.last_page = pp.prev(m, f.first_seq).await?;
                this.rewritten_last_page_id = Some(pp.page_id);
            }
        }

        Ok(this)
    }

    #[allow(unused)]
    fn curr_seq<F: Flash>(&mut self, _m: &mut FileManager<F>) -> Seq {
        let n = self.writer.as_ref().map(|w| w.len()).unwrap_or(0);
        self.seq.add(n).unwrap()
    }

    #[allow(unused)]
    pub fn offset<F: Flash>(&mut self, m: &mut FileManager<F>) -> usize {
        let first_seq = m.files[self.file_id as usize].first_seq;
        self.curr_seq(m).sub(first_seq)
    }

    async fn flush_header<F: Flash>(
        &mut self,
        m: &mut FileManager<F>,
        mut w: PageWriter<DataHeader>,
    ) -> Result<(), Error<F::Error>> {
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
        w.write_header(&mut m.flash, header).await.map_err(Error::Flash)?;
        w.commit(&mut m.flash).await?;

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

    async fn next_page<F: Flash>(&mut self, m: &mut FileManager<F>) -> Result<(), Error<F::Error>> {
        if let Some(w) = self.writer.take() {
            self.flush_header(m, w).await?;
        }

        let page_id = m.alloc.allocate();
        trace!("writer: allocated page {:?}", page_id);
        self.writer = Some(m.write_page(page_id).await);
        Ok(())
    }

    pub async fn write<F: Flash>(&mut self, m: &mut FileManager<F>, mut data: &[u8]) -> Result<(), Error<F::Error>> {
        while !data.is_empty() {
            match &mut self.writer {
                None => {
                    self.next_page(m).await?;
                    continue;
                }
                Some(w) => {
                    let n = w.write(&mut m.flash, data).await?;
                    data = &data[n..];
                    if n == 0 {
                        self.next_page(m).await?;
                    }

                    // Wrote some data, we're no longer at a boundary.
                    self.at_record_boundary = false;
                }
            }
        }
        Ok(())
    }

    pub async fn commit<F: Flash>(&mut self, tx: &mut Transaction<'_, F>) -> Result<(), Error<F::Error>> {
        if let Some(w) = self.writer.take() {
            self.flush_header(tx.m, w).await?;

            tx.m.dirty = true;
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

            if let Some(rewritten_page_id) = self.rewritten_last_page_id {
                trace!("freeing rewritten page {:?}", rewritten_page_id);
                tx.m.alloc.free(rewritten_page_id)?;
            }
        }
        Ok(())
    }

    pub async fn discard<F: Flash>(&mut self, m: &mut FileManager<F>) -> Result<(), Error<F::Error>> {
        if let Some(w) = &self.writer {
            // Free the page we're writing now (not yet committed)
            let page_id = w.page_id();
            m.free_page(page_id)?;

            // Free previous pages, if any
            let f = &m.files[self.file_id as usize];
            m.free_between(self.last_page, f.last_page, Seq::ZERO).await?;
        };
        Ok(())
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

    fn add(self, offs: usize) -> Result<Self, CorruptedError> {
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

    use super::*;
    use crate::flash::MemFlash;
    use crate::types::RawPageID;

    fn page(p: RawPageID) -> PageID {
        PageID::from_raw(p).unwrap()
    }

    #[test_log::test(tokio::test)]
    async fn test_read_write() {
        let mut f = MemFlash::new();
        let mut m = FileManager::new(&mut f, 0);
        let mut pr = PageReader::new();
        m.format().await.unwrap();
        m.mount(&mut pr).await.unwrap();

        let data = dummy_data(24);

        let mut w = m.write(&mut pr, 0).await.unwrap();
        w.write(&mut m, &data).await.unwrap();
        m.commit(&mut w).await.unwrap();

        let mut r = m.read(&mut pr, 0);
        let mut buf = vec![0; data.len()];
        r.read(&mut m, &mut buf).await.unwrap();
        assert_eq!(data, buf);

        // Remount
        m.mount(&mut pr).await.unwrap();

        let mut r = m.read(&mut pr, 0);
        let mut buf = vec![0; data.len()];
        r.read(&mut m, &mut buf).await.unwrap();
        assert_eq!(data, buf);
    }

    #[test_log::test(tokio::test)]
    async fn test_read_write_long() {
        let mut f = MemFlash::new();
        let mut m = FileManager::new(&mut f, 0);
        let mut pr = PageReader::new();
        m.format().await.unwrap();
        m.mount(&mut pr).await.unwrap();

        let data = dummy_data(23456);

        let mut w = m.write(&mut pr, 0).await.unwrap();
        w.write(&mut m, &data).await.unwrap();
        m.commit(&mut w).await.unwrap();
        w.discard(&mut m).await.unwrap();

        let mut r = m.read(&mut pr, 0);
        let mut buf = vec![0; data.len()];
        r.read(&mut m, &mut buf).await.unwrap();
        assert_eq!(data, buf);

        // Remount
        m.mount(&mut pr).await.unwrap();

        let mut r = m.read(&mut pr, 0);
        let mut buf = vec![0; data.len()];
        r.read(&mut m, &mut buf).await.unwrap();
        assert_eq!(data, buf);
    }

    #[test_log::test(tokio::test)]
    async fn test_empty_eof() {
        let mut f = MemFlash::new();
        let mut m = FileManager::new(&mut f, 0);
        let mut pr = PageReader::new();
        m.format().await.unwrap();
        m.mount(&mut pr).await.unwrap();

        let mut r = m.read(&mut pr, 0);
        let mut buf = vec![0; 1];
        let res = r.read(&mut m, &mut buf).await;
        assert_eq!(res, Err(ReadError::Eof));
    }

    #[test_log::test(tokio::test)]
    async fn test_read_eof() {
        let mut f = MemFlash::new();
        let mut m = FileManager::new(&mut f, 0);
        let mut pr = PageReader::new();
        m.format().await.unwrap();
        m.mount(&mut pr).await.unwrap();

        let data = dummy_data(24);

        let mut w = m.write(&mut pr, 0).await.unwrap();
        w.write(&mut m, &data).await.unwrap();
        m.commit(&mut w).await.unwrap();

        let mut r = m.read(&mut pr, 0);
        let mut buf = vec![0; data.len()];
        r.read(&mut m, &mut buf).await.unwrap();
        assert_eq!(data, buf);
        let res = r.read(&mut m, &mut buf).await;
        assert_eq!(res, Err(ReadError::Eof));
    }

    #[test_log::test(tokio::test)]
    async fn test_read_unexpected_eof() {
        let mut f = MemFlash::new();
        let mut m = FileManager::new(&mut f, 0);
        let mut pr = PageReader::new();
        m.format().await.unwrap();
        m.mount(&mut pr).await.unwrap();

        let data = dummy_data(24);

        let mut w = m.write(&mut pr, 0).await.unwrap();
        w.write(&mut m, &data).await.unwrap();
        m.commit(&mut w).await.unwrap();

        let mut r = m.read(&mut pr, 0);
        let mut buf = vec![0; data.len() + 1];
        let res = r.read(&mut m, &mut buf).await;
        assert_eq!(res, Err(ReadError::Corrupted));
    }

    #[test_log::test(tokio::test)]
    async fn test_append() {
        let mut f = MemFlash::new();
        let mut m = FileManager::new(&mut f, 0);
        let mut pr = PageReader::new();
        m.format().await.unwrap();
        m.mount(&mut pr).await.unwrap();

        let mut w = m.write(&mut pr, 0).await.unwrap();
        w.write(&mut m, &[1, 2, 3, 4, 5]).await.unwrap();
        m.commit(&mut w).await.unwrap();

        let mut w = m.write(&mut pr, 0).await.unwrap();
        w.write(&mut m, &[6, 7, 8, 9]).await.unwrap();
        m.commit(&mut w).await.unwrap();

        let mut r = m.read(&mut pr, 0);
        let mut buf = vec![0; 9];
        r.read(&mut m, &mut buf).await.unwrap();
        assert_eq!(buf, [1, 2, 3, 4, 5, 6, 7, 8, 9]);

        // Remount
        m.mount(&mut pr).await.unwrap();

        let mut r = m.read(&mut pr, 0);
        r.read(&mut m, &mut buf).await.unwrap();
        assert_eq!(buf, [1, 2, 3, 4, 5, 6, 7, 8, 9]);
    }

    #[test_log::test(tokio::test)]
    async fn test_truncate() {
        let mut f = MemFlash::new();
        let mut m = FileManager::new(&mut f, 0);
        let mut pr = PageReader::new();
        m.format().await.unwrap();
        m.mount(&mut pr).await.unwrap();

        let mut w = m.write(&mut pr, 0).await.unwrap();
        w.write(&mut m, &[1, 2, 3, 4, 5]).await.unwrap();
        m.commit(&mut w).await.unwrap();

        m.truncate(0, 2).await.unwrap();

        let mut r = m.read(&mut pr, 0);
        let mut buf = [0; 3];
        r.read(&mut m, &mut buf).await.unwrap();
        assert_eq!(buf, [3, 4, 5]);

        m.truncate(0, 1).await.unwrap();

        let mut r = m.read(&mut pr, 0);
        let mut buf = [0; 2];
        r.read(&mut m, &mut buf).await.unwrap();
        assert_eq!(buf, [4, 5]);

        // Remount
        m.mount(&mut pr).await.unwrap();

        let mut r = m.read(&mut pr, 0);
        let mut buf = [0; 2];
        r.read(&mut m, &mut buf).await.unwrap();
        assert_eq!(buf, [4, 5]);
    }

    #[test_log::test(tokio::test)]
    async fn test_append_truncate() {
        let mut f = MemFlash::new();
        let mut m = FileManager::new(&mut f, 0);
        let mut pr = PageReader::new();
        m.format().await.unwrap();
        m.mount(&mut pr).await.unwrap();

        let mut w = m.write(&mut pr, 0).await.unwrap();
        w.write(&mut m, &[1, 2, 3, 4, 5]).await.unwrap();
        m.commit(&mut w).await.unwrap();

        let mut w = m.write(&mut pr, 0).await.unwrap();
        w.write(&mut m, &[6, 7, 8, 9]).await.unwrap();

        let mut tx = m.transaction();
        w.commit(&mut tx).await.unwrap();
        tx.truncate(0, 2).await.unwrap();
        tx.commit().await.unwrap();

        let mut r = m.read(&mut pr, 0);
        let mut buf = [0; 7];
        r.read(&mut m, &mut buf).await.unwrap();
        assert_eq!(buf, [3, 4, 5, 6, 7, 8, 9]);

        m.truncate(0, 1).await.unwrap();

        let mut r = m.read(&mut pr, 0);
        let mut buf = [0; 6];
        r.read(&mut m, &mut buf).await.unwrap();
        assert_eq!(buf, [4, 5, 6, 7, 8, 9]);

        m.truncate(0, 5).await.unwrap();

        let mut r = m.read(&mut pr, 0);
        let mut buf = [0; 1];
        r.read(&mut m, &mut buf).await.unwrap();
        assert_eq!(buf, [9]);

        // Remount
        m.mount(&mut pr).await.unwrap();

        let mut r = m.read(&mut pr, 0);
        let mut buf = [0; 1];
        r.read(&mut m, &mut buf).await.unwrap();
        assert_eq!(buf, [9]);

        let mut w = m.write(&mut pr, 0).await.unwrap();
        w.write(&mut m, &[10, 11, 12]).await.unwrap();
        m.commit(&mut w).await.unwrap();

        let mut r = m.read(&mut pr, 0);
        let mut buf = [0; 4];
        r.read(&mut m, &mut buf).await.unwrap();
        assert_eq!(buf, [9, 10, 11, 12]);
    }

    #[test_log::test(tokio::test)]
    async fn test_transaction_drop() {
        let mut f = MemFlash::new();
        let mut m = FileManager::new(&mut f, 0);
        let mut pr = PageReader::new();
        m.format().await.unwrap();
        m.mount(&mut pr).await.unwrap();

        let mut w = m.write(&mut pr, 0).await.unwrap();
        w.write(&mut m, &[1, 2, 3, 4, 5]).await.unwrap();

        let mut tx = m.transaction();
        w.commit(&mut tx).await.unwrap();
        // no commit!

        assert!(m.dirty);

        m.remount_if_dirty(&mut pr).await.unwrap();

        let mut r = m.read(&mut pr, 0);
        let mut buf = [0; 1];
        let res = r.read(&mut m, &mut buf).await;
        assert_eq!(res, Err(ReadError::Eof));
    }

    #[test_log::test(tokio::test)]
    async fn test_delete() {
        let mut f = MemFlash::new();
        let mut m = FileManager::new(&mut f, 0);
        let mut pr = PageReader::new();
        m.format().await.unwrap();
        m.mount(&mut pr).await.unwrap();

        let mut w = m.write(&mut pr, 0).await.unwrap();
        w.write(&mut m, &[1, 2, 3, 4, 5]).await.unwrap();
        m.commit(&mut w).await.unwrap();

        assert_eq!(m.alloc.is_used(page(1)), true);

        m.truncate(0, 5).await.unwrap();

        assert_eq!(m.alloc.is_used(page(1)), false);

        // Remount
        m.mount(&mut pr).await.unwrap();

        assert_eq!(m.alloc.is_used(page(1)), false);

        let mut r = m.read(&mut pr, 0);
        let mut buf = [0; 1];
        let res = r.read(&mut m, &mut buf).await;
        assert!(matches!(res, Err(ReadError::Eof)));
    }

    #[test_log::test(tokio::test)]
    async fn test_truncate_alloc() {
        let mut f = MemFlash::new();
        let mut m = FileManager::new(&mut f, 0);
        let mut pr = PageReader::new();
        m.format().await.unwrap();
        m.mount(&mut pr).await.unwrap();

        assert_eq!(m.alloc.is_used(page(1)), false);

        let mut w = m.write(&mut pr, 0).await.unwrap();
        w.write(&mut m, &[1, 2, 3, 4, 5]).await.unwrap();
        m.commit(&mut w).await.unwrap();

        assert_eq!(m.alloc.is_used(page(1)), true);

        m.truncate(0, 5).await.unwrap();

        assert_eq!(m.alloc.is_used(page(1)), false);

        // Remount
        m.mount(&mut pr).await.unwrap();

        assert_eq!(m.alloc.is_used(page(1)), false);

        let mut r = m.read(&mut pr, 0);
        let mut buf = [0; 1];
        let res = r.read(&mut m, &mut buf).await;
        assert!(matches!(res, Err(ReadError::Eof)));
    }

    #[test_log::test(tokio::test)]
    async fn test_truncate_alloc_2() {
        let mut f = MemFlash::new();
        let mut m = FileManager::new(&mut f, 0);
        let mut pr = PageReader::new();
        m.format().await.unwrap();
        m.mount(&mut pr).await.unwrap();

        assert_eq!(m.alloc.is_used(page(1)), false);

        let data = dummy_data(PAGE_MAX_PAYLOAD_SIZE);

        let mut w = m.write(&mut pr, 0).await.unwrap();
        w.write(&mut m, &data).await.unwrap();
        w.write(&mut m, &data).await.unwrap();
        m.commit(&mut w).await.unwrap();

        assert_eq!(m.alloc.is_used(page(1)), true);
        assert_eq!(m.alloc.is_used(page(2)), true);

        m.truncate(0, PAGE_MAX_PAYLOAD_SIZE).await.unwrap();
        assert_eq!(m.alloc.is_used(page(1)), false);
        assert_eq!(m.alloc.is_used(page(2)), true);

        m.truncate(0, PAGE_MAX_PAYLOAD_SIZE).await.unwrap();
        assert_eq!(m.alloc.is_used(page(1)), false);
        assert_eq!(m.alloc.is_used(page(2)), false);

        // Remount
        m.mount(&mut pr).await.unwrap();

        assert_eq!(m.alloc.is_used(page(1)), false);
        assert_eq!(m.alloc.is_used(page(2)), false);

        let mut r = m.read(&mut pr, 0);
        let mut buf = [0; 1];
        let res = r.read(&mut m, &mut buf).await;
        assert!(matches!(res, Err(ReadError::Eof)));
    }

    #[test_log::test(tokio::test)]
    async fn test_append_no_commit() {
        let mut f = MemFlash::new();
        let mut m = FileManager::new(&mut f, 0);
        let mut pr = PageReader::new();
        m.format().await.unwrap();
        m.mount(&mut pr).await.unwrap();

        let mut w = m.write(&mut pr, 0).await.unwrap();
        w.write(&mut m, &[1, 2, 3, 4, 5]).await.unwrap();
        m.commit(&mut w).await.unwrap();

        let mut w = m.write(&mut pr, 0).await.unwrap();
        w.write(&mut m, &[6, 7, 8, 9]).await.unwrap();
        w.discard(&mut m).await.unwrap();

        let mut r = m.read(&mut pr, 0);
        let mut buf = [0; 5];
        r.read(&mut m, &mut buf).await.unwrap();
        assert_eq!(buf, [1, 2, 3, 4, 5]);
        let mut buf = [0; 1];
        let res = r.read(&mut m, &mut buf).await;
        assert!(matches!(res, Err(ReadError::Eof)));

        let mut w = m.write(&mut pr, 0).await.unwrap();
        w.write(&mut m, &[10, 11]).await.unwrap();
        m.commit(&mut w).await.unwrap();

        let mut r = m.read(&mut pr, 0);
        let mut buf = [0; 7];
        r.read(&mut m, &mut buf).await.unwrap();
        assert_eq!(buf, [1, 2, 3, 4, 5, 10, 11]);
    }

    #[test_log::test(tokio::test)]
    async fn test_read_unwritten() {
        let mut f = MemFlash::new();
        let mut m = FileManager::new(&mut f, 0);
        let mut pr = PageReader::new();
        m.format().await.unwrap();
        m.mount(&mut pr).await.unwrap();

        let mut r = m.read(&mut pr, 0);
        let mut buf = vec![0; 1024];
        let res = r.read(&mut m, &mut buf).await;
        assert!(matches!(res, Err(ReadError::Eof)));
    }

    #[test_log::test(tokio::test)]
    async fn test_read_uncommitted() {
        let mut f = MemFlash::new();
        let mut m = FileManager::new(&mut f, 0);
        let mut pr = PageReader::new();
        m.format().await.unwrap();
        m.mount(&mut pr).await.unwrap();

        let data = dummy_data(1234);

        let mut w = m.write(&mut pr, 0).await.unwrap();
        w.write(&mut m, &data).await.unwrap();
        w.discard(&mut m).await.unwrap(); // don't commit

        let mut r = m.read(&mut pr, 0);
        let mut buf = vec![0; 1024];
        let res = r.read(&mut m, &mut buf).await;
        assert!(matches!(res, Err(ReadError::Eof)));
    }

    #[test_log::test(tokio::test)]
    async fn test_alloc_commit() {
        let mut f = MemFlash::new();
        let mut m = FileManager::new(&mut f, 0);
        let mut pr = PageReader::new();
        m.format().await.unwrap();
        m.mount(&mut pr).await.unwrap();

        assert_eq!(m.alloc.is_used(page(1)), false);
        assert_eq!(m.alloc.is_used(page(2)), false);

        let data = dummy_data(PAGE_MAX_PAYLOAD_SIZE);
        let mut w = m.write(&mut pr, 0).await.unwrap();

        w.write(&mut m, &data).await.unwrap();
        assert_eq!(m.alloc.is_used(page(0)), true); // old meta
        assert_eq!(m.alloc.is_used(page(1)), true);
        assert_eq!(m.alloc.is_used(page(2)), false);
        assert_eq!(m.alloc.is_used(page(3)), false);

        w.write(&mut m, &data).await.unwrap();
        assert_eq!(m.alloc.is_used(page(0)), true); // old meta
        assert_eq!(m.alloc.is_used(page(1)), true);
        assert_eq!(m.alloc.is_used(page(2)), true);
        assert_eq!(m.alloc.is_used(page(3)), false);

        m.commit(&mut w).await.unwrap();
        assert_eq!(m.alloc.is_used(page(0)), true); // old meta, appended in-place.
        assert_eq!(m.alloc.is_used(page(1)), true);
        assert_eq!(m.alloc.is_used(page(2)), true);
        assert_eq!(m.alloc.is_used(page(3)), false);

        // Remount
        m.mount(&mut pr).await.unwrap();
        assert_eq!(m.alloc.is_used(page(0)), true); // old meta, appended in-place.
        assert_eq!(m.alloc.is_used(page(1)), true);
        assert_eq!(m.alloc.is_used(page(2)), true);
        assert_eq!(m.alloc.is_used(page(3)), false);
    }

    #[test_log::test(tokio::test)]
    async fn test_alloc_discard_1page() {
        let mut f = MemFlash::new();
        let mut m = FileManager::new(&mut f, 0);
        let mut pr = PageReader::new();
        m.format().await.unwrap();
        m.mount(&mut pr).await.unwrap();

        assert_eq!(m.alloc.is_used(page(0)), true);
        assert_eq!(m.alloc.is_used(page(1)), false);
        assert_eq!(m.alloc.is_used(page(2)), false);

        let data = dummy_data(PAGE_MAX_PAYLOAD_SIZE);
        let mut w = m.write(&mut pr, 0).await.unwrap();

        w.write(&mut m, &data).await.unwrap();
        assert_eq!(m.alloc.is_used(page(0)), true);
        assert_eq!(m.alloc.is_used(page(1)), true);
        assert_eq!(m.alloc.is_used(page(2)), false);

        w.discard(&mut m).await.unwrap();
        assert_eq!(m.alloc.is_used(page(0)), true);
        assert_eq!(m.alloc.is_used(page(1)), false);
        assert_eq!(m.alloc.is_used(page(2)), false);

        // Remount
        m.mount(&mut pr).await.unwrap();
        assert_eq!(m.alloc.is_used(page(0)), true);
        assert_eq!(m.alloc.is_used(page(1)), false);
        assert_eq!(m.alloc.is_used(page(2)), false);
    }

    #[test_log::test(tokio::test)]
    async fn test_alloc_discard_2page() {
        let mut f = MemFlash::new();
        let mut m = FileManager::new(&mut f, 0);
        let mut pr = PageReader::new();
        m.format().await.unwrap();
        m.mount(&mut pr).await.unwrap();

        assert_eq!(m.alloc.is_used(page(0)), true);
        assert_eq!(m.alloc.is_used(page(1)), false);

        let data = dummy_data(PAGE_MAX_PAYLOAD_SIZE);
        let mut w = m.write(&mut pr, 0).await.unwrap();

        w.write(&mut m, &data).await.unwrap();
        assert_eq!(m.alloc.is_used(page(0)), true);
        assert_eq!(m.alloc.is_used(page(1)), true);
        assert_eq!(m.alloc.is_used(page(2)), false);

        w.write(&mut m, &data).await.unwrap();
        assert_eq!(m.alloc.is_used(page(0)), true);
        assert_eq!(m.alloc.is_used(page(1)), true);
        assert_eq!(m.alloc.is_used(page(2)), true);
        assert_eq!(m.alloc.is_used(page(3)), false);

        w.discard(&mut m).await.unwrap();
        assert_eq!(m.alloc.is_used(page(0)), true);
        assert_eq!(m.alloc.is_used(page(1)), false);
        assert_eq!(m.alloc.is_used(page(2)), false);
        assert_eq!(m.alloc.is_used(page(3)), false);

        // Remount
        m.mount(&mut pr).await.unwrap();
        assert_eq!(m.alloc.is_used(page(0)), true);
        assert_eq!(m.alloc.is_used(page(1)), false);
        assert_eq!(m.alloc.is_used(page(2)), false);
        assert_eq!(m.alloc.is_used(page(3)), false);
    }

    #[test_log::test(tokio::test)]
    async fn test_alloc_discard_3page() {
        let mut f = MemFlash::new();
        let mut m = FileManager::new(&mut f, 0);
        let mut pr = PageReader::new();
        m.format().await.unwrap();
        m.mount(&mut pr).await.unwrap();

        assert_eq!(m.alloc.is_used(page(0)), true);
        assert_eq!(m.alloc.is_used(page(1)), false);
        assert_eq!(m.alloc.is_used(page(2)), false);
        assert_eq!(m.alloc.is_used(page(3)), false);

        let data = dummy_data(PAGE_MAX_PAYLOAD_SIZE * 3);
        let mut w = m.write(&mut pr, 0).await.unwrap();
        w.write(&mut m, &data).await.unwrap();
        assert_eq!(m.alloc.is_used(page(0)), true);
        assert_eq!(m.alloc.is_used(page(1)), true);
        assert_eq!(m.alloc.is_used(page(2)), true);
        assert_eq!(m.alloc.is_used(page(3)), true);
        assert_eq!(m.alloc.is_used(page(4)), false);

        w.discard(&mut m).await.unwrap();
        assert_eq!(m.alloc.is_used(page(0)), true);
        assert_eq!(m.alloc.is_used(page(1)), false);
        assert_eq!(m.alloc.is_used(page(2)), false);
        assert_eq!(m.alloc.is_used(page(3)), false);
        assert_eq!(m.alloc.is_used(page(4)), false);

        // Remount
        m.mount(&mut pr).await.unwrap();
        assert_eq!(m.alloc.is_used(page(0)), true);
        assert_eq!(m.alloc.is_used(page(1)), false);
        assert_eq!(m.alloc.is_used(page(2)), false);
        assert_eq!(m.alloc.is_used(page(3)), false);
        assert_eq!(m.alloc.is_used(page(4)), false);
    }

    #[test_log::test(tokio::test)]
    async fn test_append_alloc_discard() {
        let mut f = MemFlash::new();
        let mut m = FileManager::new(&mut f, 0);
        let mut pr = PageReader::new();
        m.format().await.unwrap();
        m.mount(&mut pr).await.unwrap();

        assert_eq!(m.alloc.is_used(page(0)), true);
        assert_eq!(m.alloc.is_used(page(1)), false);

        let data = dummy_data(24);
        let mut w = m.write(&mut pr, 0).await.unwrap();
        w.write(&mut m, &data).await.unwrap();
        m.commit(&mut w).await.unwrap();
        assert_eq!(m.alloc.is_used(page(0)), true); // old meta, appended in-place.
        assert_eq!(m.alloc.is_used(page(1)), true);
        assert_eq!(m.alloc.is_used(page(2)), false);
        assert_eq!(m.alloc.is_used(page(3)), false);

        let mut w = m.write(&mut pr, 0).await.unwrap();
        w.write(&mut m, &data).await.unwrap();
        assert_eq!(m.alloc.is_used(page(0)), true);
        assert_eq!(m.alloc.is_used(page(1)), true);
        assert_eq!(m.alloc.is_used(page(2)), true);
        assert_eq!(m.alloc.is_used(page(3)), false);

        w.discard(&mut m).await.unwrap();
        assert_eq!(m.alloc.is_used(page(0)), true);
        assert_eq!(m.alloc.is_used(page(1)), true);
        assert_eq!(m.alloc.is_used(page(2)), false);
        assert_eq!(m.alloc.is_used(page(3)), false);

        // Remount
        m.mount(&mut pr).await.unwrap();
        assert_eq!(m.alloc.is_used(page(0)), true);
        assert_eq!(m.alloc.is_used(page(1)), true);
        assert_eq!(m.alloc.is_used(page(2)), false);
        assert_eq!(m.alloc.is_used(page(3)), false);
    }

    #[test_log::test(tokio::test)]
    async fn test_write_2_files() {
        let mut f = MemFlash::new();
        let mut m = FileManager::new(&mut f, 0);
        let mut pr = PageReader::new();
        m.format().await.unwrap();
        m.mount(&mut pr).await.unwrap();

        let data = dummy_data(32);

        let mut w1 = m.write(&mut pr, 1).await.unwrap();
        w1.write(&mut m, &data).await.unwrap();

        let mut w2 = m.write(&mut pr, 2).await.unwrap();
        w2.write(&mut m, &data).await.unwrap();

        m.commit(&mut w2).await.unwrap();
        m.commit(&mut w1).await.unwrap();

        let mut r = m.read(&mut pr, 1);
        let mut buf = [0; 32];
        r.read(&mut m, &mut buf).await.unwrap();
        assert_eq!(buf[..], data[..]);

        let mut r = m.read(&mut pr, 2);
        let mut buf = [0; 32];
        r.read(&mut m, &mut buf).await.unwrap();
        assert_eq!(buf[..], data[..]);

        // Remount
        m.mount(&mut pr).await.unwrap();

        let mut r = m.read(&mut pr, 1);
        let mut buf = [0; 32];
        r.read(&mut m, &mut buf).await.unwrap();
        assert_eq!(buf[..], data[..]);

        let mut r = m.read(&mut pr, 2);
        let mut buf = [0; 32];
        r.read(&mut m, &mut buf).await.unwrap();
        assert_eq!(buf[..], data[..]);
    }

    #[test_log::test(tokio::test)]
    async fn test_flags() {
        let mut f = MemFlash::new();
        let mut m = FileManager::new(&mut f, 0);
        let mut pr = PageReader::new();
        m.format().await.unwrap();
        m.mount(&mut pr).await.unwrap();

        assert_eq!(m.file_flags(1), 0x00);

        // flags for empty files stay at 0.
        let mut tx = m.transaction();
        tx.set_flags(1, 0x42).await.unwrap();
        tx.commit().await.unwrap();
        assert_eq!(m.file_flags(1), 0x00);

        // flags for nonempty files get set properly.
        let mut w = m.write(&mut pr, 1).await.unwrap();
        w.write(&mut m, &[0x00]).await.unwrap();
        let mut tx = m.transaction();
        w.commit(&mut tx).await.unwrap();
        tx.set_flags(1, 0x42).await.unwrap();
        tx.commit().await.unwrap();
        assert_eq!(m.file_flags(1), 0x42);

        // when writing to a file, old flags are kept if we don't `.set_flags()`
        let mut w = m.write(&mut pr, 1).await.unwrap();
        w.write(&mut m, &[0x00]).await.unwrap();
        m.commit(&mut w).await.unwrap();
        assert_eq!(m.file_flags(1), 0x42);

        // flags are kept across remounts.
        m.mount(&mut pr).await.unwrap();
        assert_eq!(m.file_flags(1), 0x42);

        // when truncating the file, flags are kept.
        m.truncate(1, 1).await.unwrap();
        assert_eq!(m.file_flags(1), 0x42);

        // when deleting the file, flags are gone.
        m.truncate(1, 1).await.unwrap();
        assert_eq!(m.file_flags(1), 0x00);

        // Remount
        m.mount(&mut pr).await.unwrap();
        assert_eq!(m.file_flags(1), 0x00);
    }

    #[test_log::test(tokio::test)]
    async fn test_record_boundary_one() {
        let mut f = MemFlash::new();
        let mut m = FileManager::new(&mut f, 0);
        let mut pr = PageReader::new();
        m.format().await.unwrap();
        m.mount(&mut pr).await.unwrap();

        let mut w = m.write(&mut pr, 1).await.unwrap();
        w.write(&mut m, &[0x00]).await.unwrap();
        w.record_end();
        m.commit(&mut w).await.unwrap();

        let h = m.read_header::<DataHeader>(page(1)).await.unwrap();
        assert_eq!(h.seq, Seq(0));
        assert_eq!(h.record_boundary, 0);
    }

    #[test_log::test(tokio::test)]
    async fn test_record_boundary_two() {
        let mut f = MemFlash::new();
        let mut m = FileManager::new(&mut f, 0);
        let mut pr = PageReader::new();
        m.format().await.unwrap();
        m.mount(&mut pr).await.unwrap();

        let mut w = m.write(&mut pr, 1).await.unwrap();
        w.write(&mut m, &[0x00]).await.unwrap();
        w.record_end();
        w.write(&mut m, &[0x00; PAGE_MAX_PAYLOAD_SIZE + 1]).await.unwrap();
        w.record_end();
        m.commit(&mut w).await.unwrap();

        let h = m.read_header::<DataHeader>(page(1)).await.unwrap();
        assert_eq!(h.seq, Seq(0));
        assert_eq!(h.record_boundary, 0);

        let h = m.read_header::<DataHeader>(page(2)).await.unwrap();
        assert_eq!(h.seq, Seq(PAGE_MAX_PAYLOAD_SIZE as u32));
        assert_eq!(h.record_boundary, u16::MAX);
    }

    #[test_log::test(tokio::test)]
    async fn test_record_boundary_three() {
        let mut f = MemFlash::new();
        let mut m = FileManager::new(&mut f, 0);
        let mut pr = PageReader::new();
        m.format().await.unwrap();
        m.mount(&mut pr).await.unwrap();

        let mut w = m.write(&mut pr, 1).await.unwrap();
        w.write(&mut m, &[0x00]).await.unwrap();
        w.record_end();
        w.write(&mut m, &[0x00; PAGE_MAX_PAYLOAD_SIZE + 1]).await.unwrap();
        w.record_end();
        w.write(&mut m, &[0x00]).await.unwrap();
        w.record_end();
        m.commit(&mut w).await.unwrap();

        let h = m.read_header::<DataHeader>(page(1)).await.unwrap();
        assert_eq!(h.seq, Seq(0));
        assert_eq!(h.record_boundary, 0);

        let h = m.read_header::<DataHeader>(page(2)).await.unwrap();
        assert_eq!(h.seq, Seq(PAGE_MAX_PAYLOAD_SIZE as u32));
        assert_eq!(h.record_boundary, 2);
    }

    #[test_log::test(tokio::test)]
    async fn test_record_boundary_overlong() {
        let mut f = MemFlash::new();
        let mut m = FileManager::new(&mut f, 0);
        let mut pr = PageReader::new();
        m.format().await.unwrap();
        m.mount(&mut pr).await.unwrap();

        let mut w = m.write(&mut pr, 1).await.unwrap();
        w.write(&mut m, &[0x00]).await.unwrap();
        w.record_end();
        w.write(&mut m, &[0x00; PAGE_MAX_PAYLOAD_SIZE * 2 + 1]).await.unwrap();
        w.record_end();
        m.commit(&mut w).await.unwrap();

        let h = m.read_header::<DataHeader>(page(1)).await.unwrap();
        assert_eq!(h.seq, Seq(0));
        assert_eq!(h.record_boundary, 0);

        let h = m.read_header::<DataHeader>(page(2)).await.unwrap();
        assert_eq!(h.seq, Seq(PAGE_MAX_PAYLOAD_SIZE as u32));
        assert_eq!(h.record_boundary, u16::MAX);

        let h = m.read_header::<DataHeader>(page(3)).await.unwrap();
        assert_eq!(h.seq, Seq(PAGE_MAX_PAYLOAD_SIZE as u32 * 2));
        assert_eq!(h.record_boundary, u16::MAX);
    }

    #[test_log::test(tokio::test)]
    async fn test_record_boundary_overlong_2() {
        let mut f = MemFlash::new();
        let mut m = FileManager::new(&mut f, 0);
        let mut pr = PageReader::new();
        m.format().await.unwrap();
        m.mount(&mut pr).await.unwrap();

        let mut w = m.write(&mut pr, 1).await.unwrap();
        w.write(&mut m, &[0x00]).await.unwrap();
        w.record_end();
        w.write(&mut m, &[0x00; PAGE_MAX_PAYLOAD_SIZE * 2 + 1]).await.unwrap();
        w.record_end();
        w.write(&mut m, &[0x00; PAGE_MAX_PAYLOAD_SIZE * 2 + 1]).await.unwrap();
        w.record_end();
        m.commit(&mut w).await.unwrap();

        let h = m.read_header::<DataHeader>(page(1)).await.unwrap();
        assert_eq!(h.seq, Seq(0));
        assert_eq!(h.record_boundary, 0);

        let h = m.read_header::<DataHeader>(page(2)).await.unwrap();
        assert_eq!(h.seq, Seq(PAGE_MAX_PAYLOAD_SIZE as u32));
        assert_eq!(h.record_boundary, u16::MAX);

        let h = m.read_header::<DataHeader>(page(3)).await.unwrap();
        assert_eq!(h.seq, Seq(PAGE_MAX_PAYLOAD_SIZE as u32 * 2));
        assert_eq!(h.record_boundary, 2);

        let h = m.read_header::<DataHeader>(page(4)).await.unwrap();
        assert_eq!(h.seq, Seq(PAGE_MAX_PAYLOAD_SIZE as u32 * 3));
        assert_eq!(h.record_boundary, u16::MAX);

        let h = m.read_header::<DataHeader>(page(5)).await.unwrap();
        assert_eq!(h.seq, Seq(PAGE_MAX_PAYLOAD_SIZE as u32 * 4));
        assert_eq!(h.record_boundary, u16::MAX);
    }

    #[test_log::test(tokio::test)]
    async fn test_record_boundary_overlong_3() {
        let mut f = MemFlash::new();
        let mut m = FileManager::new(&mut f, 0);
        let mut pr = PageReader::new();
        m.format().await.unwrap();
        m.mount(&mut pr).await.unwrap();

        let mut w = m.write(&mut pr, 1).await.unwrap();
        w.write(&mut m, &[0x00]).await.unwrap();
        w.record_end();
        w.write(&mut m, &[0x00; PAGE_MAX_PAYLOAD_SIZE * 2 + 1]).await.unwrap();
        w.record_end();
        w.write(&mut m, &[0x00; PAGE_MAX_PAYLOAD_SIZE * 2 + 1]).await.unwrap();
        w.record_end();
        w.write(&mut m, &[0x00]).await.unwrap();
        w.record_end();
        w.write(&mut m, &[0x00]).await.unwrap();
        w.record_end();
        w.write(&mut m, &[0x00]).await.unwrap();
        w.record_end();

        m.commit(&mut w).await.unwrap();

        let h = m.read_header::<DataHeader>(page(1)).await.unwrap();
        assert_eq!(h.seq, Seq(0));
        assert_eq!(h.record_boundary, 0);

        let h = m.read_header::<DataHeader>(page(2)).await.unwrap();
        assert_eq!(h.seq, Seq(PAGE_MAX_PAYLOAD_SIZE as u32));
        assert_eq!(h.record_boundary, u16::MAX);

        let h = m.read_header::<DataHeader>(page(3)).await.unwrap();
        assert_eq!(h.seq, Seq(PAGE_MAX_PAYLOAD_SIZE as u32 * 2));
        assert_eq!(h.record_boundary, 2);

        let h = m.read_header::<DataHeader>(page(4)).await.unwrap();
        assert_eq!(h.seq, Seq(PAGE_MAX_PAYLOAD_SIZE as u32 * 3));
        assert_eq!(h.record_boundary, u16::MAX);

        let h = m.read_header::<DataHeader>(page(5)).await.unwrap();
        assert_eq!(h.seq, Seq(PAGE_MAX_PAYLOAD_SIZE as u32 * 4));
        assert_eq!(h.record_boundary, 3);
    }

    #[test_log::test(tokio::test)]
    async fn test_record_boundary_exact_page() {
        let mut f = MemFlash::new();
        let mut m = FileManager::new(&mut f, 0);
        let mut pr = PageReader::new();
        m.format().await.unwrap();
        m.mount(&mut pr).await.unwrap();

        let mut w = m.write(&mut pr, 1).await.unwrap();
        w.write(&mut m, &[0x00; PAGE_MAX_PAYLOAD_SIZE]).await.unwrap();
        w.record_end();
        w.write(&mut m, &[0x00; PAGE_MAX_PAYLOAD_SIZE]).await.unwrap();
        w.record_end();
        w.write(&mut m, &[0x00]).await.unwrap();
        w.record_end();
        m.commit(&mut w).await.unwrap();

        let h = m.read_header::<DataHeader>(page(1)).await.unwrap();
        assert_eq!(h.seq, Seq(0));
        assert_eq!(h.record_boundary, 0);

        let h = m.read_header::<DataHeader>(page(2)).await.unwrap();
        assert_eq!(h.seq, Seq(PAGE_MAX_PAYLOAD_SIZE as u32));
        assert_eq!(h.record_boundary, 0);

        let h = m.read_header::<DataHeader>(page(3)).await.unwrap();
        assert_eq!(h.seq, Seq(PAGE_MAX_PAYLOAD_SIZE as u32 * 2));
        assert_eq!(h.record_boundary, 0);
    }

    #[test_log::test(tokio::test)]
    async fn test_hydration() {
        let mut f = MemFlash::new();
        let mut m = FileManager::new(&mut f, 0);
        let mut pr = PageReader::new();
        m.format().await.unwrap();
        m.mount(&mut pr).await.unwrap();

        let mut w = m.write(&mut pr, 1).await.unwrap();
        w.write(&mut m, &[1, 2, 3, 4, 5, 6, 7, 8]).await.unwrap();
        w.record_end();
        m.commit(&mut w).await.unwrap();

        let mut r = m.read(&mut pr, 1);

        let dehydrated_start = r.dehydrate();

        let mut buf = [0; 3];
        r.read(&mut m, &mut buf).await.unwrap();
        assert_eq!(buf, [1, 2, 3]);

        let dehydrated_middle = r.dehydrate();

        let mut buf = [0; 5];
        r.read(&mut m, &mut buf).await.unwrap();
        assert_eq!(buf, [4, 5, 6, 7, 8]);

        let dehydrated_end = r.dehydrate();

        let mut buf = [0; 1];
        let res = r.read(&mut m, &mut buf).await;
        assert!(matches!(res, Err(ReadError::Eof)));

        let mut r = m.read_rehydrated(&mut pr, &dehydrated_start).await.unwrap();
        let mut buf = [0; 8];
        r.read(&mut m, &mut buf).await.unwrap();
        assert_eq!(buf, [1, 2, 3, 4, 5, 6, 7, 8]);
        let mut buf = [0; 1];
        let res = r.read(&mut m, &mut buf).await;
        assert!(matches!(res, Err(ReadError::Eof)));

        let mut r = m.read_rehydrated(&mut pr, &dehydrated_middle).await.unwrap();
        let mut buf = [0; 5];
        r.read(&mut m, &mut buf).await.unwrap();
        assert_eq!(buf, [4, 5, 6, 7, 8]);
        let mut buf = [0; 1];
        let res = r.read(&mut m, &mut buf).await;
        assert!(matches!(res, Err(ReadError::Eof)));

        let mut r = m.read_rehydrated(&mut pr, &dehydrated_end).await.unwrap();
        let mut buf = [0; 1];
        let res = r.read(&mut m, &mut buf).await;
        assert!(matches!(res, Err(ReadError::Eof)));
    }

    #[test_log::test(tokio::test)]
    async fn test_search_empty() {
        let mut f = MemFlash::new();
        let mut m = FileManager::new(&mut f, 0);
        let mut pr = PageReader::new();
        m.format().await.unwrap();
        m.mount(&mut pr).await.unwrap();

        let mut s = FileSearcher::new(m.read(&mut pr, 1));
        assert_eq!(s.start(&mut m).await.unwrap(), false);
        assert_eq!(s.reader().offset(&mut m), 0);
    }

    #[test_log::test(tokio::test)]
    async fn test_search_one_page() {
        let mut f = MemFlash::new();
        let mut m = FileManager::new(&mut f, 0);
        let mut pr = PageReader::new();
        m.format().await.unwrap();
        m.mount(&mut pr).await.unwrap();

        let mut w = m.write(&mut pr, 1).await.unwrap();
        w.write(&mut m, &[0x00]).await.unwrap();
        m.commit(&mut w).await.unwrap();

        // start immediately return false, because there's nothing to bisect.
        // Only possible point to seek is start of the only page.
        let mut s = FileSearcher::new(m.read(&mut pr, 1));
        assert_eq!(s.start(&mut m).await.unwrap(), false);
        assert_eq!(s.reader().offset(&mut m), 0);
    }

    #[test_log::test(tokio::test)]
    async fn test_search_two_pages() {
        let mut f = MemFlash::new();
        let mut m = FileManager::new(&mut f, 0);
        let mut pr = PageReader::new();
        m.format().await.unwrap();
        m.mount(&mut pr).await.unwrap();

        let mut w = m.write(&mut pr, 1).await.unwrap();
        for _ in 0..2 {
            w.write(&mut m, &[0x00; PAGE_MAX_PAYLOAD_SIZE]).await.unwrap();
            w.record_end();
        }
        m.commit(&mut w).await.unwrap();

        let mut s = FileSearcher::new(m.read(&mut pr, 1));
        assert_eq!(s.start(&mut m).await.unwrap(), true);
        assert_eq!(s.reader().offset(&mut m), PAGE_MAX_PAYLOAD_SIZE);
        assert_eq!(s.seek(&mut m, SeekDirection::Left).await.unwrap(), false);
        assert_eq!(s.reader().offset(&mut m), 0);

        let mut s = FileSearcher::new(m.read(&mut pr, 1));
        assert_eq!(s.start(&mut m).await.unwrap(), true);
        assert_eq!(s.reader().offset(&mut m), PAGE_MAX_PAYLOAD_SIZE);
        assert_eq!(s.seek(&mut m, SeekDirection::Right).await.unwrap(), false);
        assert_eq!(s.reader().offset(&mut m), PAGE_MAX_PAYLOAD_SIZE);
    }

    #[test_log::test(tokio::test)]
    async fn test_search_no_boundary_on_second_page() {
        let mut f = MemFlash::new();
        let mut m = FileManager::new(&mut f, 0);
        let mut pr = PageReader::new();
        m.format().await.unwrap();
        m.mount(&mut pr).await.unwrap();

        let mut w = m.write(&mut pr, 1).await.unwrap();
        w.write(&mut m, &[0x00; 238]).await.unwrap();
        w.record_end();
        m.commit(&mut w).await.unwrap();

        // start immediately return false, because there's nothing to bisect.
        // Only possible point to seek is start of the only page.
        let mut s = FileSearcher::new(m.read(&mut pr, 1));
        assert_eq!(s.start(&mut m).await.unwrap(), false);
        assert_eq!(s.reader().offset(&mut m), 0);
    }

    #[test_log::test(tokio::test)]
    async fn test_search_no_boundary_more_pages() {
        let mut f = MemFlash::new();
        let mut m = FileManager::new(&mut f, 0);
        let mut pr = PageReader::new();
        m.format().await.unwrap();
        m.mount(&mut pr).await.unwrap();

        let mut w = m.write(&mut pr, 1).await.unwrap();
        w.write(&mut m, &[0x00; 4348]).await.unwrap();
        w.record_end();
        m.commit(&mut w).await.unwrap();

        // start immediately return false, because there's nothing to bisect.
        // Only possible point to seek is start of the only page.
        let mut s = FileSearcher::new(m.read(&mut pr, 1));
        assert_eq!(s.start(&mut m).await.unwrap(), false);
        assert_eq!(s.reader().offset(&mut m), 0);
    }

    #[test_log::test(tokio::test)]
    async fn test_search_no_boundary_more_pages_two() {
        let mut f = MemFlash::new();
        let mut m = FileManager::new(&mut f, 0);
        let mut pr = PageReader::new();
        m.format().await.unwrap();
        m.mount(&mut pr).await.unwrap();

        let mut w = m.write(&mut pr, 1).await.unwrap();
        w.write(&mut m, &[0x00; 4348]).await.unwrap();
        w.record_end();
        w.write(&mut m, &[0x00; 4348]).await.unwrap();
        w.record_end();
        m.commit(&mut w).await.unwrap();

        let mut buf = [0u8; 1];
        // Seek left
        let mut s = FileSearcher::new(m.read(&mut pr, 1));
        assert_eq!(s.start(&mut m).await.unwrap(), true);
        assert_eq!(s.reader().offset(&mut m), 4348);
        s.reader().read(&mut m, &mut buf).await.unwrap();
        assert_eq!(s.seek(&mut m, SeekDirection::Left).await.unwrap(), false);
        assert_eq!(s.reader().offset(&mut m), 0);

        // Seek right
        let mut s = FileSearcher::new(m.read(&mut pr, 1));
        assert_eq!(s.start(&mut m).await.unwrap(), true);
        assert_eq!(s.reader().offset(&mut m), 4348);
        s.reader().read(&mut m, &mut buf).await.unwrap();
        assert_eq!(s.seek(&mut m, SeekDirection::Right).await.unwrap(), false);
        assert_eq!(s.reader().offset(&mut m), 4348);
    }

    #[test_log::test(tokio::test)]
    async fn test_search_no_boundary_more_pages_three() {
        let mut f = MemFlash::new();
        let mut m = FileManager::new(&mut f, 0);
        let mut pr = PageReader::new();
        m.format().await.unwrap();
        m.mount(&mut pr).await.unwrap();

        let mut w = m.write(&mut pr, 1).await.unwrap();
        w.write(&mut m, &[0x00; 4348]).await.unwrap();
        w.record_end();
        w.write(&mut m, &[0x00; 4348]).await.unwrap();
        w.record_end();
        w.write(&mut m, &[0x00; 4348]).await.unwrap();
        w.record_end();
        m.commit(&mut w).await.unwrap();

        let mut buf = [0u8; 1];
        // Seek left
        let mut s = FileSearcher::new(m.read(&mut pr, 1));
        assert_eq!(s.start(&mut m).await.unwrap(), true);
        assert_eq!(s.reader().offset(&mut m), 8696);
        s.reader().read(&mut m, &mut buf).await.unwrap();
        assert_eq!(s.seek(&mut m, SeekDirection::Left).await.unwrap(), true);
        assert_eq!(s.reader().offset(&mut m), 4348);
        s.reader().read(&mut m, &mut buf).await.unwrap();
        assert_eq!(s.seek(&mut m, SeekDirection::Left).await.unwrap(), false);
        assert_eq!(s.reader().offset(&mut m), 0);

        // Seek less left
        let mut s = FileSearcher::new(m.read(&mut pr, 1));
        assert_eq!(s.start(&mut m).await.unwrap(), true);
        assert_eq!(s.reader().offset(&mut m), 8696);
        s.reader().read(&mut m, &mut buf).await.unwrap();
        assert_eq!(s.seek(&mut m, SeekDirection::Left).await.unwrap(), true);
        assert_eq!(s.reader().offset(&mut m), 4348);
        s.reader().read(&mut m, &mut buf).await.unwrap();
        assert_eq!(s.seek(&mut m, SeekDirection::Left).await.unwrap(), false);
        assert_eq!(s.reader().offset(&mut m), 0);

        // Seek middle
        let mut s = FileSearcher::new(m.read(&mut pr, 1));
        assert_eq!(s.start(&mut m).await.unwrap(), true);
        assert_eq!(s.reader().offset(&mut m), 8696);
        s.reader().read(&mut m, &mut buf).await.unwrap();
        assert_eq!(s.seek(&mut m, SeekDirection::Left).await.unwrap(), true);
        assert_eq!(s.reader().offset(&mut m), 4348);
        s.reader().read(&mut m, &mut buf).await.unwrap();
        assert_eq!(s.seek(&mut m, SeekDirection::Right).await.unwrap(), false);
        assert_eq!(s.reader().offset(&mut m), 4348);

        // Seek right
        let mut s = FileSearcher::new(m.read(&mut pr, 1));
        assert_eq!(s.start(&mut m).await.unwrap(), true);
        assert_eq!(s.reader().offset(&mut m), 8696);
        s.reader().read(&mut m, &mut buf).await.unwrap();
        assert_eq!(s.seek(&mut m, SeekDirection::Right).await.unwrap(), false);
        assert_eq!(s.reader().offset(&mut m), 8696);
    }

    #[test_log::test(tokio::test)]
    async fn test_search_truncate() {
        let mut f = MemFlash::new();
        let mut m = FileManager::new(&mut f, 0);
        let mut pr = PageReader::new();
        m.format().await.unwrap();
        m.mount(&mut pr).await.unwrap();

        const N: usize = PAGE_MAX_PAYLOAD_SIZE + 3;
        let mut w = m.write(&mut pr, 1).await.unwrap();
        w.write(&mut m, &[0x00; N]).await.unwrap();
        w.record_end();
        w.write(&mut m, &[0x00; N]).await.unwrap();
        w.record_end();
        w.write(&mut m, &[0x00; N]).await.unwrap();
        w.record_end();
        w.write(&mut m, &[0x00; N]).await.unwrap();
        w.record_end();
        m.commit(&mut w).await.unwrap();

        let mut buf = [0u8; 1];
        // Seek left
        let mut s = FileSearcher::new(m.read(&mut pr, 1));
        assert_eq!(s.start(&mut m).await.unwrap(), true);
        assert_eq!(s.reader().offset(&mut m), N * 2);
        s.reader().read(&mut m, &mut buf).await.unwrap();
        assert_eq!(s.seek(&mut m, SeekDirection::Left).await.unwrap(), true);
        assert_eq!(s.reader().offset(&mut m), N);
        s.reader().read(&mut m, &mut buf).await.unwrap();
        assert_eq!(s.seek(&mut m, SeekDirection::Left).await.unwrap(), false);
        assert_eq!(s.reader().offset(&mut m), 0);

        m.truncate(1, N * 2).await.unwrap();

        // Seek left
        let mut s = FileSearcher::new(m.read(&mut pr, 1));
        assert_eq!(s.start(&mut m).await.unwrap(), true);
        assert_eq!(s.reader().offset(&mut m), N);
        s.reader().read(&mut m, &mut buf).await.unwrap();
        assert_eq!(s.seek(&mut m, SeekDirection::Left).await.unwrap(), false);
        assert_eq!(s.reader().offset(&mut m), 0);

        m.truncate(1, N).await.unwrap();

        // Seek left
        let mut s = FileSearcher::new(m.read(&mut pr, 1));
        assert_eq!(s.start(&mut m).await.unwrap(), false);
        assert_eq!(s.reader().offset(&mut m), 0);
    }

    #[test_log::test(tokio::test)]
    async fn test_search_long() {
        let mut f = MemFlash::new();
        let mut m = FileManager::new(&mut f, 0);
        let mut pr = PageReader::new();
        m.format().await.unwrap();
        m.mount(&mut pr).await.unwrap();

        let count: u32 = 20000 / 4;

        let mut w = m.write(&mut pr, 1).await.unwrap();
        for i in 1..=count {
            w.write(&mut m, &i.to_le_bytes()).await.unwrap();
            // make records not line up with page boundaries.
            w.write(&mut m, &[0x00]).await.unwrap();
            w.record_end();
        }
        m.commit(&mut w).await.unwrap();

        for want in 0..count + 1 {
            debug!("searching for {}", want);

            let mut s = FileSearcher::new(m.read(&mut pr, 1));
            assert_eq!(s.start(&mut m).await.unwrap(), true);

            loop {
                let mut record = [0; 4];
                s.reader().read(&mut m, &mut record).await.unwrap();
                let record = u32::from_le_bytes(record);

                let dir = if record >= want {
                    SeekDirection::Left
                } else {
                    SeekDirection::Right
                };
                let ok = s.seek(&mut m, dir).await.unwrap();
                if !ok {
                    break;
                }
            }

            let mut record = [0; 4];
            s.reader().read(&mut m, &mut record).await.unwrap();
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

    #[test_log::test(tokio::test)]
    async fn test_smoke() {
        let mut f = MemFlash::new();
        let mut m = FileManager::new(&mut f, 0);
        let mut pr = PageReader::new();
        m.format().await.unwrap();
        m.mount(&mut pr).await.unwrap();

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
                    m.truncate(file_id, s).await.unwrap();
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

                    let mut w = m.write(&mut pr, file_id).await.unwrap();
                    w.write(&mut m, &data).await.unwrap();
                    m.commit(&mut w).await.unwrap();

                    seq_max += n;
                }
            }

            // ============ Check read all
            debug!("{} {}, read_all", seq_min, seq_max);

            let mut r = m.read(&mut pr, file_id);
            let mut data = vec![0; seq_max - seq_min];
            r.read(&mut m, &mut data).await.unwrap();
            let want_data: Vec<_> = (0..seq_max - seq_min).map(|i| (seq_min + i) as u8).collect();
            assert_eq!(data, want_data);

            // Check we're at EOF
            let mut buf = [0; 1];
            assert_eq!(r.read(&mut m, &mut buf).await, Err(ReadError::Eof));

            // ============ Check read seek
            let s = rand_between(0, seq_max - seq_min);
            debug!("{} {}, read_seek {}", seq_min, seq_max, s);

            let mut r = m.read(&mut pr, file_id);
            r.seek(&mut m, s).await.unwrap();
            let mut data = vec![0; seq_max - seq_min - s];
            r.read(&mut m, &mut data).await.unwrap();
            let want_data: Vec<_> = (0..seq_max - seq_min - s).map(|i| (seq_min + s + i) as u8).collect();
            assert_eq!(data, want_data);

            // Check we're at EOF
            let mut buf = [0; 1];
            assert_eq!(r.read(&mut m, &mut buf).await, Err(ReadError::Eof));

            // ============ Check read skip
            let s1 = rand_between(0, seq_max - seq_min);
            let s2 = rand_between(0, seq_max - seq_min - s1);
            debug!("{} {}, read_skip {} {}", seq_min, seq_max, s1, s2);

            let mut r = m.read(&mut pr, file_id);
            r.skip(&mut m, s1).await.unwrap();
            r.skip(&mut m, s2).await.unwrap();
            let mut data = vec![0; seq_max - seq_min - s1 - s2];
            r.read(&mut m, &mut data).await.unwrap();
            let want_data: Vec<_> = (0..seq_max - seq_min - s1 - s2)
                .map(|i| (seq_min + s1 + s2 + i) as u8)
                .collect();
            assert_eq!(data, want_data);

            // Check we're at EOF
            let mut buf = [0; 1];
            assert_eq!(r.read(&mut m, &mut buf).await, Err(ReadError::Eof));
        }
    }

    #[test_log::test(tokio::test)]
    async fn test_max_trailing_zeros_between() {
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

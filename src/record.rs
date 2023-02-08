use core::cell::RefCell;
use core::cmp::Ordering;
use core::future::poll_fn;
use core::mem::{size_of, MaybeUninit};
use core::ops::{Deref, DerefMut};
use core::slice;
use core::task::Poll;

use embassy_sync::blocking_mutex::raw::NoopRawMutex;
use embassy_sync::mutex::Mutex;
use embassy_sync::waitqueue::WakerRegistration;
use heapless::Vec;

use crate::config::*;
use crate::errors::{CorruptedError, Error, ReadError, WriteError};
use crate::file::{
    DataHeader, FileManager, FileReader, FileSearcher, FileWriter, MetaHeader, SeekDirection, PAGE_MAX_PAYLOAD_SIZE,
};
use crate::flash::Flash;
use crate::page::ReadError as PageReadError;
use crate::{CommitError, FormatError};

const FILE_FLAG_COMPACT_DEST: u8 = 0x01;
const FILE_FLAG_COMPACT_SRC: u8 = 0x02;

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
#[non_exhaustive]
pub enum FormatConfig {
    Never,
    IfNotFormatted,
    Format,
}

#[derive(Debug, Clone, Eq, PartialEq)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
#[non_exhaustive]
pub struct Config {
    pub format: FormatConfig,
}

impl Default for Config {
    fn default() -> Self {
        Self::default()
    }
}

impl Config {
    const fn default() -> Self {
        Self {
            format: FormatConfig::Never,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
enum WriteTxState {
    Idle,
    Created,
    Committing,
}

// We allow N read transactions XOR 1 write transaction.
struct State {
    read_tx_count: usize,
    write_tx: WriteTxState,
    waker: WakerRegistration,
}

pub struct Database<F: Flash> {
    state: RefCell<State>,

    inner: Mutex<NoopRawMutex, Inner<F>>,
}

impl<F: Flash> Database<F> {
    pub async fn new(flash: F, config: Config) -> Result<Self, Error<F::Error>> {
        let mut inner = Inner::new(flash).await;

        match config.format {
            FormatConfig::Format => {
                inner.format().await?;
                inner.mount().await?;
            }
            FormatConfig::IfNotFormatted => match inner.mount().await {
                Ok(()) => {}
                Err(Error::Corrupted) => {
                    inner.format().await?;
                    inner.mount().await?;
                }
                Err(e) => return Err(e),
            },
            FormatConfig::Never => {
                inner.mount().await?;
            }
        }

        Ok(Self {
            inner: Mutex::new(inner),
            state: RefCell::new(State {
                read_tx_count: 0,
                write_tx: WriteTxState::Idle,
                waker: WakerRegistration::new(),
            }),
        })
    }

    pub async fn lock_flash(&self) -> impl Deref<Target = F> + DerefMut + '_ {
        FlashLockGuard(self.inner.lock().await)
    }

    pub async fn format(&self) -> Result<(), FormatError<F::Error>> {
        todo!()
    }

    #[cfg(feature = "std")]
    pub async fn dump(&self) {
        self.inner.lock().await.dump().await
    }

    pub async fn read_transaction(&self) -> ReadTransaction<'_, F> {
        poll_fn(|cx| {
            let s = &mut *self.state.borrow_mut();

            // If there's a write transaction either
            // - committing, or
            // - trying to commit, waiting for other read transactions to end,
            // then we don't let new read transactions start.
            //
            // The latter is needed to avoid a commit to get stuck forever if other
            // tasks are constantly doing reads.
            if s.write_tx == WriteTxState::Committing {
                s.waker.register(cx.waker());
                return Poll::Pending;
            }

            // NOTE(unwrap): we'll panic if there's 2^32 concurrent read txs, that's fine.
            s.read_tx_count = s.read_tx_count.checked_add(1).unwrap();
            Poll::Ready(())
        })
        .await;

        ReadTransaction { db: self }
    }

    pub async fn write_transaction(&self) -> WriteTransaction<'_, F> {
        poll_fn(|cx| {
            let s = &mut *self.state.borrow_mut();
            if s.write_tx != WriteTxState::Idle {
                s.waker.register(cx.waker());
                return Poll::Pending;
            }
            s.write_tx = WriteTxState::Created;
            Poll::Ready(())
        })
        .await;

        WriteTransaction {
            db: self,
            state: WriteTransactionState::Created,
        }
    }
}

struct FlashLockGuard<G, F>(G)
where
    G: Deref<Target = Inner<F>> + DerefMut,
    F: Flash;

impl<G, F> DerefMut for FlashLockGuard<G, F>
where
    G: Deref<Target = Inner<F>> + DerefMut,
    F: Flash,
{
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.0.files.flash_mut()
    }
}

impl<G, F> Deref for FlashLockGuard<G, F>
where
    G: Deref<Target = Inner<F>> + DerefMut,
    F: Flash,
{
    type Target = F;
    fn deref(&self) -> &Self::Target {
        self.0.files.flash()
    }
}

pub struct ReadTransaction<'a, F: Flash + 'a> {
    db: &'a Database<F>,
}

impl<'a, F: Flash + 'a> Drop for ReadTransaction<'a, F> {
    fn drop(&mut self) {
        let s = &mut *self.db.state.borrow_mut();

        // NOTE(unwrap): It's impossible that read_tx_count==0, because at least one
        // read transaction was in progress: the one we're dropping now.
        s.read_tx_count = s.read_tx_count.checked_sub(1).unwrap();
        if s.read_tx_count == 0 {
            s.waker.wake();
        }
    }
}

impl<'a, F: Flash + 'a> ReadTransaction<'a, F> {
    pub async fn read(&mut self, key: &[u8], value: &mut [u8]) -> Result<usize, ReadError<F::Error>> {
        if key.len() > MAX_KEY_SIZE {
            return Err(ReadError::KeyTooBig);
        }

        self.db.inner.lock().await.read(key, value).await
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
enum WriteTransactionState {
    Created,
    InProgress,
    Canceled,
}

pub struct WriteTransaction<'a, F: Flash + 'a> {
    db: &'a Database<F>,
    state: WriteTransactionState,
}

impl<'a, F: Flash + 'a> Drop for WriteTransaction<'a, F> {
    fn drop(&mut self) {
        let s = &mut *self.db.state.borrow_mut();

        assert!(s.write_tx != WriteTxState::Idle);
        s.write_tx = WriteTxState::Idle;
        s.waker.wake();
    }
}

impl<'a, F: Flash + 'a> WriteTransaction<'a, F> {
    pub async fn write(&mut self, key: &[u8], value: &[u8]) -> Result<(), WriteError<F::Error>> {
        let is_first_write = match self.state {
            WriteTransactionState::Canceled => return Err(WriteError::TransactionCanceled),
            WriteTransactionState::Created => true,
            WriteTransactionState::InProgress => false,
        };

        if key.len() > MAX_KEY_SIZE {
            return Err(WriteError::KeyTooBig);
        }
        if value.len() > MAX_VALUE_SIZE {
            return Err(WriteError::ValueTooBig);
        }

        // Canceling a call to `write()` (dropping its `Future` before it's done) can leave
        // the transaction in an undefined state, so we cancel it entirely.
        self.state = WriteTransactionState::Canceled;

        // If inner `write` fails, we also cancel the transaction.
        let mut db = self.db.inner.lock().await;
        if is_first_write {
            db.rollback_if_any().await?;
        }
        db.write(key, value).await?;

        self.state = WriteTransactionState::InProgress;

        Ok(())
    }

    pub async fn commit(self) -> Result<(), CommitError<F::Error>> {
        match self.state {
            WriteTransactionState::Canceled => return Err(CommitError::TransactionCanceled),
            WriteTransactionState::Created => return Ok(()),
            WriteTransactionState::InProgress => {}
        }

        // First switch to Committing, so that no new read txs can start.
        {
            let s = &mut *self.db.state.borrow_mut();
            assert!(s.write_tx == WriteTxState::Created);
            s.write_tx = WriteTxState::Committing;
        }

        // Then wait for the existing read txs to finish.
        poll_fn(|cx| {
            let s = &mut *self.db.state.borrow_mut();
            if s.read_tx_count != 0 {
                s.waker.register(cx.waker());
                return Poll::Pending;
            }
            Poll::Ready(())
        })
        .await;

        // do commit
        self.db.inner.lock().await.commit().await?;

        // Here self gets dropped, which unlocks the write in `Database`, to let
        // read transactions proceed again.

        Ok(())
    }
}

struct Inner<F: Flash> {
    files: FileManager<F>,
    write_tx: Option<WriteTransactionInner>,
}

impl<F: Flash> Inner<F> {
    async fn new(flash: F) -> Self {
        debug!("creating database!");
        debug!(
            "page_size={}, page_count={}, total_size={}",
            PAGE_SIZE,
            PAGE_COUNT,
            PAGE_COUNT * PAGE_SIZE
        );
        debug!("write_size={}, erase_value={:02x}", WRITE_SIZE, ERASE_VALUE);
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
            "free_page_buffer={}, free_page_buffer_commit={}",
            FREE_PAGE_BUFFER, FREE_PAGE_BUFFER_COMMIT
        );

        Self {
            files: FileManager::new(flash),
            write_tx: None,
        }
    }

    async fn format(&mut self) -> Result<(), FormatError<F::Error>> {
        assert!(self.write_tx.is_none());
        self.files.format().await
    }

    async fn mount(&mut self) -> Result<(), Error<F::Error>> {
        assert!(self.write_tx.is_none());
        self.files.mount().await
    }

    async fn read(&mut self, key: &[u8], value: &mut [u8]) -> Result<usize, ReadError<F::Error>> {
        for file_id in (0..FILE_COUNT).rev() {
            if let Some(res) = self.read_in_file(file_id as _, key, value).await? {
                return Ok(res);
            }
        }
        Ok(0)
    }

    async fn read_in_file(
        &mut self,
        file_id: FileID,
        key: &[u8],
        value: &mut [u8],
    ) -> Result<Option<usize>, ReadError<F::Error>> {
        let r = self.files.read(file_id).await;
        let m = &mut self.files;
        let mut s = FileSearcher::new(r);

        let mut key_buf = Vec::new();

        // Binary search
        let mut ok = s.start(m).await?;
        while ok {
            match read_key(m, s.reader(), &mut key_buf).await {
                Err(PageReadError::Eof) => return Ok(None), // key not present.
                x => x?,
            };

            // Found?
            let dir = match key_buf[..].cmp(key) {
                Ordering::Equal => return Ok(Some(read_value(m, s.reader(), value).await?)),
                Ordering::Less => SeekDirection::Right,
                Ordering::Greater => SeekDirection::Left,
            };

            // Not found, do a binary search step.
            ok = s.seek(m, dir).await?;
        }

        let r = s.reader();

        // Linear search
        loop {
            match read_key(m, r, &mut key_buf).await {
                Err(PageReadError::Eof) => return Ok(None), // key not present.
                x => x?,
            }

            // Found?
            match key_buf[..].cmp(key) {
                Ordering::Equal => return Ok(Some(read_value(m, r, value).await?)),
                Ordering::Less => {}                  // keep going
                Ordering::Greater => return Ok(None), // not present.
            }

            skip_value(m, r).await?;
        }
    }

    async fn ensure_write_transaction_started(&mut self) -> Result<(), Error<F::Error>> {
        if self.write_tx.is_some() {
            return Ok(());
        }

        debug!("write_transaction: start");

        let file_id = loop {
            match self.new_file_in_level(LEVEL_COUNT - 1) {
                Some(f) => break f,
                None => {
                    debug!("write_transaction: no free file, compacting.");
                    let did_something = self.compact().await?;

                    // if last level is full, compact should always
                    // find something to do.
                    assert!(did_something);
                }
            }
        };

        debug!("write_transaction: writing file {}", file_id);
        let w = self.files.write(file_id).await?;

        self.write_tx = Some(WriteTransactionInner { w, last_key: None });

        Ok(())
    }

    async fn write(&mut self, key: &[u8], value: &[u8]) -> Result<(), WriteError<F::Error>> {
        self.ensure_write_transaction_started().await?;
        let tx = self.write_tx.as_mut().unwrap();

        if let Some(last_key) = &tx.last_key {
            if key <= last_key {
                panic!("writes within a transaction must be sorted.");
            }
        }
        tx.last_key = Some(Vec::from_slice(key).unwrap());

        loop {
            let tx = self.write_tx.as_mut().unwrap();

            let record_size = record_size(key.len(), value.len());
            let need_size = record_size + FREE_PAGE_BUFFER * PAGE_MAX_PAYLOAD_SIZE;
            let available_size = tx.w.space_left_on_current_page() + self.files.free_pages() * PAGE_MAX_PAYLOAD_SIZE;
            if need_size <= available_size {
                break;
            }

            debug!("free pages less than buffer, compacting.");
            let did_something = self.compact().await?;
            if !did_something {
                debug!("storage full");
                return Err(WriteError::Full);
            }
        }

        let tx = self.write_tx.as_mut().unwrap();
        write_record(&mut self.files, &mut tx.w, key, value).await?;

        Ok(())
    }

    async fn commit(&mut self) -> Result<(), Error<F::Error>> {
        debug!("write_transaction: commit");

        let tx = self.write_tx.as_mut().unwrap();
        self.files.commit(&mut tx.w).await?;

        self.write_tx = None;

        Ok(())
    }

    async fn rollback(&mut self) -> Result<(), Error<F::Error>> {
        debug!("write_transaction: rollback");

        let _tx = self.write_tx.as_mut().unwrap();
        // TODO: free pages.

        self.write_tx = None;

        Ok(())
    }

    async fn rollback_if_any(&mut self) -> Result<(), Error<F::Error>> {
        if self.write_tx.is_some() {
            self.rollback().await?
        }
        Ok(())
    }

    fn file_id(level: usize, index: usize) -> FileID {
        (1 + level * BRANCHING_FACTOR + index) as _
    }

    /// Get a file_id suitable for appending data to a given level, if possible.
    fn new_file_in_level(&mut self, level: usize) -> Option<FileID> {
        // Get the first empty slot that doesn't have a nonempty slot after it.
        // This is important, because the new file must be the last in the level.

        let mut res = None;
        for i in 0..BRANCHING_FACTOR {
            let file_id = Self::file_id(level, i);
            if self.files.is_empty(file_id) {
                if res.is_none() {
                    res = Some(file_id)
                }
            } else {
                res = None
            }
        }
        res
    }

    fn is_level_full(&self, level: usize) -> bool {
        (0..BRANCHING_FACTOR).all(|i| !self.files.is_empty(Self::file_id(level, i)))
    }

    fn level_file_count(&self, level: usize) -> usize {
        (0..BRANCHING_FACTOR)
            .filter(|&i| !self.files.is_empty(Self::file_id(level, i)))
            .count()
    }

    fn compact_find_work(&mut self) -> Result<Option<(Vec<FileID, BRANCHING_FACTOR>, FileID)>, CorruptedError> {
        // Check if there's an in-progress compaction that we should continue.
        match self.files.files_with_flag(FILE_FLAG_COMPACT_DEST).single() {
            Ok(dst) => {
                debug!("compact_find_work: continuing in-progress compact.");
                let mut src = Vec::new();
                for src_file in self.files.files_with_flag(FILE_FLAG_COMPACT_SRC) {
                    if src_file <= dst {
                        // All src files should be after dst in the tree.
                        corrupted!()
                    }

                    if src.push(src_file).is_err() {
                        // at most BRANCHING_FACTOR src files
                        corrupted!()
                    }
                }
                return Ok(Some((src, dst)));
            }
            Err(SingleError::MultipleElements) => corrupted!(), // should never happen
            Err(SingleError::NoElements) => {}                  // no compaction in progress
        }

        // File 0 should always be empty if there's no in-progress compaction.
        if !self.files.is_empty(0) {
            corrupted!()
        }

        // Otherwise, start a new compaction.

        // Find a level...
        let lv = (0..LEVEL_COUNT)
            // ... that we can compact (level above is not full)
            .filter(|&lv| lv == 0 || !self.is_level_full(lv - 1))
            // ... and that is the fullest.
            // In case of a tie, pick the lowest level (max_by_key picks the latest element on ties)
            .max_by_key(|&lv| self.level_file_count(lv))
            // unwrap is OK because we'll always have at least level 0.
            .unwrap();

        // destination file
        let dst = if lv == 0 {
            0
        } else {
            self.new_file_in_level(lv - 1).unwrap()
        };

        // source files
        let mut src = Vec::new();
        for i in 0..BRANCHING_FACTOR {
            let src_file = Self::file_id(lv, i);
            if !self.files.is_empty(src_file) {
                src.push(src_file).unwrap();
            }
        }

        if src.is_empty() || (src.len() == 1 && lv == 0) {
            // No compaction work to do.
            debug!("compact_find_work: no work.");
            return Ok(None);
        }

        debug!("compact_find_work: starting new compact.");
        Ok(Some((src, dst)))
    }

    async fn do_compact(&mut self, src: Vec<FileID, BRANCHING_FACTOR>, dst: FileID) -> Result<(), Error<F::Error>> {
        debug!("do_compact {:?} -> {}", &src[..], dst);

        assert!(!src.is_empty());

        if self.files.is_empty(dst) && src.len() == 1 {
            debug!("do_compact: short-circuit rename");
            let mut tx = self.files.transaction();
            tx.rename(src[0], dst).await?;
            tx.commit().await?;
            return Ok(());
        }

        let mut w = self.files.write(dst).await?;

        // Open all files in level for reading.
        let mut r: [MaybeUninit<FileReader>; BRANCHING_FACTOR] = unsafe { MaybeUninit::uninit().assume_init() };
        for (i, &file_id) in src.iter().enumerate() {
            r[i].write(self.files.read(file_id).await);
        }
        let r = unsafe { slice::from_raw_parts_mut(r.as_mut_ptr() as *mut FileReader, src.len()) };

        let m = &mut self.files;

        struct KeySlot {
            valid: bool,
            key: Vec<u8, MAX_KEY_SIZE>,
        }

        async fn read_key_slot<F: Flash>(
            m: &mut FileManager<F>,
            r: &mut FileReader,
            buf: &mut KeySlot,
        ) -> Result<(), Error<F::Error>> {
            match read_key(m, r, &mut buf.key).await {
                Ok(()) => {
                    buf.valid = true;
                    Ok(())
                }
                Err(PageReadError::Flash(e)) => Err(Error::Flash(e)),
                Err(PageReadError::Eof) => {
                    buf.valid = false;
                    Ok(())
                }
                Err(PageReadError::Corrupted) => corrupted!(),
            }
        }

        const NEW_SLOT: KeySlot = KeySlot {
            key: Vec::new(),
            valid: false,
        };
        let mut k = [NEW_SLOT; BRANCHING_FACTOR];
        let mut trunc = [0; BRANCHING_FACTOR];

        for i in 0..src.len() {
            read_key_slot(m, &mut r[i], &mut k[i]).await?;
        }

        let mut progress = false;
        let done = loop {
            fn highest_bit(x: u32) -> Option<usize> {
                match x {
                    0 => None,
                    _ => Some(31 - x.leading_zeros() as usize),
                }
            }

            let mut bits: u32 = 0;
            for i in 0..src.len() {
                // Ignore files that have already reached the end.
                if !k[i].valid {
                    continue;
                }

                match highest_bit(bits) {
                    // If we haven't found any nonempty key yet, take the current one.
                    None => bits = 1 << i,
                    Some(j) => match k[j].key.cmp(&k[i].key) {
                        Ordering::Greater => bits = 1 << i,
                        Ordering::Equal => bits |= 1 << i,
                        Ordering::Less => {}
                    },
                }
            }

            trace!("do_compact: bits {:02x}", bits);
            match highest_bit(bits) {
                // All keys empty, means we've finished
                None => break true,
                // Copy value from the highest bit (so newest file)
                Some(i) => {
                    let val_len = check_corrupted!(read_leb128(m, &mut r[i]).await);

                    let record_size = record_size(k[i].key.len(), val_len as usize);
                    let need_size = record_size + FREE_PAGE_BUFFER_COMMIT * PAGE_MAX_PAYLOAD_SIZE;
                    let available_size = w.space_left_on_current_page() + m.free_pages() * PAGE_MAX_PAYLOAD_SIZE;

                    trace!(
                        "do_compact: key_len={} val_len={} space_left={} free_pages={} size={} available_size={}",
                        k[i].key.len(),
                        val_len,
                        w.space_left_on_current_page(),
                        m.free_pages(),
                        need_size,
                        available_size
                    );

                    if need_size > available_size {
                        // it will not fit, so stop.
                        break false;
                    }

                    #[cfg(feature = "defmt")]
                    trace!("do_compact: copying key from file {:?}: {:02x}", src[i], &k[i].key[..]);
                    #[cfg(not(feature = "defmt"))]
                    trace!("do_compact: copying key from file {:?}: {:02x?}", src[i], &k[i].key[..]);

                    progress = true;

                    write_key(m, &mut w, &k[i].key).await?;
                    write_leb128(m, &mut w, val_len).await?;
                    copy(m, &mut r[i], &mut w, val_len as usize).await?;
                    w.record_end();

                    // Advance all readers
                    for j in 0..BRANCHING_FACTOR {
                        if (bits & 1 << j) != 0 {
                            if j != i {
                                check_corrupted!(skip_value(m, &mut r[j]).await);
                            }
                            trunc[j] = r[j].offset(m);
                            read_key_slot(m, &mut r[j], &mut k[j]).await?;
                        }
                    }
                }
            }
        };

        debug!("do_compact: stopped. done={:?} progress={:?}", done, progress);

        // We should've made some progress, as long as the free page margins were respected.
        // TODO maybe return corrupted error instead.
        assert!(progress);

        let (src_flag, dst_flag) = match done {
            true => (0, 0),
            false => (FILE_FLAG_COMPACT_SRC, FILE_FLAG_COMPACT_DEST),
        };

        let mut tx = self.files.transaction();
        for (i, &file_id) in src.iter().enumerate() {
            tx.set_flags(file_id, src_flag).await?;
            tx.truncate(file_id, trunc[i]).await?;
        }
        w.commit(&mut tx).await?;
        tx.set_flags(dst, dst_flag).await?;

        // special case: if compacting from level 0
        if dst == 0 && done {
            tx.rename(0, Self::file_id(0, 0)).await?;
        }

        tx.commit().await?;

        Ok(())
    }

    async fn compact(&mut self) -> Result<bool, Error<F::Error>> {
        let Some((src, dst)) = self.compact_find_work()? else{
            return Ok(false)
        };

        self.do_compact(src, dst).await?;
        Ok(true)
    }

    #[cfg(feature = "std")]
    pub async fn dump(&mut self) {
        for file_id in 0..FILE_COUNT {
            info!("====== FILE {} ======", file_id);
            if let Err(e) = self.dump_file(file_id as _).await {
                info!("failed to dump file: {:?}", e);
            }
        }
    }

    #[cfg(feature = "std")]
    pub async fn dump_file(&mut self, file_id: FileID) -> Result<(), Error<F::Error>> {
        self.files.dump_file(file_id).await?;

        let mut r = self.files.read(file_id).await;
        let mut key = Vec::new();
        let mut value = [0u8; 32 * 1024];
        loop {
            let seq = r.curr_seq(&mut self.files);
            match read_key(&mut self.files, &mut r, &mut key).await {
                Ok(()) => {}
                Err(PageReadError::Flash(e)) => return Err(Error::Flash(e)),
                Err(PageReadError::Eof) => break,
                Err(PageReadError::Corrupted) => corrupted!(),
            }
            let n = check_corrupted!(read_value(&mut self.files, &mut r, &mut value).await);
            let value = &value[..n];

            debug!(
                "record at seq={:?}: key={:02x?} value_len={} value={:02x?}",
                seq,
                key,
                value.len(),
                value
            );
        }

        Ok(())
    }
}

pub struct WriteTransactionInner {
    w: FileWriter,
    last_key: Option<Vec<u8, MAX_KEY_SIZE>>,
}

async fn write_record<F: Flash>(
    m: &mut FileManager<F>,
    w: &mut FileWriter,
    key: &[u8],
    value: &[u8],
) -> Result<(), Error<F::Error>> {
    write_key(m, w, key).await?;
    write_value(m, w, value).await?;
    Ok(())
}

async fn write_key<F: Flash>(m: &mut FileManager<F>, w: &mut FileWriter, key: &[u8]) -> Result<(), Error<F::Error>> {
    let key_len: u32 = key.len().try_into().unwrap();
    write_leb128(m, w, key_len).await?;
    w.write(m, key).await?;
    Ok(())
}

async fn write_value<F: Flash>(
    m: &mut FileManager<F>,
    w: &mut FileWriter,
    value: &[u8],
) -> Result<(), Error<F::Error>> {
    let value_len: u32 = value.len().try_into().unwrap();
    write_leb128(m, w, value_len).await?;
    w.write(m, value).await?;
    w.record_end();
    Ok(())
}

async fn copy<F: Flash>(
    m: &mut FileManager<F>,
    r: &mut FileReader,
    w: &mut FileWriter,
    mut len: usize,
) -> Result<(), Error<F::Error>> {
    let mut buf = [0; 128];
    while len != 0 {
        let n = len.min(buf.len());
        len -= n;

        check_corrupted!(r.read(m, &mut buf[..n]).await);
        w.write(m, &buf[..n]).await?;
    }
    Ok(())
}

async fn write_leb128<F: Flash>(
    m: &mut FileManager<F>,
    w: &mut FileWriter,
    mut val: u32,
) -> Result<(), Error<F::Error>> {
    loop {
        let mut part = val & 0x7F;
        let rest = val >> 7;
        if rest != 0 {
            part |= 0x80
        }

        w.write(m, &[part as u8]).await?;

        if rest == 0 {
            break;
        }
        val = rest
    }
    Ok(())
}

fn leb128_size(mut val: u32) -> usize {
    let mut size = 0;
    loop {
        let rest = val >> 7;

        size += 1;

        if rest == 0 {
            break;
        }
        val = rest
    }
    size
}

fn record_size(key_len: usize, val_len: usize) -> usize {
    leb128_size(key_len.try_into().unwrap()) + key_len + leb128_size(val_len.try_into().unwrap()) + val_len
}

async fn read_key<F: Flash>(
    m: &mut FileManager<F>,
    r: &mut FileReader,
    buf: &mut Vec<u8, MAX_KEY_SIZE>,
) -> Result<(), PageReadError<F::Error>> {
    let len = read_leb128(m, r).await? as usize;
    if len > MAX_KEY_SIZE {
        info!("key too long: {}", len);
        corrupted!();
    }
    unsafe { buf.set_len(len) };
    r.read(m, buf).await
}

async fn read_value<F: Flash>(
    m: &mut FileManager<F>,
    r: &mut FileReader,
    value: &mut [u8],
) -> Result<usize, ReadError<F::Error>> {
    let len = check_corrupted!(read_leb128(m, r).await) as usize;
    if len > value.len() {
        return Err(ReadError::BufferTooSmall);
    }
    r.read(m, &mut value[..len]).await?;
    Ok(len)
}

async fn skip_value<F: Flash>(m: &mut FileManager<F>, r: &mut FileReader) -> Result<(), PageReadError<F::Error>> {
    let len = read_leb128(m, r).await? as usize;
    r.skip(m, len).await?;
    Ok(())
}

async fn read_u8<F: Flash>(m: &mut FileManager<F>, r: &mut FileReader) -> Result<u8, PageReadError<F::Error>> {
    let mut buf = [0u8; 1];
    r.read(m, &mut buf).await?;
    Ok(buf[0])
}

async fn read_leb128<F: Flash>(m: &mut FileManager<F>, r: &mut FileReader) -> Result<u32, PageReadError<F::Error>> {
    let mut res = 0;
    let mut shift = 0;
    loop {
        let x = read_u8(m, r).await?;
        if shift >= 32 {
            corrupted!()
        }
        res |= (x as u32 & 0x7F) << shift;
        if x & 0x80 == 0 {
            break;
        }
        shift += 7;
    }
    Ok(res)
}

pub trait Single: Iterator {
    /// Get the single element from a single-element iterator.
    fn single(self) -> Result<Self::Item, SingleError>;
}

/// An error in the execution of [`Single::single`](trait.Single.html#tymethod.single).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub enum SingleError {
    /// Asked empty iterator for single element.
    NoElements,
    /// Asked iterator with multiple elements for single element.
    MultipleElements,
}

impl<I: Iterator> Single for I {
    fn single(mut self) -> Result<Self::Item, SingleError> {
        match self.next() {
            None => Err(SingleError::NoElements),
            Some(element) => match self.next() {
                None => Ok(element),
                Some(_) => Err(SingleError::MultipleElements),
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::flash::MemFlash;

    const FORMAT: Config = {
        let mut config = Config::default();
        config.format = FormatConfig::Format;
        config
    };
    const NO_FORMAT: Config = {
        let mut config = Config::default();
        config.format = FormatConfig::Never;
        config
    };

    #[test_log::test(tokio::test)]
    async fn test() {
        let mut f = MemFlash::new();
        let db = Database::new(&mut f, FORMAT).await.unwrap();

        let mut buf = [0u8; 1024];

        let mut wtx = db.write_transaction().await;
        wtx.write(b"bar", b"4321").await.unwrap();
        wtx.write(b"foo", b"1234").await.unwrap();
        wtx.commit().await.unwrap();

        let mut rtx = db.read_transaction().await;
        let n = rtx.read(b"foo", &mut buf).await.unwrap();
        assert_eq!(&buf[..n], b"1234");
        let n = rtx.read(b"bar", &mut buf).await.unwrap();
        assert_eq!(&buf[..n], b"4321");
        let n = rtx.read(b"baz", &mut buf).await.unwrap();
        assert_eq!(&buf[..n], b"");
        drop(rtx);

        let mut wtx = db.write_transaction().await;
        wtx.write(b"bar", b"8765").await.unwrap();
        wtx.write(b"baz", b"4242").await.unwrap();
        wtx.write(b"foo", b"5678").await.unwrap();
        wtx.commit().await.unwrap();

        let mut rtx = db.read_transaction().await;
        let n = rtx.read(b"foo", &mut buf).await.unwrap();
        assert_eq!(&buf[..n], b"5678");
        let n = rtx.read(b"bar", &mut buf).await.unwrap();
        assert_eq!(&buf[..n], b"8765");
        let n = rtx.read(b"baz", &mut buf).await.unwrap();
        assert_eq!(&buf[..n], b"4242");
        drop(rtx);

        let mut wtx = db.write_transaction().await;
        wtx.write(b"lol", b"9999").await.unwrap();
        wtx.commit().await.unwrap();

        let mut rtx = db.read_transaction().await;
        let n = rtx.read(b"foo", &mut buf).await.unwrap();
        assert_eq!(&buf[..n], b"5678");
        let n = rtx.read(b"bar", &mut buf).await.unwrap();
        assert_eq!(&buf[..n], b"8765");
        let n = rtx.read(b"baz", &mut buf).await.unwrap();
        assert_eq!(&buf[..n], b"4242");
        let n = rtx.read(b"lol", &mut buf).await.unwrap();
        assert_eq!(&buf[..n], b"9999");
        drop(rtx);
    }

    #[test_log::test(tokio::test)]
    async fn test_empty_key() {
        let mut f = MemFlash::new();
        let db = Database::new(&mut f, FORMAT).await.unwrap();

        let mut buf = [0u8; 1024];

        let mut wtx = db.write_transaction().await;
        wtx.write(b"", b"aaaa").await.unwrap();
        wtx.write(b"foo", b"4321").await.unwrap();
        wtx.commit().await.unwrap();

        let mut wtx = db.write_transaction().await;
        wtx.write(b"", b"bbbb").await.unwrap();
        wtx.write(b"foo", b"1234").await.unwrap();
        wtx.commit().await.unwrap();

        assert_eq!(db.inner.lock().await.compact().await.unwrap(), true);

        let mut rtx = db.read_transaction().await;
        let n = rtx.read(b"", &mut buf).await.unwrap();
        assert_eq!(&buf[..n], b"bbbb");
        let n = rtx.read(b"foo", &mut buf).await.unwrap();
        assert_eq!(&buf[..n], b"1234");
        let n = rtx.read(b"baz", &mut buf).await.unwrap();
        assert_eq!(&buf[..n], b"");
        drop(rtx);
    }

    #[test_log::test(tokio::test)]
    async fn test_buf_too_small() {
        let mut f = MemFlash::new();
        let db = Database::new(&mut f, FORMAT).await.unwrap();

        let mut wtx = db.write_transaction().await;
        wtx.write(b"foo", b"1234").await.unwrap();
        wtx.commit().await.unwrap();

        let mut rtx = db.read_transaction().await;
        let mut buf = [0u8; 1];
        let r = rtx.read(b"foo", &mut buf).await;
        assert!(matches!(r, Err(ReadError::BufferTooSmall)));
    }

    #[test_log::test(tokio::test)]
    async fn test_remount() {
        let mut f = MemFlash::new();
        let mut buf = [0u8; 1024];

        {
            let db = Database::new(&mut f, FORMAT).await.unwrap();

            let mut wtx = db.write_transaction().await;
            wtx.write(b"bar", b"4321").await.unwrap();
            wtx.write(b"foo", b"1234").await.unwrap();
            wtx.commit().await.unwrap();
        }

        {
            // remount
            let db = Database::new(&mut f, NO_FORMAT).await.unwrap();

            let mut rtx = db.read_transaction().await;
            let n = rtx.read(b"foo", &mut buf).await.unwrap();
            assert_eq!(&buf[..n], b"1234");
            let n = rtx.read(b"bar", &mut buf).await.unwrap();
            assert_eq!(&buf[..n], b"4321");
            let n = rtx.read(b"baz", &mut buf).await.unwrap();
            assert_eq!(&buf[..n], b"");
            drop(rtx);

            let mut wtx = db.write_transaction().await;
            wtx.write(b"bar", b"8765").await.unwrap();
            wtx.write(b"baz", b"4242").await.unwrap();
            wtx.write(b"foo", b"5678").await.unwrap();
            wtx.commit().await.unwrap();
        }

        {
            // remount
            let db = Database::new(&mut f, NO_FORMAT).await.unwrap();

            let mut rtx = db.read_transaction().await;
            let n = rtx.read(b"foo", &mut buf).await.unwrap();
            assert_eq!(&buf[..n], b"5678");
            let n = rtx.read(b"bar", &mut buf).await.unwrap();
            assert_eq!(&buf[..n], b"8765");
            let n = rtx.read(b"baz", &mut buf).await.unwrap();
            assert_eq!(&buf[..n], b"4242");
            drop(rtx);

            let mut wtx = db.write_transaction().await;
            wtx.write(b"lol", b"9999").await.unwrap();
            wtx.commit().await.unwrap();
        }

        {
            // remount
            let db = Database::new(&mut f, NO_FORMAT).await.unwrap();

            let mut rtx = db.read_transaction().await;
            let n = rtx.read(b"foo", &mut buf).await.unwrap();
            assert_eq!(&buf[..n], b"5678");
            let n = rtx.read(b"bar", &mut buf).await.unwrap();
            assert_eq!(&buf[..n], b"8765");
            let n = rtx.read(b"baz", &mut buf).await.unwrap();
            assert_eq!(&buf[..n], b"4242");
            let n = rtx.read(b"lol", &mut buf).await.unwrap();
            assert_eq!(&buf[..n], b"9999");
            drop(rtx);
        }
    }
}

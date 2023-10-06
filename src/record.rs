use core::cell::RefCell;
use core::cmp::Ordering;
use core::future::poll_fn;
use core::mem::MaybeUninit;
use core::ops::{Deref, DerefMut};
use core::slice;
use core::task::Poll;

use embassy_sync::blocking_mutex::raw::RawMutex;
use embassy_sync::blocking_mutex::Mutex as BlockingMutex;
use embassy_sync::mutex::Mutex;
use embassy_sync::waitqueue::WakerRegistration;
use heapless::Vec;

use crate::config::*;
use crate::errors::{CorruptedError, Error, MountError, ReadError, WriteError};
use crate::file::{FileID, FileManager, FileReader, FileSearcher, FileWriter, SeekDirection, PAGE_MAX_PAYLOAD_SIZE};
use crate::flash::Flash;
use crate::page::{PageReader, ReadError as PageReadError};
use crate::{CommitError, FormatError};

const FILE_FLAG_COMPACT_DEST: u8 = 0x01;
const FILE_FLAG_COMPACT_SRC: u8 = 0x02;

/// Run-time configuration.
#[derive(Debug, Clone, Eq, PartialEq)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
#[non_exhaustive]
pub struct Config {
    /// Random seed, used for wear leveling.
    ///
    /// This should be different every boot, and "random enough". It does not
    /// need to be cryptographically secure.
    pub random_seed: u32,
}

impl Default for Config {
    fn default() -> Self {
        Self::default()
    }
}

impl Config {
    const fn default() -> Self {
        Self { random_seed: 0 }
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

/// The main database struct.
pub struct Database<F: Flash, M: RawMutex> {
    state: BlockingMutex<M, RefCell<State>>,

    inner: Mutex<M, Inner<F>>,
}

impl<F: Flash, M: RawMutex> Database<F, M> {
    /// Create a new database.
    ///
    /// This does no flash operations, and always succeeds. Actually mounting the database
    /// is done lazily, when the first operation (read or write) is done.
    ///
    /// If the storage is not formatted, you have to call [`format`](Self::format) before first use.
    ///
    /// You can call [`mount`](Self::mount) to force eagerly mounting the database. This can be
    /// useful to detect whether the storage is formatted or not, so that you can format it if it isn't
    /// before first use.
    pub fn new(flash: F, config: Config) -> Self {
        Self {
            inner: Mutex::new(Inner::new(flash, config.random_seed)),
            state: BlockingMutex::new(RefCell::new(State {
                read_tx_count: 0,
                write_tx: WriteTxState::Idle,
                waker: WakerRegistration::new(),
            })),
        }
    }

    /// Get an exclusive lock for the underlying flash.
    ///
    /// This returns a "mutex guard"-like object that gives exclusive access to
    /// the flash. All other concurrent operations on the database will wait on
    /// this object to be dropped.
    ///
    /// Note that actually writing to the flash behind `ekv`'s back will result
    /// in corruption. This is intended for other tasks, for example
    /// reading the flash memory's serial number, or statistics.
    pub async fn lock_flash(&self) -> impl Deref<Target = F> + DerefMut + '_ {
        FlashLockGuard(self.inner.lock().await)
    }

    /// Format the database storage.
    ///
    /// This will format the underlying storage into an empty key-value database.
    /// If the storage was already formatted, all data will be lost.
    pub async fn format(&self) -> Result<(), FormatError<F::Error>> {
        self.inner.lock().await.format().await
    }

    /// Force eagerly mounting the database storage.
    ///
    /// You don't have to call this method, mounting is done lazily on first operation.
    ///
    /// Eagerly mounting can still be useful, to detect whether the storage is
    /// formatted or not, so that you can format it if it isn't before first use.
    pub async fn mount(&self) -> Result<(), MountError<F::Error>> {
        self.inner.lock().await.mount().await
    }

    /// Dump the on-disk database structures.
    ///
    /// Intended for debugging only.
    #[cfg(feature = "std")]
    pub async fn dump(&self) {
        self.inner.lock().await.dump().await
    }

    /// Open a read transaction.
    ///
    /// This will wait if there's a write transaction either being currently committed, or
    /// waiting to be committed because there are other read transactions open.
    ///
    /// Dropping the `ReadTransaction` closes the transaction. Make sure to drop it as soon
    /// as possible, to not delay write transaction commits.
    pub async fn read_transaction(&self) -> ReadTransaction<'_, F, M> {
        poll_fn(|cx| {
            self.state.lock(|s| {
                let s = &mut s.borrow_mut();

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
        })
        .await;

        ReadTransaction { db: self }
    }

    /// Open a write transaction.
    ///
    /// This will wait if there's another write transaction already open.
    ///
    /// To make all the writes permanent, call [`commit`](WriteTransaction::commit).
    /// Dropping the `WriteTransaction` without committing closes the transaction
    /// and discards all written data.
    pub async fn write_transaction(&self) -> WriteTransaction<'_, F, M> {
        poll_fn(|cx| {
            self.state.lock(|s| {
                let s = &mut s.borrow_mut();
                if s.write_tx != WriteTxState::Idle {
                    s.waker.register(cx.waker());
                    return Poll::Pending;
                }
                s.write_tx = WriteTxState::Created;
                Poll::Ready(())
            })
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

/// In-progress read transaction.
pub struct ReadTransaction<'a, F: Flash + 'a, M: RawMutex + 'a> {
    db: &'a Database<F, M>,
}

impl<'a, F: Flash + 'a, M: RawMutex + 'a> Drop for ReadTransaction<'a, F, M> {
    fn drop(&mut self) {
        self.db.state.lock(|s| {
            let s = &mut s.borrow_mut();

            // NOTE(unwrap): It's impossible that read_tx_count==0, because at least one
            // read transaction was in progress: the one we're dropping now.
            s.read_tx_count = s.read_tx_count.checked_sub(1).unwrap();
            if s.read_tx_count == 0 {
                s.waker.wake();
            }
        })
    }
}

impl<'a, F: Flash + 'a, M: RawMutex + 'a> ReadTransaction<'a, F, M> {
    /// Read a key from the database.
    ///
    /// The value is stored in the `value` buffer, and the length is returned.
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

/// In-progress write transaction.
///
/// ## Cancelation
///
/// If any operation within the transaction (`write` or `delete`) either fails, or is canceled (due
/// to dropping its `Future` before completion), the entire write transaction is canceled.
///
/// When the transaction is canceled, all operations will return `TransactionCanceled` errors.
/// To recover, you must drop the entire `WriteTransaction`, and (if desired) open a new one to retry
/// the writes.
pub struct WriteTransaction<'a, F: Flash + 'a, M: RawMutex + 'a> {
    db: &'a Database<F, M>,
    state: WriteTransactionState,
}

impl<'a, F: Flash + 'a, M: RawMutex + 'a> Drop for WriteTransaction<'a, F, M> {
    fn drop(&mut self) {
        self.db.state.lock(|s| {
            let s = &mut s.borrow_mut();

            assert!(s.write_tx != WriteTxState::Idle);
            s.write_tx = WriteTxState::Idle;
            s.waker.wake();
        })
    }
}

impl<'a, F: Flash + 'a, M: RawMutex + 'a> WriteTransaction<'a, F, M> {
    /// Write a key to the database.
    ///
    /// If the key was already present, the previous value is overwritten.
    pub async fn write(&mut self, key: &[u8], value: &[u8]) -> Result<(), WriteError<F::Error>> {
        self.write_inner(key, value, false).await
    }

    /// Delete a key from the database.
    ///
    /// If the key was not present, this is a no-op.
    pub async fn delete(&mut self, key: &[u8]) -> Result<(), WriteError<F::Error>> {
        self.write_inner(key, &[], true).await
    }

    async fn write_inner(&mut self, key: &[u8], value: &[u8], is_delete: bool) -> Result<(), WriteError<F::Error>> {
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
        let db = &mut *self.db.inner.lock().await;
        db.files.remount_if_dirty(&mut db.readers[0]).await?;

        if is_first_write {
            db.rollback_if_any().await?;
        }
        db.write(key, value, is_delete).await?;

        self.state = WriteTransactionState::InProgress;

        Ok(())
    }

    /// Commit the transaction.
    ///
    /// This will wait until no read transaction is open. While waiting, opening new read transactions
    /// is blocked, to prevent readers from starving writers.
    ///
    /// This makes all the writes permanent on the underlyling database. When it returns, the writes are
    /// guaranteed to be fully safely written to flash, so they can't get lost by a crash or a power failure anymore.
    ///
    /// Committing is atomic: if commit is interrupted (due to power loss, crash, or canceling the future), it is
    /// guaranteed that either all or none of the writes in the transaction are committed.
    pub async fn commit(self) -> Result<(), CommitError<F::Error>> {
        match self.state {
            WriteTransactionState::Canceled => return Err(CommitError::TransactionCanceled),
            WriteTransactionState::Created => return Ok(()),
            WriteTransactionState::InProgress => {}
        }

        // First switch to Committing, so that no new read txs can start.
        self.db.state.lock(|s| {
            let s = &mut s.borrow_mut();
            assert!(s.write_tx == WriteTxState::Created);
            s.write_tx = WriteTxState::Committing;
        });

        // Then wait for the existing read txs to finish.
        poll_fn(|cx| {
            self.db.state.lock(|s| {
                let s = &mut s.borrow_mut();
                if s.read_tx_count != 0 {
                    s.waker.register(cx.waker());
                    return Poll::Pending;
                }
                Poll::Ready(())
            })
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
    readers: [PageReader; BRANCHING_FACTOR],
    write_tx: Option<WriteTransactionInner>,
}

impl<F: Flash> Inner<F> {
    fn new(flash: F, random_seed: u32) -> Self {
        const NEW_PR: PageReader = PageReader::new();
        Self {
            files: FileManager::new(flash, random_seed),
            readers: [NEW_PR; BRANCHING_FACTOR],
            write_tx: None,
        }
    }

    async fn format(&mut self) -> Result<(), FormatError<F::Error>> {
        assert!(self.write_tx.is_none());
        self.files.format().await
    }

    async fn mount(&mut self) -> Result<(), MountError<F::Error>> {
        assert!(self.write_tx.is_none());
        self.files.remount_if_dirty(&mut self.readers[0]).await?;
        Ok(())
    }

    async fn read(&mut self, key: &[u8], value: &mut [u8]) -> Result<usize, ReadError<F::Error>> {
        self.files.remount_if_dirty(&mut self.readers[0]).await?;

        for file_id in (0..FILE_COUNT).rev() {
            trace!("read: checking file {}", file_id);
            if let Some(res) = self.read_in_file(file_id as _, key, value).await? {
                return Ok(res);
            }
        }
        Err(ReadError::KeyNotFound)
    }

    async fn read_in_file(
        &mut self,
        file_id: FileID,
        key: &[u8],
        value: &mut [u8],
    ) -> Result<Option<usize>, ReadError<F::Error>> {
        let r = self.files.read(&mut self.readers[0], file_id).await;
        let m = &mut self.files;
        let mut s = FileSearcher::new(r);

        let mut key_buf = [0u8; MAX_KEY_SIZE];

        // Binary search
        let mut ok = s.start(m).await?;
        while ok {
            let mut header = [0; RECORD_HEADER_SIZE];
            match s.reader().read(m, &mut header).await {
                Ok(()) => {}
                Err(PageReadError::Eof) => return Ok(None), // key not present.
                Err(e) => return Err(no_eof(e).into()),
            };
            let header = RecordHeader::decode(header)?;

            // Read key
            let got_key = &mut key_buf[..header.key_len];
            s.reader().read(m, got_key).await.map_err(no_eof)?;

            // Found?
            let dir = match got_key[..].cmp(key) {
                Ordering::Equal => {
                    if header.is_delete {
                        return Err(ReadError::KeyNotFound);
                    }
                    if header.value_len > value.len() {
                        return Err(ReadError::BufferTooSmall);
                    }
                    s.reader()
                        .read(m, &mut value[..header.value_len])
                        .await
                        .map_err(no_eof)?;
                    return Ok(Some(header.value_len));
                }
                Ordering::Less => SeekDirection::Right,
                Ordering::Greater => SeekDirection::Left,
            };

            // Not found, do a binary search step.
            ok = s.seek(m, dir).await?;
        }

        let r = s.reader();

        // Linear search
        loop {
            let mut header = [0; RECORD_HEADER_SIZE];
            match r.read(m, &mut header).await {
                Ok(()) => {}
                Err(PageReadError::Eof) => return Ok(None), // key not present.
                Err(e) => return Err(no_eof(e).into()),
            };
            let header = RecordHeader::decode(header)?;

            // Read key
            let got_key = &mut key_buf[..header.key_len];
            r.read(m, got_key).await.map_err(no_eof)?;

            // Found?
            match got_key[..].cmp(key) {
                Ordering::Equal => {
                    if header.is_delete {
                        return Err(ReadError::KeyNotFound);
                    }
                    if header.value_len > value.len() {
                        return Err(ReadError::BufferTooSmall);
                    }
                    r.read(m, &mut value[..header.value_len]).await.map_err(no_eof)?;
                    return Ok(Some(header.value_len));
                }
                Ordering::Less => {}                  // keep going
                Ordering::Greater => return Ok(None), // not present.
            }

            r.skip(m, header.value_len).await.map_err(no_eof)?;
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
        let w = self.files.write(&mut self.readers[0], file_id).await?;

        self.write_tx = Some(WriteTransactionInner { w, last_key: None });

        Ok(())
    }

    async fn write(&mut self, key: &[u8], value: &[u8], is_delete: bool) -> Result<(), WriteError<F::Error>> {
        self.ensure_write_transaction_started().await?;
        let tx = self.write_tx.as_mut().unwrap();

        if let Some(last_key) = &tx.last_key {
            if key <= last_key {
                return Err(WriteError::NotSorted);
            }
        }
        tx.last_key = Some(Vec::from_slice(key).unwrap());

        let header = RecordHeader {
            is_delete,
            key_len: key.len(),
            value_len: value.len(),
        };

        loop {
            let tx = self.write_tx.as_mut().unwrap();

            let need_size = header.record_size() + MIN_FREE_PAGE_COUNT * PAGE_MAX_PAYLOAD_SIZE;
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

        tx.w.write(&mut self.files, &header.encode()).await?;
        tx.w.write(&mut self.files, key).await?;
        tx.w.write(&mut self.files, value).await?;
        tx.w.record_end();

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

        let tx = self.write_tx.as_mut().unwrap();
        tx.w.discard(&mut self.files).await.unwrap();

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
                if src.is_empty() {
                    corrupted!()
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
            match self.new_file_in_level(lv - 1) {
                Some(dst) => dst,
                // This can happen if the level is not full, but the only free slots
                // are "in the middle". This shouldn't happen in normal operation,
                // it signals corruption.
                None => corrupted!(),
            }
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

        let topmost = dst == 0;

        assert!(!src.is_empty());

        if self.files.is_empty(dst) && src.len() == 1 {
            debug!("do_compact: short-circuit rename");
            let mut tx = self.files.transaction();
            tx.rename(src[0], dst).await?;
            tx.commit().await?;
            return Ok(());
        }

        let mut w = self.files.write(&mut self.readers[0], dst).await?;

        // Open all files in level for reading.
        // TODO: maybe use a bit less unsafe?
        let mut r: [MaybeUninit<FileReader>; BRANCHING_FACTOR] = unsafe { MaybeUninit::uninit().assume_init() };
        let readers_ptr = self.readers.as_mut_ptr();
        for (i, &file_id) in src.iter().enumerate() {
            r[i].write(self.files.read(unsafe { &mut *readers_ptr.add(i) }, file_id).await);
        }
        let r = unsafe { slice::from_raw_parts_mut(r.as_mut_ptr() as *mut FileReader, src.len()) };

        let m = &mut self.files;

        struct KeySlot {
            valid: bool,
            header: RecordHeader,
            key_buf: [u8; MAX_KEY_SIZE],
        }

        impl KeySlot {
            fn key(&self) -> &[u8] {
                &self.key_buf[..self.header.key_len]
            }
        }

        async fn read_key_slot<F: Flash>(
            m: &mut FileManager<F>,
            r: &mut FileReader<'_>,
            buf: &mut KeySlot,
        ) -> Result<(), Error<F::Error>> {
            let mut header = [0; RECORD_HEADER_SIZE];
            match r.read(m, &mut header).await {
                Ok(()) => {}
                Err(PageReadError::Flash(e)) => return Err(Error::Flash(e)),
                Err(PageReadError::Eof) => {
                    buf.valid = false;
                    return Ok(());
                }
                Err(PageReadError::Corrupted) => corrupted!(),
            }

            buf.valid = true;
            buf.header = RecordHeader::decode(header)?;

            // Read key
            match r.read(m, &mut buf.key_buf[..buf.header.key_len]).await {
                Ok(()) => Ok(()),
                Err(PageReadError::Flash(e)) => Err(Error::Flash(e)),
                Err(PageReadError::Eof) => corrupted!(),
                Err(PageReadError::Corrupted) => corrupted!(),
            }
        }

        const NEW_SLOT: KeySlot = KeySlot {
            valid: false,
            header: RecordHeader {
                key_len: 0,
                value_len: 0,
                is_delete: false,
            },
            key_buf: [0; MAX_KEY_SIZE],
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
                    Some(j) => match k[j].key().cmp(k[i].key()) {
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
                    let need_size = k[i].header.record_size() + MIN_FREE_PAGE_COUNT_COMPACT * PAGE_MAX_PAYLOAD_SIZE;
                    let available_size = w.space_left_on_current_page() + m.free_pages() * PAGE_MAX_PAYLOAD_SIZE;

                    trace!(
                        "do_compact: key_len={} val_len={} space_left={} free_pages={} size={} available_size={}",
                        k[i].header.key_len,
                        k[i].header.value_len,
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
                    trace!("do_compact: copying key from file {:?}: {:02x}", src[i], &k[i].key());
                    #[cfg(not(feature = "defmt"))]
                    trace!("do_compact: copying key from file {:?}: {:02x?}", src[i], &k[i].key());

                    progress = true;

                    // if we're compacting to the topmost level, do not write tombstone records
                    if topmost && k[i].header.is_delete {
                        trace!("do_compact: skipping tombstone.");
                    } else {
                        w.write(m, &k[i].header.encode()).await?;
                        w.write(m, k[i].key()).await?;
                        copy(m, &mut r[i], &mut w, k[i].header.value_len).await?;
                        w.record_end();
                    }

                    // Advance all readers
                    for j in 0..BRANCHING_FACTOR {
                        if (bits & 1 << j) != 0 {
                            if j != i {
                                r[j].skip(m, k[j].header.value_len).await.map_err(no_eof)?;
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
        if !progress {
            return Err(Error::Corrupted);
        }

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
        if topmost && done {
            tx.rename(0, Self::file_id(0, 0)).await?;
        }

        tx.commit().await?;

        Ok(())
    }

    async fn compact(&mut self) -> Result<bool, Error<F::Error>> {
        let Some((src, dst)) = self.compact_find_work()? else {
            return Ok(false);
        };

        self.do_compact(src, dst).await?;
        Ok(true)
    }

    #[cfg(feature = "std")]
    pub async fn dump(&mut self) {
        if let Err(e) = self.files.remount_if_dirty(&mut self.readers[0]).await {
            info!("db is dirty, and remount failed: {:?}", e);
            return;
        }

        for file_id in 0..FILE_COUNT {
            info!("====== FILE {} ======", file_id);
            if let Err(e) = self.dump_file(file_id as _).await {
                info!("failed to dump file: {:?}", e);
            }
        }
    }

    #[cfg(feature = "std")]
    pub async fn dump_file(&mut self, file_id: FileID) -> Result<(), Error<F::Error>> {
        self.files.dump_file(&mut self.readers[0], file_id).await?;

        let mut r = self.files.read(&mut self.readers[0], file_id).await;
        let mut key = [0u8; MAX_KEY_SIZE];
        let mut value = [0u8; MAX_VALUE_SIZE];
        loop {
            let seq = r.curr_seq(&mut self.files);

            let mut header = [0; RECORD_HEADER_SIZE];
            match r.read(&mut self.files, &mut header).await {
                Ok(()) => {}
                Err(PageReadError::Flash(e)) => return Err(Error::Flash(e)),
                Err(PageReadError::Eof) => break,
                Err(PageReadError::Corrupted) => corrupted!(),
            };
            let header = RecordHeader::decode(header)?;

            // Read key
            let key = &mut key[..header.key_len];
            r.read(&mut self.files, key).await.map_err(no_eof)?;

            // read value
            let value = &mut value[..header.value_len];
            r.read(&mut self.files, value).await.map_err(no_eof)?;

            debug!(
                "record at seq={:?}: key_len={} key={:02x?} value_len={} value={:02x?}",
                seq,
                key.len(),
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

async fn copy<F: Flash>(
    m: &mut FileManager<F>,
    r: &mut FileReader<'_>,
    w: &mut FileWriter,
    mut len: usize,
) -> Result<(), Error<F::Error>> {
    let mut buf = [0; 128];
    while len != 0 {
        let n = len.min(buf.len());
        len -= n;

        r.read(m, &mut buf[..n]).await.map_err(no_eof)?;
        w.write(m, &buf[..n]).await?;
    }
    Ok(())
}

#[derive(Debug, Copy, Clone)]
pub(crate) struct RecordHeader {
    pub key_len: usize,
    pub value_len: usize,
    pub is_delete: bool,
}

impl RecordHeader {
    pub fn decode(raw: [u8; RECORD_HEADER_SIZE]) -> Result<Self, CorruptedError> {
        let mut raw2 = [0u8; 4];
        raw2[..RECORD_HEADER_SIZE].copy_from_slice(&raw);
        let raw = u32::from_le_bytes(raw2);
        let key_len = raw & ((1 << KEY_SIZE_BITS) - 1);
        let value_len = (raw >> KEY_SIZE_BITS) & ((1 << VALUE_SIZE_BITS) - 1);
        let is_delete = (raw >> (KEY_SIZE_BITS + VALUE_SIZE_BITS)) & 1 != 0;
        let this = Self {
            is_delete,
            key_len: key_len as usize,
            value_len: value_len as usize,
        };

        if !this.valid() {
            corrupted!();
        }

        Ok(this)
    }

    pub fn encode(self) -> [u8; RECORD_HEADER_SIZE] {
        assert!(self.valid());

        let res = (self.key_len as u32)
            | ((self.value_len as u32) << KEY_SIZE_BITS)
            | ((self.is_delete as u32) << (KEY_SIZE_BITS + VALUE_SIZE_BITS));
        res.to_le_bytes()[..RECORD_HEADER_SIZE].try_into().unwrap()
    }

    pub const fn record_size(self) -> usize {
        4 + self.key_len + self.value_len
    }

    fn valid(self) -> bool {
        self.key_len <= MAX_KEY_SIZE && self.value_len <= MAX_VALUE_SIZE && !(self.is_delete && self.value_len != 0)
    }
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

fn no_eof<T>(e: PageReadError<T>) -> Error<T> {
    match e {
        PageReadError::Corrupted => Error::Corrupted,
        #[cfg(not(feature = "_panic-on-corrupted"))]
        PageReadError::Eof => Error::Corrupted,
        #[cfg(feature = "_panic-on-corrupted")]
        PageReadError::Eof => panic!("corrupted"),
        PageReadError::Flash(x) => Error::Flash(x),
    }
}

#[cfg(test)]
mod tests {
    use core::cell::Cell;
    use core::future::Future;
    use core::pin::Pin;
    use core::ptr;
    use core::task::{Context, RawWaker, RawWakerVTable, Waker};

    use embassy_sync::blocking_mutex::raw::NoopRawMutex;
    use tokio::task::yield_now;

    use super::*;
    use crate::flash::MemFlash;

    async fn check_read(db: &Database<impl Flash, NoopRawMutex>, key: &[u8], value: &[u8]) {
        let mut rtx = db.read_transaction().await;
        let mut buf = [0; 1024];
        let n = rtx.read(key, &mut buf).await.unwrap();
        assert_eq!(&buf[..n], value);
    }

    async fn check_not_found<F: Flash>(db: &Database<F, NoopRawMutex>, key: &[u8])
    where
        F::Error: PartialEq,
    {
        let mut rtx = db.read_transaction().await;
        assert_eq!(rtx.read(key, &mut []).await, Err(ReadError::KeyNotFound));
    }

    async fn compact(db: &Database<impl Flash, NoopRawMutex>) -> bool {
        let mut work = false;
        while db.inner.lock().await.compact().await.unwrap() {
            work = true
        }
        work
    }

    #[test_log::test(tokio::test)]
    async fn test() {
        let mut f = MemFlash::new();
        let db = Database::new(&mut f, Config::default());
        db.format().await.unwrap();

        let mut wtx = db.write_transaction().await;
        wtx.write(b"bar", b"4321").await.unwrap();
        wtx.write(b"foo", b"1234").await.unwrap();
        wtx.commit().await.unwrap();

        check_read(&db, b"foo", b"1234").await;
        check_read(&db, b"bar", b"4321").await;
        check_not_found(&db, b"baz").await;

        let mut wtx = db.write_transaction().await;
        wtx.write(b"bar", b"8765").await.unwrap();
        wtx.write(b"baz", b"4242").await.unwrap();
        wtx.write(b"foo", b"5678").await.unwrap();
        wtx.commit().await.unwrap();

        check_read(&db, b"foo", b"5678").await;
        check_read(&db, b"bar", b"8765").await;
        check_read(&db, b"baz", b"4242").await;

        let mut wtx = db.write_transaction().await;
        wtx.write(b"lol", b"9999").await.unwrap();
        wtx.commit().await.unwrap();

        check_read(&db, b"foo", b"5678").await;
        check_read(&db, b"bar", b"8765").await;
        check_read(&db, b"baz", b"4242").await;
        check_read(&db, b"lol", b"9999").await;
    }

    #[test_log::test(tokio::test)]
    async fn test_empty_key() {
        let mut f = MemFlash::new();
        let db = Database::new(&mut f, Config::default());
        db.format().await.unwrap();

        let mut wtx = db.write_transaction().await;
        wtx.write(b"", b"aaaa").await.unwrap();
        wtx.write(b"foo", b"4321").await.unwrap();
        wtx.commit().await.unwrap();

        let mut wtx = db.write_transaction().await;
        wtx.write(b"", b"bbbb").await.unwrap();
        wtx.write(b"foo", b"1234").await.unwrap();
        wtx.commit().await.unwrap();

        // force compact, to check it handles empty key fine.
        compact(&db).await;

        check_read(&db, b"", b"bbbb").await;
        check_read(&db, b"foo", b"1234").await;
        check_not_found(&db, b"baz").await;
    }

    #[test_log::test(tokio::test)]
    async fn test_empty_value() {
        let mut f = MemFlash::new();
        let db = Database::new(&mut f, Config::default());
        db.format().await.unwrap();

        let mut wtx = db.write_transaction().await;
        wtx.write(b"", b"aaaa").await.unwrap();
        wtx.write(b"bar", b"barbar").await.unwrap();
        wtx.write(b"foo", b"").await.unwrap();
        wtx.commit().await.unwrap();

        let mut wtx = db.write_transaction().await;
        wtx.write(b"", b"").await.unwrap();
        wtx.write(b"baz", b"").await.unwrap();
        wtx.commit().await.unwrap();

        // force compact, to check it handles empty values fine.
        compact(&db).await;

        check_read(&db, b"", b"").await;
        check_read(&db, b"foo", b"").await;
        check_read(&db, b"bar", b"barbar").await;
        check_read(&db, b"baz", b"").await;
        check_not_found(&db, b"lol").await;
    }

    #[test_log::test(tokio::test)]
    async fn test_delete() {
        let mut f = MemFlash::new();
        let db = Database::new(&mut f, Config::default());
        db.format().await.unwrap();

        let mut wtx = db.write_transaction().await;
        wtx.write(b"", b"").await.unwrap();
        wtx.commit().await.unwrap();

        check_read(&db, b"", b"").await;

        let mut wtx = db.write_transaction().await;
        wtx.delete(b"").await.unwrap();
        wtx.commit().await.unwrap();

        check_not_found(&db, b"").await;

        compact(&db).await;

        check_not_found(&db, b"").await;
    }

    #[test_log::test(tokio::test)]
    async fn test_transaction() {
        let mut f = MemFlash::new();
        let db = Database::new(&mut f, Config::default());
        db.format().await.unwrap();

        check_not_found(&db, b"foo").await;
        check_not_found(&db, b"bar").await;

        let mut wtx = db.write_transaction().await;

        wtx.write(b"bar", b"1234").await.unwrap();
        check_not_found(&db, b"foo").await;
        check_not_found(&db, b"bar").await;

        wtx.write(b"foo", b"4321").await.unwrap();
        check_not_found(&db, b"foo").await;
        check_not_found(&db, b"bar").await;

        wtx.commit().await.unwrap();

        check_read(&db, b"foo", b"4321").await;
        check_read(&db, b"bar", b"1234").await;
    }

    #[test_log::test(tokio::test)]
    async fn test_transaction_drop() {
        let mut f = MemFlash::new();
        let db = Database::new(&mut f, Config::default());
        db.format().await.unwrap();

        let mut wtx = db.write_transaction().await;
        wtx.write(b"foo", b"4321").await.unwrap();
        drop(wtx);

        check_not_found(&db, b"foo").await;

        let mut wtx = db.write_transaction().await;
        wtx.write(b"bar", b"4321").await.unwrap();
        wtx.commit().await.unwrap();

        check_not_found(&db, b"foo").await;
        check_read(&db, b"bar", b"4321").await;
    }

    #[test_log::test(tokio::test)]
    async fn test_transaction_locking() {
        let mut f = MemFlash::new();
        let db = Database::<_, NoopRawMutex>::new(&mut f, Config::default());
        db.format().await.unwrap();

        static VTABLE: RawWakerVTable =
            RawWakerVTable::new(|_| RawWaker::new(ptr::null(), &VTABLE), |_| {}, |_| {}, |_| {});
        let raw_waker = RawWaker::new(ptr::null(), &VTABLE);
        let waker = unsafe { Waker::from_raw(raw_waker) };
        let cx = &mut Context::from_waker(&waker);

        let read_state = Cell::new(0);
        let mut read_fut = async {
            read_state.set(1);
            let mut rtx = db.read_transaction().await;

            read_state.set(2);
            yield_now().await;

            let mut buf = [0; 128];
            let _ = rtx.read(b"foo", &mut buf).await;

            read_state.set(3);
            drop(rtx);

            read_state.set(4);
        };

        let write_state = Cell::new(0);
        let mut write_fut = async {
            write_state.set(1);
            let mut wtx = db.write_transaction().await;

            write_state.set(2);
            wtx.write(b"foo", b"lol").await.unwrap();

            write_state.set(3);
            wtx.commit().await.unwrap();

            write_state.set(4);
        };

        let mut read_fut = unsafe { Pin::new_unchecked(&mut read_fut) };
        let mut write_fut = unsafe { Pin::new_unchecked(&mut write_fut) };

        // Start read tx
        assert_eq!(read_fut.as_mut().poll(cx), Poll::Pending);
        assert_eq!(read_state.get(), 2);

        // Start write tx. Commit should wait for the rtx to end.
        assert_eq!(write_fut.as_mut().poll(cx), Poll::Pending);
        assert_eq!(write_state.get(), 3);

        // Still shouldn't move.
        assert_eq!(write_fut.as_mut().poll(cx), Poll::Pending);
        assert_eq!(write_state.get(), 3);

        // End read tx
        assert_eq!(read_fut.as_mut().poll(cx), Poll::Ready(()));
        assert_eq!(read_state.get(), 4);

        assert_eq!(write_fut.as_mut().poll(cx), Poll::Ready(()));
        assert_eq!(write_state.get(), 4);
    }

    #[test_log::test(tokio::test)]
    async fn test_transaction_locking_queue() {
        let mut f = MemFlash::new();
        let db = Database::<_, NoopRawMutex>::new(&mut f, Config::default());
        db.format().await.unwrap();

        static VTABLE: RawWakerVTable =
            RawWakerVTable::new(|_| RawWaker::new(ptr::null(), &VTABLE), |_| {}, |_| {}, |_| {});
        let raw_waker = RawWaker::new(ptr::null(), &VTABLE);
        let waker = unsafe { Waker::from_raw(raw_waker) };
        let cx = &mut Context::from_waker(&waker);

        let read_state = Cell::new(0);
        let mut read_fut = async {
            read_state.set(1);
            let mut rtx = db.read_transaction().await;

            read_state.set(2);
            yield_now().await;

            let mut buf = [0; 128];
            let _ = rtx.read(b"foo", &mut buf).await;

            read_state.set(3);
            drop(rtx);

            read_state.set(4);
        };

        let read2_state = Cell::new(0);
        let mut read2_fut = async {
            read2_state.set(1);
            let mut rtx = db.read_transaction().await;

            read2_state.set(2);

            let mut buf = [0; 128];
            let _ = rtx.read(b"foo", &mut buf).await;

            read2_state.set(3);
            drop(rtx);

            read2_state.set(4);
        };

        let write_state = Cell::new(0);
        let mut write_fut = async {
            write_state.set(1);
            let mut wtx = db.write_transaction().await;

            write_state.set(2);
            wtx.write(b"foo", b"lol").await.unwrap();

            write_state.set(3);
            wtx.commit().await.unwrap();

            write_state.set(4);
        };

        let mut read_fut = unsafe { Pin::new_unchecked(&mut read_fut) };
        let mut read2_fut = unsafe { Pin::new_unchecked(&mut read2_fut) };
        let mut write_fut = unsafe { Pin::new_unchecked(&mut write_fut) };

        // Start read tx
        assert_eq!(read_fut.as_mut().poll(cx), Poll::Pending);
        assert_eq!(read_state.get(), 2);

        // Start write tx. Commit should wait for the rtx to end.
        assert_eq!(write_fut.as_mut().poll(cx), Poll::Pending);
        assert_eq!(write_state.get(), 3);

        // Try to start the other read tx. Because commit is waiting, it should wait.
        assert_eq!(read2_fut.as_mut().poll(cx), Poll::Pending);
        assert_eq!(read2_state.get(), 1);

        // Still shouldn't move.
        assert_eq!(write_fut.as_mut().poll(cx), Poll::Pending);
        assert_eq!(write_state.get(), 3);
        assert_eq!(read2_fut.as_mut().poll(cx), Poll::Pending);
        assert_eq!(read2_state.get(), 1);

        // End read tx
        assert_eq!(read_fut.as_mut().poll(cx), Poll::Ready(()));
        assert_eq!(read_state.get(), 4);

        // The read2 tx shouldn't start because we haven't polled the write tx yet.
        assert_eq!(read2_fut.as_mut().poll(cx), Poll::Pending);
        assert_eq!(read2_state.get(), 1);

        // poll the write tx, it commits.
        assert_eq!(write_fut.as_mut().poll(cx), Poll::Ready(()));
        assert_eq!(write_state.get(), 4);

        // then the other read tx can go through now.
        assert_eq!(read2_fut.as_mut().poll(cx), Poll::Ready(()));
        assert_eq!(read2_state.get(), 4);
    }

    #[test_log::test(tokio::test)]
    async fn test_free_pages_on_transaction_drop() {
        let mut f = MemFlash::new();
        let db = Database::<_, NoopRawMutex>::new(&mut f, Config::default());
        db.format().await.unwrap();

        let prev_free = db.inner.lock().await.files.free_pages();

        let mut wtx = db.write_transaction().await;
        wtx.write(b"foo", b"4321").await.unwrap();
        drop(wtx);

        // rollback is lazy, force it.
        db.inner.lock().await.rollback().await.unwrap();

        let now_free = db.inner.lock().await.files.free_pages();

        assert_eq!(prev_free, now_free);
    }

    #[test_log::test(tokio::test)]
    async fn test_buf_too_small() {
        let mut f = MemFlash::new();
        let db = Database::<_, NoopRawMutex>::new(&mut f, Config::default());
        db.format().await.unwrap();

        let mut wtx = db.write_transaction().await;
        wtx.write(b"foo", b"1234").await.unwrap();
        wtx.commit().await.unwrap();

        let mut rtx = db.read_transaction().await;
        let mut buf = [0u8; 1];
        let r = rtx.read(b"foo", &mut buf).await;
        assert!(matches!(r, Err(ReadError::BufferTooSmall)));
    }

    #[test_log::test(tokio::test)]
    async fn test_unformatted_read() {
        let mut f = MemFlash::new();

        let db = Database::<_, NoopRawMutex>::new(&mut f, Config::default());

        let mut rtx = db.read_transaction().await;
        let mut buf = [0u8; 1];
        let r = rtx.read(b"foo", &mut buf).await;
        assert!(matches!(r, Err(ReadError::Corrupted)));
    }

    #[test_log::test(tokio::test)]
    async fn test_unformatted_write() {
        let mut f = MemFlash::new();

        let db = Database::<_, NoopRawMutex>::new(&mut f, Config::default());

        let mut wtx = db.write_transaction().await;
        assert_eq!(wtx.write(b"bar", b"4321").await, Err(WriteError::Corrupted));
    }

    #[test_log::test(tokio::test)]
    async fn test_remount() {
        let mut f = MemFlash::new();

        {
            let db = Database::<_, NoopRawMutex>::new(&mut f, Config::default());
            db.format().await.unwrap();

            let mut wtx = db.write_transaction().await;
            wtx.write(b"bar", b"4321").await.unwrap();
            wtx.write(b"foo", b"1234").await.unwrap();
            wtx.commit().await.unwrap();
        }

        {
            // remount
            let db = Database::new(&mut f, Config::default());

            check_read(&db, b"foo", b"1234").await;
            check_read(&db, b"bar", b"4321").await;
            check_not_found(&db, b"baz").await;

            let mut wtx = db.write_transaction().await;
            wtx.write(b"bar", b"8765").await.unwrap();
            wtx.write(b"baz", b"4242").await.unwrap();
            wtx.write(b"foo", b"5678").await.unwrap();
            wtx.commit().await.unwrap();
        }

        {
            // remount
            let db = Database::new(&mut f, Config::default());

            check_read(&db, b"foo", b"5678").await;
            check_read(&db, b"bar", b"8765").await;
            check_read(&db, b"baz", b"4242").await;

            let mut wtx = db.write_transaction().await;
            wtx.write(b"lol", b"9999").await.unwrap();
            wtx.commit().await.unwrap();
        }

        {
            // remount
            let db = Database::new(&mut f, Config::default());

            check_read(&db, b"foo", b"5678").await;
            check_read(&db, b"bar", b"8765").await;
            check_read(&db, b"baz", b"4242").await;
            check_read(&db, b"lol", b"9999").await;
        }
    }

    #[test_log::test(tokio::test)]
    async fn test_compact() {
        let mut f = MemFlash::new();
        let db = Database::<_, NoopRawMutex>::new(&mut f, Config::default());
        db.format().await.unwrap();

        // Write the key
        let mut wtx = db.write_transaction().await;
        wtx.write(b"foo", b"4321").await.unwrap();
        wtx.commit().await.unwrap();

        // force compact all the way.
        compact(&db).await;

        // Then erase it.
        let mut wtx = db.write_transaction().await;
        wtx.write(b"bar", b"6666").await.unwrap();
        wtx.write(b"foo", b"5555").await.unwrap();
        wtx.commit().await.unwrap();

        // force compact all the way.
        compact(&db).await;

        check_read(&db, b"foo", b"5555").await;
        check_read(&db, b"bar", b"6666").await;
    }

    #[test_log::test(tokio::test)]
    async fn test_compact_removes_tombstones() {
        let mut f = MemFlash::new();
        let db = Database::<_, NoopRawMutex>::new(&mut f, Config::default());
        db.format().await.unwrap();

        // Write the key
        let mut wtx = db.write_transaction().await;
        wtx.write(b"foo", b"4321").await.unwrap();
        wtx.commit().await.unwrap();

        // force compact all the way.
        compact(&db).await;

        // Then erase it.
        let mut wtx = db.write_transaction().await;
        wtx.delete(b"foo").await.unwrap();
        wtx.commit().await.unwrap();

        // force compact all the way.
        compact(&db).await;

        let dbi = db.inner.lock().await;
        assert!((0..FILE_COUNT).all(|i| dbi.files.is_empty(i as _)));
    }

    #[test_log::test(tokio::test)]
    async fn test_write_not_sorted() {
        let mut f = MemFlash::new();
        let db = Database::<_, NoopRawMutex>::new(&mut f, Config::default());
        db.format().await.unwrap();

        // Write the key
        let mut wtx = db.write_transaction().await;
        wtx.write(b"foo", b"4321").await.unwrap();
        assert_eq!(wtx.write(b"bar", b"4321").await, Err(WriteError::NotSorted));
    }
}

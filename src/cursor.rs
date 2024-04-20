use core::cmp::Ordering;

use embassy_sync::blocking_mutex::raw::RawMutex;
use heapless::Vec;

use crate::config::{FILE_COUNT, MAX_KEY_SIZE, RECORD_HEADER_SIZE};
use crate::errors::{no_eof, CursorError, Error};
use crate::file::{DehydratedFileReader, FileID, FileSearcher, SeekDirection};
use crate::flash::Flash;
use crate::page::ReadError as PageReadError;
use crate::record::{Inner, RecordHeader};
use crate::Database;

/// Upper or lower bound for a range read.
pub struct Bound<'a> {
    /// Key.
    pub key: &'a [u8],
    /// Whether the bound includes entries with key equal to `self.key`.
    ///
    /// If false, only entries with strictly greater keys (for `lower_bound`) or
    /// strictly smaller keys (for `upper_bound`) will be returned.
    ///
    /// If true, equal keys will also be returned.
    pub allow_equal: bool,
}

/// Cursor for a range read.
///
/// Returned by [`ReadTransaction::read_all()`](crate::ReadTransaction::read_all) and [`ReadTransaction::read_range()`](crate::ReadTransaction::read_range).
pub struct Cursor<'a, F: Flash + 'a, M: RawMutex + 'a> {
    db: &'a Database<F, M>,
    upper_bound: Option<Bound<'a>>,
    readers: [Option<DehydratedFileReader>; FILE_COUNT],
}

impl<'a, F: Flash + 'a, M: RawMutex + 'a> Cursor<'a, F, M> {
    pub(crate) async fn new(
        db: &'a Database<F, M>,
        lower_bound: Option<Bound<'_>>,
        upper_bound: Option<Bound<'a>>,
    ) -> Result<Self, Error<F::Error>> {
        let inner = &mut *db.inner.lock().await;
        inner.files.remount_if_dirty(&mut inner.readers[0]).await?;

        // Open and seek each file to the first key matching lower_bound.
        let mut readers: Vec<Option<DehydratedFileReader>, FILE_COUNT> = Vec::new();
        for i in 0..FILE_COUNT {
            let file_id = i as FileID;
            let r = if let Some(bound) = &lower_bound {
                inner.search_lower_bound_file(file_id, bound).await?
            } else {
                Some(inner.files.read(&mut inner.readers[0], file_id).dehydrate())
            };
            let _ = readers.push(r);
        }
        let Ok(readers) = readers.into_array() else {
            unreachable!()
        };

        Ok(Self {
            db,
            upper_bound,
            readers,
        })
    }

    /// Get the next key/value entry.
    ///
    /// If the cursor has not reached the end, the next entry in lexicographically ascending order is read into the start of the `key` and `value` buffers.
    /// The respective lengths are returned: `Ok(Some((key_len, value_len)))`.
    ///
    /// If the cursor has reached the end of the iteration, `Ok(None)` is returned.
    pub async fn next(
        &mut self,
        key: &mut [u8],
        value: &mut [u8],
    ) -> Result<Option<(usize, usize)>, CursorError<F::Error>> {
        let inner = &mut *self.db.inner.lock().await;
        let m = &mut inner.files;

        let mut key_buf = [0u8; MAX_KEY_SIZE];
        let mut header = [0; RECORD_HEADER_SIZE];

        // loop to retry if found record is deleted.
        loop {
            let mut is_lowest = [false; FILE_COUNT];
            let mut lowest_key: Vec<u8, MAX_KEY_SIZE> = Vec::new();
            let mut found = false;

            for i in 0..FILE_COUNT {
                if let Some(r) = &self.readers[i] {
                    let mut r = m.read_rehydrated(&mut inner.readers[0], r).await?;

                    // read header
                    match r.read(m, &mut header).await {
                        Ok(()) => {}
                        Err(PageReadError::Eof) => {
                            // reached EOF, remove this file.
                            self.readers[i] = None;
                            continue;
                        }
                        Err(e) => return Err(no_eof(e).into()),
                    };
                    let header = RecordHeader::decode(header)?;

                    // Read key
                    let got_key = &mut key_buf[..header.key_len];
                    r.read(m, got_key).await.map_err(no_eof)?;

                    let finished = match &self.upper_bound {
                        None => false,
                        Some(upper_bound) => match got_key[..].cmp(upper_bound.key) {
                            Ordering::Equal => !upper_bound.allow_equal,
                            Ordering::Less => false,
                            Ordering::Greater => true,
                        },
                    };
                    if finished {
                        // reached the upper bound, remove this file.
                        self.readers[i] = None;
                        continue;
                    }

                    let ordering = match found {
                        false => Ordering::Less,
                        true => got_key[..].cmp(&lowest_key[..]),
                    };
                    found = true;
                    match ordering {
                        Ordering::Less => {
                            lowest_key = unwrap!(Vec::from_slice(got_key));
                            is_lowest.fill(false);
                            is_lowest[i] = true;
                        }
                        Ordering::Equal => {
                            is_lowest[i] = true;
                        }
                        Ordering::Greater => {}
                    }
                }
            }

            if !found {
                return Ok(None);
            }

            // Advance all files matching the lowest key.
            // read the value from the highest file id (newer file).
            // if key is deleted, do another loop.
            let mut is_highest_file = true;
            let mut result = None;
            for i in (0..FILE_COUNT).rev() {
                if !is_lowest[i] {
                    continue;
                }
                let r = self.readers[i].as_ref().unwrap();
                let mut r = m.read_rehydrated(&mut inner.readers[0], r).await?;

                // read header
                match r.read(m, &mut header).await {
                    Ok(()) => {}
                    Err(PageReadError::Eof) => {
                        // reached EOF, remove this file.
                        self.readers[i] = None;
                        continue;
                    }
                    Err(e) => return Err(no_eof(e).into()),
                };
                let header = RecordHeader::decode(header)?;

                // Skip key
                r.skip(m, header.key_len).await.map_err(no_eof)?;

                if is_highest_file && !header.is_delete {
                    // read value
                    if header.key_len > key.len() {
                        return Err(CursorError::KeyBufferTooSmall);
                    }
                    if header.value_len > value.len() {
                        return Err(CursorError::ValueBufferTooSmall);
                    }
                    key[..header.key_len].copy_from_slice(&lowest_key);
                    r.read(m, &mut value[..header.value_len]).await.map_err(no_eof)?;
                    result = Some((header.key_len, header.value_len))
                } else {
                    // skip value
                    r.skip(m, header.value_len).await.map_err(no_eof)?;
                }

                self.readers[i] = Some(r.dehydrate());
                is_highest_file = false;
            }

            // if key was not deleted, return it.
            if result.is_some() {
                return Ok(result);
            }
        }
    }
}

impl<F: Flash> Inner<F> {
    async fn search_lower_bound_file(
        &mut self,
        file_id: FileID,
        bound: &Bound<'_>,
    ) -> Result<Option<DehydratedFileReader>, Error<F::Error>> {
        let r = self.files.read(&mut self.readers[0], file_id);
        let m = &mut self.files;
        let mut s = FileSearcher::new(r);

        let mut key_buf = [0u8; MAX_KEY_SIZE];
        let mut header = [0; RECORD_HEADER_SIZE];

        // Binary search
        let mut ok = s.start(m).await?;
        while ok {
            let dehydrated = s.reader().dehydrate();

            match s.reader().read(m, &mut header).await {
                Ok(()) => {}
                Err(PageReadError::Eof) => return Ok(None), // not found
                Err(e) => return Err(no_eof(e)),
            };
            let header = RecordHeader::decode(header)?;

            // Read key
            let got_key = &mut key_buf[..header.key_len];
            s.reader().read(m, got_key).await.map_err(no_eof)?;

            // Found?
            let dir = match got_key[..].cmp(bound.key) {
                Ordering::Equal => {
                    // if equal is allowed, return it.
                    if bound.allow_equal {
                        return Ok(Some(dehydrated));
                    }
                    // otherwise return the next key.
                    s.reader().skip(m, header.value_len).await.map_err(no_eof)?;
                    return Ok(Some(s.reader().dehydrate()));
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
            let dehydrated = r.dehydrate();

            match r.read(m, &mut header).await {
                Ok(()) => {}
                Err(PageReadError::Eof) => return Ok(None), // not found
                Err(e) => return Err(no_eof(e)),
            };
            let header = RecordHeader::decode(header)?;

            // Read key
            let got_key = &mut key_buf[..header.key_len];
            r.read(m, got_key).await.map_err(no_eof)?;

            // Found?
            match got_key[..].cmp(bound.key) {
                Ordering::Equal => {
                    // if equal is allowed, return it.
                    if bound.allow_equal {
                        return Ok(Some(dehydrated));
                    }
                    // otherwise return the next key.
                    s.reader().skip(m, header.value_len).await.map_err(no_eof)?;
                    return Ok(Some(s.reader().dehydrate()));
                }
                Ordering::Less => {}                  // keep going
                Ordering::Greater => return Ok(None), // done
            }

            r.skip(m, header.value_len).await.map_err(no_eof)?;
        }
    }
}

#[cfg(test)]
mod tests {
    use embassy_sync::blocking_mutex::raw::NoopRawMutex;

    use super::*;
    use crate::config::MAX_VALUE_SIZE;
    use crate::flash::MemFlash;
    use crate::Config;

    async fn check_read_range(db: &Database<impl Flash, NoopRawMutex>, entries: &[(&[u8], &[u8])]) {
        let rtx = db.read_transaction().await;
        let mut cursor = rtx.read_all().await.unwrap();

        let mut kbuf = [0; MAX_KEY_SIZE];
        let mut vbuf = [0; MAX_VALUE_SIZE];

        for (k, v) in entries {
            let (klen, vlen) = cursor.next(&mut kbuf, &mut vbuf).await.unwrap().unwrap();
            assert_eq!(*k, &kbuf[..klen]);
            assert_eq!(*v, &vbuf[..vlen]);
        }
        assert!(cursor.next(&mut kbuf, &mut vbuf).await.unwrap().is_none());
    }

    #[test_log::test(tokio::test)]
    async fn test_empty() {
        let mut f = MemFlash::new();
        let db = Database::new(&mut f, Config::default());
        db.format().await.unwrap();

        let rows: &[(&[u8], &[u8])] = &[];
        check_read_range(&db, rows).await;
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

        let mut wtx = db.write_transaction().await;
        wtx.write(b"bar", b"8765").await.unwrap();
        wtx.write(b"baz", b"4242").await.unwrap();
        wtx.write(b"foo", b"5678").await.unwrap();
        wtx.commit().await.unwrap();

        let mut wtx = db.write_transaction().await;
        wtx.write(b"lol", b"9999").await.unwrap();
        wtx.commit().await.unwrap();

        let rows: &[(&[u8], &[u8])] = &[
            (b"bar", b"8765"),
            (b"baz", b"4242"),
            (b"foo", b"5678"),
            (b"lol", b"9999"),
        ];
        check_read_range(&db, rows).await;
    }

    #[test_log::test(tokio::test)]
    async fn test_delete() {
        let mut f = MemFlash::new();
        let db = Database::new(&mut f, Config::default());
        db.format().await.unwrap();

        let mut wtx = db.write_transaction().await;
        wtx.write(b"bar", b"4321").await.unwrap();
        wtx.write(b"foo", b"1234").await.unwrap();
        wtx.commit().await.unwrap();

        let mut wtx = db.write_transaction().await;
        wtx.delete(b"bar").await.unwrap();
        wtx.commit().await.unwrap();

        let rows: &[(&[u8], &[u8])] = &[(b"foo", b"1234")];
        check_read_range(&db, rows).await;
    }

    #[test_log::test(tokio::test)]
    async fn test_delete_empty() {
        let mut f = MemFlash::new();
        let db = Database::new(&mut f, Config::default());
        db.format().await.unwrap();

        let mut wtx = db.write_transaction().await;
        wtx.write(b"bar", b"4321").await.unwrap();
        wtx.write(b"foo", b"1234").await.unwrap();
        wtx.commit().await.unwrap();

        let mut wtx = db.write_transaction().await;
        wtx.delete(b"bar").await.unwrap();
        wtx.commit().await.unwrap();

        let mut wtx = db.write_transaction().await;
        wtx.delete(b"foo").await.unwrap();
        wtx.commit().await.unwrap();

        let rows: &[(&[u8], &[u8])] = &[];
        check_read_range(&db, rows).await;
    }
}

use std::cmp::Ordering;
use std::mem::MaybeUninit;

use heapless::Vec;

use crate::config::*;
use crate::file::{FileManager, FileReader, FileWriter, SeekDirection};
use crate::flash::Flash;
use crate::page::ReadError;

pub const MAX_KEY_SIZE: usize = 64;

pub struct Database<F: Flash> {
    files: FileManager<F>,
}

impl<F: Flash> Database<F> {
    pub fn format(flash: F) {
        let mut m = FileManager::new(flash);
        m.format();
    }

    pub fn new(flash: F) -> Self {
        let mut m = FileManager::new(flash);
        m.mount();
        Self { files: m }
    }

    pub fn read_transaction(&mut self) -> ReadTransaction<'_, F> {
        ReadTransaction { db: self }
    }

    pub fn write_transaction(&mut self) -> WriteTransaction<'_, F> {
        let num_compacts = (0..LEVEL_COUNT)
            .rev()
            .take_while(|&i| self.find_empty_file_in_level(i).is_none())
            .count();

        for level in (LEVEL_COUNT - num_compacts)..LEVEL_COUNT {
            self.compact(level)
        }

        let file_id = self.find_empty_file_in_level(LEVEL_COUNT - 1).unwrap();
        println!("writing {}", file_id);
        let w = self.files.write(file_id);
        WriteTransaction {
            db: self,
            w,
            last_key: Vec::new(),
        }
    }

    fn file_id(level: usize, index: usize) -> FileID {
        (1 + level * BRANCHING_FACTOR + index) as _
    }

    /// Returns None if level is full.
    fn find_empty_file_in_level(&mut self, level: usize) -> Option<FileID> {
        for i in 0..BRANCHING_FACTOR {
            let file_id = Self::file_id(level, i);
            if self.files.is_empty(file_id) {
                return Some(file_id);
            }
        }
        None
    }

    /// Compact all files within the level into a single file in the upper level.
    /// Upper level MUST not be full.
    fn compact(&mut self, level: usize) {
        // Open file in higher level for writing.
        let fw = match level {
            0 => 0,
            _ => self.find_empty_file_in_level(level - 1).unwrap(),
        };
        assert!(self.files.is_empty(fw));
        let mut w = self.files.write(fw);

        println!(
            "compacting {}..{} -> {}",
            Self::file_id(level, 0),
            Self::file_id(level, BRANCHING_FACTOR - 1),
            fw
        );

        // Open all files in level for reading.
        let mut r: [MaybeUninit<FileReader<F>>; BRANCHING_FACTOR] = unsafe { MaybeUninit::uninit().assume_init() };
        for i in 0..BRANCHING_FACTOR {
            r[i].write(self.files.read(Self::file_id(level, i)));
        }
        let r = unsafe { &mut *(&mut r as *mut _ as *mut [FileReader<F>; BRANCHING_FACTOR]) };

        let m = &mut self.files;

        fn read_key_or_empty<F: Flash>(m: &mut FileManager<F>, r: &mut FileReader<F>, buf: &mut Vec<u8, MAX_KEY_SIZE>) {
            match read_key(m, r, buf) {
                Ok(()) => {}
                Err(ReadError::Eof) => buf.truncate(0),
            }
        }

        const NEW_VEC: Vec<u8, MAX_KEY_SIZE> = Vec::new();
        let mut k = [NEW_VEC; BRANCHING_FACTOR];

        for i in 0..BRANCHING_FACTOR {
            read_key_or_empty(m, &mut r[i], &mut k[i]);
        }

        loop {
            fn highest_bit(x: u32) -> Option<usize> {
                match x {
                    0 => None,
                    _ => Some(31 - x.leading_zeros() as usize),
                }
            }

            let mut bits: u32 = 0;
            for i in 0..BRANCHING_FACTOR {
                // Ignore files that have already reached the end.
                if k[i].is_empty() {
                    continue;
                }

                match highest_bit(bits) {
                    // If we haven't found any nonempty key yet, take the current one.
                    None => bits = 1 << i,
                    Some(j) => match k[j].cmp(&k[i]) {
                        Ordering::Greater => bits = 1 << i,
                        Ordering::Equal => bits |= 1 << i,
                        Ordering::Less => {}
                    },
                }
            }

            // All keys empty, means we've finished
            if bits == 0 {
                break;
            }

            match highest_bit(bits) {
                // All keys empty, means we've finished
                None => break,
                Some(i) => {
                    // Copy value from the highest bit (so newest file)
                    write_key(m, &mut w, &k[i]);
                    copy_value(m, &mut r[i], &mut w);
                    read_key_or_empty(m, &mut r[i], &mut k[i]);

                    // Advance all the others
                    for j in 0..BRANCHING_FACTOR {
                        if j != i && (bits & 1 << j) != 0 {
                            skip_value(m, &mut r[j]);
                            read_key_or_empty(m, &mut r[j], &mut k[j]);
                        }
                    }
                }
            }
        }

        let mut truncate = [(0, 0); BRANCHING_FACTOR];
        for i in 0..BRANCHING_FACTOR {
            truncate[i] = (Self::file_id(level, i), u32::MAX);
        }
        self.files.commit_and_truncate(Some(&mut w), &truncate);

        if level == 0 {
            self.files.rename(0, Self::file_id(level, 0));
        }
    }
}

pub struct ReadTransaction<'a, F: Flash + 'a> {
    db: &'a mut Database<F>,
}

impl<'a, F: Flash + 'a> ReadTransaction<'a, F> {
    pub fn read(&mut self, key: &[u8], value: &mut [u8]) -> usize {
        for file_id in (0..FILE_COUNT).rev() {
            let res = self.read_in_file(file_id as _, key, value);
            if res != 0 {
                return res;
            }
        }
        0
    }

    fn read_in_file(&mut self, file_id: FileID, key: &[u8], value: &mut [u8]) -> usize {
        let r = &mut self.db.files.read(file_id);
        let m = &mut self.db.files;

        let mut key_buf = Vec::new();

        // Binary search
        r.binary_search_start(m);
        loop {
            match read_key(m, r, &mut key_buf) {
                Ok(()) => {}
                Err(ReadError::Eof) => return 0, // key not present.
            };

            // Found?
            let dir = match key_buf[..].cmp(key) {
                Ordering::Equal => return read_value(m, r, value),
                Ordering::Less => SeekDirection::Right,
                Ordering::Greater => SeekDirection::Left,
            };

            // Not found, do a binary search step.
            if !r.binary_search_seek(m, dir) {
                // Can't seek anymore. In this case, the read pointer wasn't moved.
                // Skip the value from the key we read above, then go do linear search.
                skip_value(m, r);
                break;
            }
        }

        // Linear search
        loop {
            match read_key(m, r, &mut key_buf) {
                Ok(()) => {}
                Err(ReadError::Eof) => return 0, // key not present.
            };

            // Found?
            if key_buf == key {
                return read_value(m, r, value);
            }

            skip_value(m, r);
        }
    }
}

pub struct WriteTransaction<'a, F: Flash + 'a> {
    db: &'a mut Database<F>,
    w: FileWriter<F>,
    last_key: Vec<u8, MAX_KEY_SIZE>,
}

impl<'a, F: Flash + 'a> WriteTransaction<'a, F> {
    pub fn write(&mut self, key: &[u8], value: &[u8]) {
        if key.is_empty() {
            panic!("key cannot be empty.")
        }
        if key.len() > MAX_KEY_SIZE {
            panic!("key too long.")
        }

        if key <= &self.last_key {
            panic!("writes within a transaction must be sorted.");
        }
        self.last_key = Vec::from_slice(key).unwrap();

        write_record(&mut self.db.files, &mut self.w, key, value)
    }

    pub fn commit(mut self) {
        self.db.files.commit(&mut self.w)
    }
}

fn write_record<F: Flash>(m: &mut FileManager<F>, w: &mut FileWriter<F>, key: &[u8], value: &[u8]) {
    write_key(m, w, key);
    write_value(m, w, value);
}

fn write_key<F: Flash>(m: &mut FileManager<F>, w: &mut FileWriter<F>, key: &[u8]) {
    let key_len: u32 = key.len().try_into().unwrap();
    write_leb128(m, w, key_len);
    w.write(m, key);
}

fn write_value<F: Flash>(m: &mut FileManager<F>, w: &mut FileWriter<F>, value: &[u8]) {
    let value_len: u32 = value.len().try_into().unwrap();
    write_leb128(m, w, value_len);
    w.write(m, value);
    w.record_end();
}

fn copy_value<F: Flash>(m: &mut FileManager<F>, r: &mut FileReader<F>, w: &mut FileWriter<F>) {
    let mut len = read_leb128(m, r).unwrap() as usize;
    write_leb128(m, w, len as _);

    let mut buf = [0; 128];
    while len != 0 {
        let n = len.min(buf.len());
        len -= n;

        r.read(m, &mut buf[..n]).unwrap();
        w.write(m, &buf[..n]);
    }
    w.record_end();
}

fn write_leb128<F: Flash>(m: &mut FileManager<F>, w: &mut FileWriter<F>, mut val: u32) {
    loop {
        let mut part = val & 0x7F;
        let rest = val >> 7;
        if rest != 0 {
            part |= 0x80
        }

        w.write(m, &[part as u8]);

        if rest == 0 {
            return;
        }
        val = rest
    }
}

fn read_key<F: Flash>(
    m: &mut FileManager<F>,
    r: &mut FileReader<F>,
    buf: &mut Vec<u8, MAX_KEY_SIZE>,
) -> Result<(), ReadError> {
    let len = read_leb128(m, r)? as usize;
    assert!(len <= MAX_KEY_SIZE);
    unsafe { buf.set_len(len) };
    r.read(m, buf).unwrap();
    Ok(())
}

fn read_value<F: Flash>(m: &mut FileManager<F>, r: &mut FileReader<F>, value: &mut [u8]) -> usize {
    let len = read_leb128(m, r).unwrap() as usize;
    assert!(value.len() >= len);
    r.read(m, &mut value[..len]).unwrap();
    len
}

fn skip_value<F: Flash>(m: &mut FileManager<F>, r: &mut FileReader<F>) {
    let len = read_leb128(m, r).unwrap() as usize;
    r.skip(m, len).unwrap();
}

fn read_u8<F: Flash>(m: &mut FileManager<F>, r: &mut FileReader<F>) -> Result<u8, ReadError> {
    let mut buf = [0u8; 1];
    r.read(m, &mut buf)?;
    Ok(buf[0])
}

fn read_leb128<F: Flash>(m: &mut FileManager<F>, r: &mut FileReader<F>) -> Result<u32, ReadError> {
    let mut res = 0;
    let mut shift = 0;
    loop {
        let x = read_u8(m, r)?;
        res |= (x as u32 & 0x7F) << shift;
        if x & 0x80 == 0 {
            break;
        }
        shift += 7;
    }
    Ok(res)
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::flash::MemFlash;

    #[test]
    fn test() {
        let mut f = MemFlash::new();
        Database::format(&mut f);

        let mut db = Database::new(&mut f);

        let mut buf = [0u8; 1024];

        let mut wtx = db.write_transaction();
        wtx.write(b"bar", b"4321");
        wtx.write(b"foo", b"1234");
        wtx.commit();

        let mut rtx = db.read_transaction();
        let n = rtx.read(b"foo", &mut buf);
        assert_eq!(&buf[..n], b"1234");
        let n = rtx.read(b"bar", &mut buf);
        assert_eq!(&buf[..n], b"4321");
        let n = rtx.read(b"baz", &mut buf);
        assert_eq!(&buf[..n], b"");

        let mut wtx = db.write_transaction();
        wtx.write(b"bar", b"8765");
        wtx.write(b"baz", b"4242");
        wtx.write(b"foo", b"5678");
        wtx.commit();

        let mut rtx = db.read_transaction();
        let n = rtx.read(b"foo", &mut buf);
        assert_eq!(&buf[..n], b"5678");
        let n = rtx.read(b"bar", &mut buf);
        assert_eq!(&buf[..n], b"8765");
        let n = rtx.read(b"baz", &mut buf);
        assert_eq!(&buf[..n], b"4242");

        let mut wtx = db.write_transaction();
        wtx.write(b"lol", b"9999");
        wtx.commit();

        let mut rtx = db.read_transaction();
        let n = rtx.read(b"foo", &mut buf);
        assert_eq!(&buf[..n], b"5678");
        let n = rtx.read(b"bar", &mut buf);
        assert_eq!(&buf[..n], b"8765");
        let n = rtx.read(b"baz", &mut buf);
        assert_eq!(&buf[..n], b"4242");
        let n = rtx.read(b"lol", &mut buf);
        assert_eq!(&buf[..n], b"9999");
    }

    #[test]
    fn test_remount() {
        let mut f = MemFlash::new();
        Database::format(&mut f);

        let mut db = Database::new(&mut f);

        let mut buf = [0u8; 1024];

        let mut wtx = db.write_transaction();
        wtx.write(b"bar", b"4321");
        wtx.write(b"foo", b"1234");
        wtx.commit();

        // remount
        let mut db = Database::new(&mut f);

        let mut rtx = db.read_transaction();
        let n = rtx.read(b"foo", &mut buf);
        assert_eq!(&buf[..n], b"1234");
        let n = rtx.read(b"bar", &mut buf);
        assert_eq!(&buf[..n], b"4321");
        let n = rtx.read(b"baz", &mut buf);
        assert_eq!(&buf[..n], b"");

        let mut wtx = db.write_transaction();
        wtx.write(b"bar", b"8765");
        wtx.write(b"baz", b"4242");
        wtx.write(b"foo", b"5678");
        wtx.commit();

        // remount
        let mut db = Database::new(&mut f);

        let mut rtx = db.read_transaction();
        let n = rtx.read(b"foo", &mut buf);
        assert_eq!(&buf[..n], b"5678");
        let n = rtx.read(b"bar", &mut buf);
        assert_eq!(&buf[..n], b"8765");
        let n = rtx.read(b"baz", &mut buf);
        assert_eq!(&buf[..n], b"4242");

        let mut wtx = db.write_transaction();
        wtx.write(b"lol", b"9999");
        wtx.commit();

        // remount
        let mut db = Database::new(&mut f);

        let mut rtx = db.read_transaction();
        let n = rtx.read(b"foo", &mut buf);
        assert_eq!(&buf[..n], b"5678");
        let n = rtx.read(b"bar", &mut buf);
        assert_eq!(&buf[..n], b"8765");
        let n = rtx.read(b"baz", &mut buf);
        assert_eq!(&buf[..n], b"4242");
        let n = rtx.read(b"lol", &mut buf);
        assert_eq!(&buf[..n], b"9999");
    }
}

use std::borrow::BorrowMut;
use std::cell::{Cell, RefCell};
use std::cmp::Ordering;

use heapless::Vec;

use crate::config::*;
use crate::file::{FileManager, FileReader, FileWriter, SeekDirection};
use crate::flash::Flash;
use crate::page::ReadError;

pub const MAX_KEY_SIZE: usize = 64;

pub struct Database<F: Flash> {
    files: FileManager<F>,
    state: RefCell<State>,
}

struct State {
    levels: [usize; LEVEL_COUNT],
}

impl<F: Flash> Database<F> {
    pub fn format(flash: F) {
        FileManager::format(flash);
    }

    pub fn new(flash: F) -> Self {
        Self {
            files: FileManager::new(flash),
            state: RefCell::new(State {
                levels: [0; LEVEL_COUNT],
            }),
        }
    }

    pub fn read_transaction(&self) -> ReadTransaction<'_, F> {
        ReadTransaction { db: self }
    }

    pub fn write_transaction(&self) -> WriteTransaction<'_, F> {
        let s = &mut *self.state.borrow_mut();
        let file_id = self.get_file(s, LEVEL_COUNT - 1);
        println!("writing {}", file_id);
        let w = self.files.write(file_id);
        WriteTransaction {
            w,
            last_key: Vec::new(),
        }
    }

    fn file_id(level: usize, index: usize) -> FileID {
        (1 + level * BRANCHING_FACTOR + index) as _
    }

    fn get_file(&self, s: &mut State, level: usize) -> FileID {
        assert!(s.levels[level] <= BRANCHING_FACTOR);

        if s.levels[level] == BRANCHING_FACTOR {
            self.compact(s, level);
            assert!(s.levels[level] < BRANCHING_FACTOR);
        }

        let res = Self::file_id(level, s.levels[level]);
        s.levels[level] += 1;
        res
    }

    fn compact(&self, s: &mut State, level: usize) {
        let fw = match level {
            0 => 0,
            _ => self.get_file(s, level - 1),
        };
        let f1 = Self::file_id(level, 0);
        let f2 = Self::file_id(level, 1);

        println!("compacting {}, {} -> {}", f1, f2, fw);
        let r1 = &mut self.files.read(f1);
        let r2 = &mut self.files.read(f2);
        let mut ww = self.files.write(fw);
        let w = &mut ww;

        fn read_key_or_empty(r: &mut FileReader<impl Flash>, buf: &mut Vec<u8, MAX_KEY_SIZE>) {
            match read_key(r, buf) {
                Ok(()) => {}
                Err(ReadError::Eof) => buf.truncate(0),
            }
        }

        let mut k1 = Vec::new();
        let mut k2 = Vec::new();
        read_key_or_empty(r1, &mut k1);
        read_key_or_empty(r2, &mut k2);

        loop {
            match (k1.is_empty(), k2.is_empty(), k1.cmp(&k2)) {
                (true, true, _) => break,
                (false, false, Ordering::Equal) => {
                    // Advance both, keep 2nd value because it's newer.
                    write_key(w, &k1);
                    skip_value(r1);
                    copy_value(r2, w);
                    read_key_or_empty(r1, &mut k1);
                    read_key_or_empty(r2, &mut k2);
                }
                (false, true, _) | (false, false, Ordering::Less) => {
                    // Advance r1
                    write_key(w, &k1);
                    copy_value(r1, w);
                    read_key_or_empty(r1, &mut k1);
                }
                (true, false, _) | (false, false, Ordering::Greater) => {
                    // Advance r2
                    write_key(w, &k2);
                    copy_value(r2, w);
                    read_key_or_empty(r2, &mut k2);
                }
            }
        }

        ww.commit();
        drop(ww);

        self.files.delete(f1);
        self.files.delete(f2);

        if level == 0 {
            self.files.rename(0, f1);
            s.levels[level] = 1;
        } else {
            s.levels[level] = 0;
        }
    }
}

pub struct ReadTransaction<'a, F: Flash + 'a> {
    db: &'a Database<F>,
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

        let mut key_buf = Vec::new();

        // Binary search
        r.binary_search_start();
        loop {
            match read_key(r, &mut key_buf) {
                Ok(()) => {}
                Err(ReadError::Eof) => return 0, // key not present.
            };

            // Found?
            let dir = match key_buf[..].cmp(key) {
                Ordering::Equal => return read_value(r, value),
                Ordering::Less => SeekDirection::Right,
                Ordering::Greater => SeekDirection::Left,
            };

            // Not found, do a binary search step.
            if !r.binary_search_seek(dir) {
                // Can't seek anymore. In this case, the read pointer wasn't moved.
                // Skip the value from the key we read above, then go do linear search.
                skip_value(r);
                break;
            }
        }

        // Linear search
        loop {
            match read_key(r, &mut key_buf) {
                Ok(()) => {}
                Err(ReadError::Eof) => return 0, // key not present.
            };

            // Found?
            if key_buf == key {
                return read_value(r, value);
            }

            skip_value(r);
        }
    }
}

pub struct WriteTransaction<'a, F: Flash + 'a> {
    w: FileWriter<'a, F>,
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

        write_record(&mut self.w, key, value)
    }

    pub fn commit(mut self) {
        self.w.commit()
    }
}

fn write_record(w: &mut FileWriter<impl Flash>, key: &[u8], value: &[u8]) {
    write_key(w, key);
    write_value(w, value);
}

fn write_key(w: &mut FileWriter<impl Flash>, key: &[u8]) {
    let key_len: u32 = key.len().try_into().unwrap();
    write_leb128(w, key_len);
    w.write(key);
}

fn write_value(w: &mut FileWriter<impl Flash>, value: &[u8]) {
    let value_len: u32 = value.len().try_into().unwrap();
    write_leb128(w, value_len);
    w.write(value);
    w.record_end();
}

fn copy_value(r: &mut FileReader<impl Flash>, w: &mut FileWriter<impl Flash>) {
    let mut len = read_leb128(r).unwrap() as usize;
    write_leb128(w, len as _);

    let mut buf = [0; 128];
    while len != 0 {
        let n = len.min(buf.len());
        len -= n;

        r.read(&mut buf[..n]).unwrap();
        w.write(&buf[..n]);
    }
    w.record_end();
}

fn write_leb128(w: &mut FileWriter<impl Flash>, mut val: u32) {
    loop {
        let mut part = val & 0x7F;
        let rest = val >> 7;
        if rest != 0 {
            part |= 0x80
        }

        w.write(&[part as u8]);

        if rest == 0 {
            return;
        }
        val = rest
    }
}

fn read_key(r: &mut FileReader<impl Flash>, buf: &mut Vec<u8, MAX_KEY_SIZE>) -> Result<(), ReadError> {
    let len = read_leb128(r)? as usize;
    assert!(len <= MAX_KEY_SIZE);
    unsafe { buf.set_len(len) };
    r.read(buf).unwrap();
    Ok(())
}

fn read_value(r: &mut FileReader<impl Flash>, value: &mut [u8]) -> usize {
    let len = read_leb128(r).unwrap() as usize;
    assert!(value.len() >= len);
    r.read(&mut value[..len]).unwrap();
    len
}

fn skip_value(r: &mut FileReader<impl Flash>) {
    let len = read_leb128(r).unwrap() as usize;
    r.skip(len).unwrap();
}

fn read_u8(r: &mut FileReader<impl Flash>) -> Result<u8, ReadError> {
    let mut buf = [0u8; 1];
    r.read(&mut buf)?;
    Ok(buf[0])
}

fn read_leb128(r: &mut FileReader<impl Flash>) -> Result<u32, ReadError> {
    let mut res = 0;
    let mut shift = 0;
    loop {
        let x = read_u8(r)?;
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

        let db = Database::new(&mut f);

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
}

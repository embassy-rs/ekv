#![feature(generic_associated_types)]
#![deny(unused_must_use)]

// MUST go first.
pub mod macros;

pub mod backend;
pub mod backends;
pub mod flash;

use std::cell::Cell;
use std::cmp::Ordering;

use heapless::Vec;

use crate::backend::*;

pub const MAX_KEY_SIZE: usize = 64;

pub struct Database<B: Backend> {
    backend: B,
    run_start: Cell<u32>,
    run_end: Cell<u32>,
}

impl<B: Backend> Database<B> {
    pub fn new(backend: B) -> Self {
        Self {
            backend,
            run_start: Cell::new(0),
            run_end: Cell::new(0),
        }
    }

    pub fn read_transaction(&self) -> ReadTransaction<'_, B> {
        ReadTransaction { db: self }
    }

    pub fn write_transaction(&self) -> WriteTransaction<'_, B> {
        let run_id = self.run_end.get();
        self.run_end.set(run_id + 1);

        let w = self.backend.write_run(run_id);
        WriteTransaction {
            w,
            last_key: Vec::new(),
        }
    }

    pub fn compact(&self) {
        let start = self.run_start.get();
        let end = self.run_end.get();
        assert!(start + 2 == end);
        self.run_start.set(end);
        self.run_end.set(end + 1);

        let r1 = &mut self.backend.read_run(start);
        let r2 = &mut self.backend.read_run(start + 1);
        let w = &mut self.backend.write_run(start + 2);

        fn read_key_or_empty(r: &mut impl RunReader, buf: &mut Vec<u8, MAX_KEY_SIZE>) {
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
    }
}

pub struct ReadTransaction<'a, B: Backend + 'a> {
    db: &'a Database<B>,
}

impl<'a, B: Backend + 'a> ReadTransaction<'a, B> {
    pub fn read(&mut self, key: &[u8], value: &mut [u8]) -> usize {
        let start = self.db.run_start.get();
        let end = self.db.run_end.get();
        for run_id in (start..end).rev() {
            let res = self.read_in_run(run_id, key, value);
            if res != 0 {
                return res;
            }
        }
        0
    }

    fn read_in_run(&mut self, run_id: u32, key: &[u8], value: &mut [u8]) -> usize {
        let r = &mut self.db.backend.read_run(run_id);

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

pub struct WriteTransaction<'a, B: Backend + 'a> {
    w: B::RunWriter<'a>,
    last_key: Vec<u8, MAX_KEY_SIZE>,
}

impl<'a, B: Backend + 'a> WriteTransaction<'a, B> {
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
}

fn write_record(w: &mut impl RunWriter, key: &[u8], value: &[u8]) {
    write_key(w, key);
    write_value(w, value);
}

fn write_key(w: &mut impl RunWriter, key: &[u8]) {
    let key_len: u32 = key.len().try_into().unwrap();
    write_leb128(w, key_len);
    w.write(key);
}

fn write_value(w: &mut impl RunWriter, value: &[u8]) {
    let value_len: u32 = value.len().try_into().unwrap();
    write_leb128(w, value_len);
    w.write(value);
    w.record_end();
}

fn copy_value(r: &mut impl RunReader, w: &mut impl RunWriter) {
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

fn write_leb128(w: &mut impl RunWriter, mut val: u32) {
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

fn read_key(r: &mut impl RunReader, buf: &mut Vec<u8, MAX_KEY_SIZE>) -> Result<(), ReadError> {
    let len = read_leb128(r)? as usize;
    assert!(len <= MAX_KEY_SIZE);
    unsafe { buf.set_len(len) };
    r.read(buf).unwrap();
    Ok(())
}

fn read_value(r: &mut impl RunReader, value: &mut [u8]) -> usize {
    let len = read_leb128(r).unwrap() as usize;
    assert!(value.len() >= len);
    r.read(&mut value[..len]).unwrap();
    len
}

fn skip_value(r: &mut impl RunReader) {
    let len = read_leb128(r).unwrap() as usize;
    r.skip(len).unwrap();
}

fn read_u8(r: &mut impl RunReader) -> Result<u8, ReadError> {
    let mut buf = [0u8; 1];
    r.read(&mut buf)?;
    Ok(buf[0])
}

fn read_leb128(r: &mut impl RunReader) -> Result<u32, ReadError> {
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

    #[test]
    fn test() {
        let backend = backends::in_memory::InMemory::new();
        let db = Database::new(backend);

        let mut buf = [0u8; 1024];

        let mut wtx = db.write_transaction();
        wtx.write(b"bar", b"4321");
        wtx.write(b"foo", b"1234");

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

        let mut rtx = db.read_transaction();
        let n = rtx.read(b"foo", &mut buf);
        assert_eq!(&buf[..n], b"5678");
        let n = rtx.read(b"bar", &mut buf);
        assert_eq!(&buf[..n], b"8765");
        let n = rtx.read(b"baz", &mut buf);
        assert_eq!(&buf[..n], b"4242");

        db.compact();

        let mut rtx = db.read_transaction();
        let n = rtx.read(b"foo", &mut buf);
        assert_eq!(&buf[..n], b"5678");
        let n = rtx.read(b"bar", &mut buf);
        assert_eq!(&buf[..n], b"8765");
        let n = rtx.read(b"baz", &mut buf);
        assert_eq!(&buf[..n], b"4242");

        let mut wtx = db.write_transaction();
        wtx.write(b"lol", b"9999");

        let mut rtx = db.read_transaction();
        let n = rtx.read(b"foo", &mut buf);
        assert_eq!(&buf[..n], b"5678");
        let n = rtx.read(b"bar", &mut buf);
        assert_eq!(&buf[..n], b"8765");
        let n = rtx.read(b"baz", &mut buf);
        assert_eq!(&buf[..n], b"4242");
        let n = rtx.read(b"lol", &mut buf);
        assert_eq!(&buf[..n], b"9999");

        db.compact();

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

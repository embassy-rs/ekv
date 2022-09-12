#![feature(generic_associated_types)]
#![deny(unused_must_use)]

pub mod backend;
pub mod backends;

use std::cell::Cell;
use std::cmp::Ordering;

use heapless::Vec;

use crate::backend::*;

pub const KEY_MAX_SIZE: usize = 64;

pub struct Database<B: Backend> {
    backend: B,
    runs: Cell<u32>,
}

impl<B: Backend> Database<B> {
    pub fn new(backend: B) -> Self {
        Self {
            backend,
            runs: Cell::new(0),
        }
    }

    pub fn read_transaction(&self) -> ReadTransaction<'_, B> {
        ReadTransaction { db: self }
    }

    pub fn write_transaction(&self) -> WriteTransaction<'_, B> {
        let run_id = self.runs.get();
        self.runs.set(run_id + 1);

        let w = self.backend.write_run(run_id);
        WriteTransaction {
            w,
            last_key: Vec::new(),
        }
    }
}

pub struct ReadTransaction<'a, B: Backend + 'a> {
    db: &'a Database<B>,
}

impl<'a, B: Backend + 'a> ReadTransaction<'a, B> {
    pub fn read(&mut self, key: &[u8], value: &mut [u8]) -> usize {
        for run_id in (0..self.db.runs.get()).rev() {
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
    last_key: Vec<u8, KEY_MAX_SIZE>,
}

impl<'a, B: Backend + 'a> WriteTransaction<'a, B> {
    pub fn write(&mut self, key: &[u8], value: &[u8]) {
        if key.is_empty() {
            panic!("key cannot be empty.")
        }
        if key.len() > KEY_MAX_SIZE {
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
    let key_len: u32 = key.len().try_into().unwrap();
    let value_len: u32 = value.len().try_into().unwrap();

    write_leb128(w, key_len);
    w.write(key);
    write_leb128(w, value_len);
    w.write(value);
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

fn read_key(r: &mut impl RunReader, buf: &mut Vec<u8, KEY_MAX_SIZE>) -> Result<(), ReadError> {
    let len = read_leb128(r)? as usize;
    assert!(len <= KEY_MAX_SIZE);
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
    }
}

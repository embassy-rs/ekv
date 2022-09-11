#![feature(generic_associated_types)]
#![deny(unused_must_use)]

pub mod backend;
pub mod backends;

use std::cell::Cell;

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

        let writer = self.backend.write_run(run_id);
        WriteTransaction { writer }
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
        let mut reader = self.db.backend.read_run(run_id);
        loop {
            let got_key_len = match Self::read_leb128(&mut reader) {
                Ok(x) => x as usize,
                Err(ReadError::Eof) => return 0, // key not present.
            };
            println!("got_key_len {}", got_key_len);
            assert!(got_key_len <= KEY_MAX_SIZE);
            let mut got_key = [0u8; KEY_MAX_SIZE];
            reader.read(&mut got_key[..got_key_len]).unwrap();
            let got_key = &got_key[..got_key_len];
            let got_value_len = Self::read_leb128(&mut reader).unwrap() as usize;
            println!("got_value_len {}", got_value_len);

            if got_key == key {
                assert!(value.len() >= got_value_len);
                reader.read(&mut value[..got_value_len]).unwrap();
                return got_value_len;
            }

            reader.skip(got_value_len).unwrap();
        }
    }

    fn read_u8(reader: &mut B::RunReader<'_>) -> Result<u8, ReadError> {
        let mut buf = [0u8; 1];
        reader.read(&mut buf)?;
        Ok(buf[0])
    }

    fn read_leb128(reader: &mut B::RunReader<'_>) -> Result<u32, ReadError> {
        let mut res = 0;
        let mut shift = 0;
        loop {
            let x = Self::read_u8(reader)?;
            res |= (x as u32 & 0x7F) << shift;
            if x & 0x80 == 0 {
                break;
            }
            shift += 7;
        }
        Ok(res)
    }
}

pub struct WriteTransaction<'a, B: Backend + 'a> {
    writer: B::RunWriter<'a>,
}

impl<'a, B: Backend + 'a> WriteTransaction<'a, B> {
    pub fn write(&mut self, key: &[u8], value: &[u8]) {
        let key_len: u32 = key.len().try_into().unwrap();
        let value_len: u32 = value.len().try_into().unwrap();

        self.write_leb128(key_len);
        self.writer.write(key);
        self.write_leb128(value_len);
        self.writer.write(value);
        self.writer.record_end();
    }

    fn write_leb128(&mut self, mut val: u32) {
        loop {
            let mut part = val & 0x7F;
            let rest = val >> 7;
            if rest != 0 {
                part |= 0x80
            }

            self.writer.write(&[part as u8]);

            if rest == 0 {
                return;
            }
            val = rest
        }
    }
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
        wtx.write(b"foo", b"1234");
        wtx.write(b"bar", b"4321");

        let mut rtx = db.read_transaction();
        let n = rtx.read(b"foo", &mut buf);
        assert_eq!(&buf[..n], b"1234");
        let n = rtx.read(b"bar", &mut buf);
        assert_eq!(&buf[..n], b"4321");
        let n = rtx.read(b"baz", &mut buf);
        assert_eq!(&buf[..n], b"");

        let mut wtx = db.write_transaction();
        wtx.write(b"foo", b"5678");
        wtx.write(b"bar", b"8765");
        wtx.write(b"baz", b"4242");

        let mut rtx = db.read_transaction();
        let n = rtx.read(b"foo", &mut buf);
        assert_eq!(&buf[..n], b"5678");
        let n = rtx.read(b"bar", &mut buf);
        assert_eq!(&buf[..n], b"8765");
        let n = rtx.read(b"baz", &mut buf);
        assert_eq!(&buf[..n], b"4242");
    }
}

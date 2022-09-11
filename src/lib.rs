#![feature(generic_associated_types)]

pub mod backend;
pub mod backends;

use crate::backend::*;

pub const KEY_MAX_SIZE: usize = 64;

pub struct Database<B: Backend> {
    backend: B,
}

impl<B: Backend> Database<B> {
    pub fn new(backend: B) -> Self {
        Self { backend }
    }

    pub fn read_transaction(&self) -> ReadTransaction<'_, B> {
        let reader = self.backend.read_run(0);
        ReadTransaction { reader }
    }

    pub fn write_transaction(&self) -> WriteTransaction<'_, B> {
        let writer = self.backend.write_run(0);
        WriteTransaction { writer }
    }
}

pub struct ReadTransaction<'a, B: Backend + 'a> {
    reader: B::RunReader<'a>,
}

impl<'a, B: Backend + 'a> ReadTransaction<'a, B> {
    pub fn read(&mut self, key: &[u8], value: &mut [u8]) -> usize {
        loop {
            let got_key_len = self.read_leb128() as usize;
            println!("got_key_len {}", got_key_len);
            assert!(got_key_len <= KEY_MAX_SIZE);
            let mut got_key = [0u8; KEY_MAX_SIZE];
            self.reader.read(&mut got_key[..got_key_len]);
            let got_key = &got_key[..got_key_len];
            let got_value_len = self.read_leb128() as usize;
            println!("got_value_len {}", got_value_len);

            if got_key == key {
                assert!(value.len() >= got_value_len);
                self.reader.read(&mut value[..got_value_len]);
                return got_value_len;
            }

            self.reader.skip(got_value_len);
        }
    }

    fn read_u8(&mut self) -> u8 {
        let mut buf = [0u8; 1];
        self.reader.read(&mut buf);
        buf[0]
    }

    fn read_leb128(&mut self) -> u32 {
        let mut res = 0;
        let mut shift = 0;
        loop {
            let x = self.read_u8();
            res |= (x as u32 & 0x7F) << shift;
            if x & 0x80 == 0 {
                break;
            }
            shift += 7;
        }
        res
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

        let mut wtx = db.write_transaction();
        wtx.write(b"foo", b"1234");
        wtx.write(b"bar", b"4321");

        let mut buf = [0u8; 1024];

        let mut rtx = db.read_transaction();
        let n = rtx.read(b"foo", &mut buf);
        assert_eq!(&buf[..n], b"1234");
        let n = rtx.read(b"bar", &mut buf);
        assert_eq!(&buf[..n], b"4321");
    }
}

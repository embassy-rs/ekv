use std::cell::RefCell;
use std::collections::HashMap;
use std::marker::PhantomData;
use std::mem;
use std::rc::Rc;

use crate::backend::{self, ReadError, SeekDirection};

struct Run {
    records: Vec<Vec<u8>>,
}

impl Run {
    fn new() -> Self {
        Self { records: Vec::new() }
    }
}

struct Data {
    runs: HashMap<u32, Rc<RefCell<Run>>>,
}

pub struct InMemory {
    data: RefCell<Data>,
}

impl InMemory {
    pub fn new() -> Self {
        Self {
            data: RefCell::new(Data { runs: HashMap::new() }),
        }
    }
}

impl backend::Backend for InMemory {
    type RunReader<'a> = RunReader<'a>;
    type RunWriter<'a> = RunWriter<'a>;

    fn read_run(&self, run_id: u32) -> Self::RunReader<'_> {
        let data = self.data.borrow();
        let run = data.runs.get(&run_id).unwrap().clone();
        RunReader::new(run)
    }

    fn write_run(&self, run_id: u32) -> Self::RunWriter<'_> {
        let mut data = self.data.borrow_mut();
        let run = Rc::new(RefCell::new(Run::new()));
        assert!(data.runs.insert(run_id, run).is_none());
        let run = data.runs.get(&run_id).unwrap().clone();
        RunWriter::new(run)
    }
}

pub struct RunReader<'a> {
    run: Rc<RefCell<Run>>,
    phantom: PhantomData<&'a ()>,

    // for binary search
    record_l: usize,
    record_r: usize,

    // current read pointer
    record: usize,
    pos: usize,
}

impl<'a> RunReader<'a> {
    fn new(run: Rc<RefCell<Run>>) -> Self {
        let nrecords = run.borrow().records.len();
        Self {
            run,
            phantom: PhantomData,

            record_l: 0,
            record_r: nrecords,
            record: nrecords / 2,
            pos: 0,
        }
    }
}

impl<'a> backend::RunReader for RunReader<'a> {
    fn binary_search_seek(&mut self, direction: SeekDirection) -> bool {
        if self.record_l + 1 >= self.record_r {
            return false;
        }

        let m = (self.record_l + self.record_r) / 2;

        match direction {
            SeekDirection::Left => self.record_r = m,
            SeekDirection::Right => self.record_l = m,
        }

        self.record = (self.record_l + self.record_r) / 2;
        self.pos = 0;

        true
    }

    fn skip(&mut self, mut len: usize) -> Result<(), backend::ReadError> {
        let run = self.run.borrow();
        while len != 0 {
            if self.record >= run.records.len() {
                return Err(ReadError::Eof);
            }

            let record = &run.records[self.record];
            assert!(self.pos < record.len());
            let n = len.min(record.len() - self.pos);
            len -= n;
            self.pos += n;
            if self.pos == record.len() {
                self.pos = 0;
                self.record += 1;
            }
        }
        Ok(())
    }

    fn read(&mut self, mut data: &mut [u8]) -> Result<(), backend::ReadError> {
        let run = self.run.borrow();
        while !data.is_empty() {
            if self.record >= run.records.len() {
                return Err(ReadError::Eof);
            }

            let record = &run.records[self.record];
            assert!(self.pos < record.len());
            let n = data.len().min(record.len() - self.pos);
            data[..n].copy_from_slice(&record[self.pos..][..n]);
            data = &mut data[n..];
            self.pos += n;
            if self.pos == record.len() {
                self.pos = 0;
                self.record += 1;
            }
        }
        Ok(())
    }
}

pub struct RunWriter<'a> {
    run: Rc<RefCell<Run>>,
    current_record: Vec<u8>,
    phantom: PhantomData<&'a ()>,
}

impl<'a> RunWriter<'a> {
    fn new(run: Rc<RefCell<Run>>) -> Self {
        Self {
            run,
            current_record: Vec::new(),
            phantom: PhantomData,
        }
    }
}

impl<'a> backend::RunWriter for RunWriter<'a> {
    fn write(&mut self, data: &[u8]) {
        self.current_record.extend_from_slice(data);
    }

    fn record_end(&mut self) {
        let record = mem::take(&mut self.current_record);
        self.run.borrow_mut().records.push(record);
    }
}

impl<'a> Drop for RunWriter<'a> {
    fn drop(&mut self) {
        assert!(self.current_record.is_empty())
    }
}

use std::cell::RefCell;
use std::collections::HashMap;
use std::marker::PhantomData;
use std::mem;
use std::rc::Rc;

use crate::backend;

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
    record: usize,
    pos: usize,
    phantom: PhantomData<&'a ()>,
}

impl<'a> RunReader<'a> {
    fn new(run: Rc<RefCell<Run>>) -> Self {
        Self {
            run,
            record: 0,
            pos: 0,
            phantom: PhantomData,
        }
    }
}

impl<'a> backend::RunReader for RunReader<'a> {
    fn skip(&mut self, mut len: usize) {
        while len != 0 {
            let run = self.run.borrow();

            assert!(self.record < run.records.len());
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
    }

    fn read(&mut self, mut data: &mut [u8]) {
        while !data.is_empty() {
            let run = self.run.borrow();

            assert!(self.record < run.records.len());
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

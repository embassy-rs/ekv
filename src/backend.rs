pub trait Backend {
    type RunReader<'a>: RunReader
    where
        Self: 'a;
    type RunWriter<'a>: RunWriter
    where
        Self: 'a;

    fn read_run(&self, run_id: u32) -> Self::RunReader<'_>;
    fn write_run(&self, run_id: u32) -> Self::RunWriter<'_>;
}

pub trait RunWriter {
    fn write(&mut self, data: &[u8]);
    fn record_end(&mut self);
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ReadError {
    Eof,
}

pub trait RunReader {
    fn read(&mut self, data: &mut [u8]) -> Result<(), ReadError>;
    fn skip(&mut self, len: usize) -> Result<(), ReadError>;
}

#![deny(unused_must_use)]
#![feature(result_option_inspect)]
#![feature(try_blocks)]

// MUST go first.
mod fmt;
mod macros;

mod alloc;
mod config;

// Layer 0: flash access
pub mod flash;

// Layer 1: page
mod page;

// Layer 2: file
mod file;

// Layer 3: record
mod record;
pub use record::Database;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub enum Error {
    Corrupted,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub enum ReadKeyError {
    BufferTooSmall,
    Corrupted,
}

impl From<Error> for ReadKeyError {
    fn from(e: Error) -> Self {
        match e {
            Error::Corrupted => Self::Corrupted,
        }
    }
}

impl From<page::ReadError> for ReadKeyError {
    fn from(e: page::ReadError) -> Self {
        match e {
            page::ReadError::Eof => Self::Corrupted,
            page::ReadError::Corrupted => Self::Corrupted,
        }
    }
}

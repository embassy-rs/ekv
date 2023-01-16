#![cfg_attr(not(feature = "std"), no_std)]
#![deny(unused_must_use)]
#![feature(result_option_inspect)]
#![feature(try_blocks)]

// MUST go first.
mod fmt;
mod macros;

mod alloc;
pub mod config;
pub mod flash;
mod types;
pub use record::Database;

#[cfg(feature = "_test")]
pub mod file;
#[cfg(feature = "_test")]
pub mod page;
#[cfg(feature = "_test")]
pub mod record;

#[cfg(not(feature = "_test"))]
mod file;
#[cfg(not(feature = "_test"))]
mod page;
#[cfg(not(feature = "_test"))]
mod record;

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

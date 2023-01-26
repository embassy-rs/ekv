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
pub enum Error<E> {
    Flash(E),
    Corrupted,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub enum ReadKeyError<E> {
    Flash(E),
    BufferTooSmall,
    Corrupted,
}

impl<E> From<Error<E>> for ReadKeyError<E> {
    fn from(e: Error<E>) -> Self {
        match e {
            Error::Flash(e) => Self::Flash(e),
            Error::Corrupted => Self::Corrupted,
        }
    }
}

impl<E> From<page::ReadError<E>> for ReadKeyError<E> {
    fn from(e: page::ReadError<E>) -> Self {
        match e {
            page::ReadError::Flash(e) => Self::Flash(e),
            page::ReadError::Eof => Self::Corrupted,
            page::ReadError::Corrupted => Self::Corrupted,
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub enum WriteKeyError<E> {
    Flash(E),
    Full,
    Corrupted,
}

impl<E> From<Error<E>> for WriteKeyError<E> {
    fn from(e: Error<E>) -> Self {
        match e {
            Error::Flash(e) => Self::Flash(e),
            Error::Corrupted => Self::Corrupted,
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
struct CorruptedError;

impl<E> From<CorruptedError> for Error<E> {
    fn from(_: CorruptedError) -> Self {
        Self::Corrupted
    }
}
impl<E> From<CorruptedError> for page::ReadError<E> {
    fn from(_: CorruptedError) -> Self {
        Self::Corrupted
    }
}
impl<E> From<CorruptedError> for ReadKeyError<E> {
    fn from(_: CorruptedError) -> Self {
        Self::Corrupted
    }
}
impl<E> From<CorruptedError> for WriteKeyError<E> {
    fn from(_: CorruptedError) -> Self {
        Self::Corrupted
    }
}

impl<E> From<CorruptedError> for file::SearchSeekError<E> {
    fn from(_: CorruptedError) -> Self {
        Self::Corrupted
    }
}

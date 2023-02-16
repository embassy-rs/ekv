use crate::file::SearchSeekError;
use crate::page::ReadError as PageReadError;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub enum Error<E> {
    Corrupted,
    Flash(E),
}

impl<E> From<FormatError<E>> for Error<E> {
    fn from(value: FormatError<E>) -> Self {
        match value {
            FormatError::Flash(e) => Self::Flash(e),
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub enum FormatError<E> {
    Flash(E),
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub enum MountError<E> {
    Corrupted,
    Flash(E),
}

impl<E> From<Error<E>> for MountError<E> {
    fn from(e: Error<E>) -> Self {
        match e {
            Error::Flash(e) => Self::Flash(e),
            Error::Corrupted => Self::Corrupted,
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub enum ReadError<E> {
    KeyNotFound,
    KeyTooBig,
    BufferTooSmall,
    Corrupted,
    Flash(E),
}

impl<E> From<Error<E>> for ReadError<E> {
    fn from(e: Error<E>) -> Self {
        match e {
            Error::Flash(e) => Self::Flash(e),
            Error::Corrupted => Self::Corrupted,
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub enum WriteError<E> {
    NotSorted,
    KeyTooBig,
    ValueTooBig,
    TransactionCanceled,
    Full,
    Corrupted,
    Flash(E),
}

impl<E> From<Error<E>> for WriteError<E> {
    fn from(e: Error<E>) -> Self {
        match e {
            Error::Flash(e) => Self::Flash(e),
            Error::Corrupted => Self::Corrupted,
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub enum CommitError<E> {
    TransactionCanceled,
    Corrupted,
    Flash(E),
}

impl<E> From<Error<E>> for CommitError<E> {
    fn from(e: Error<E>) -> Self {
        match e {
            Error::Flash(e) => Self::Flash(e),
            Error::Corrupted => Self::Corrupted,
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub struct CorruptedError;

impl<E> From<CorruptedError> for Error<E> {
    fn from(_: CorruptedError) -> Self {
        Self::Corrupted
    }
}

impl<E> From<CorruptedError> for PageReadError<E> {
    fn from(_: CorruptedError) -> Self {
        Self::Corrupted
    }
}

impl<E> From<CorruptedError> for ReadError<E> {
    fn from(_: CorruptedError) -> Self {
        Self::Corrupted
    }
}

impl<E> From<CorruptedError> for WriteError<E> {
    fn from(_: CorruptedError) -> Self {
        Self::Corrupted
    }
}

impl<E> From<CorruptedError> for SearchSeekError<E> {
    fn from(_: CorruptedError) -> Self {
        Self::Corrupted
    }
}

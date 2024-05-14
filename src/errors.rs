use crate::file::SearchSeekError;
use crate::page::ReadError as PageReadError;

/// Error returned by [`ReadTransaction::read_all`](crate::ReadTransaction::read_all),  [`ReadTransaction::read_range`](crate::ReadTransaction::read_range).
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

/// Error returned by [`Database::format`](crate::Database::format).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub enum FormatError<E> {
    /// Some operation on the underlying [`Flash`](crate::flash::Flash) failed.
    Flash(E),
}

/// Error returned by [`Database::mount`](crate::Database::mount).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub enum MountError<E> {
    /// Database is corrupted, or not formatted yet.
    Corrupted,
    /// Some operation on the underlying [`Flash`](crate::flash::Flash) failed.
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

/// Error returned by [`ReadTransaction::read`](crate::ReadTransaction::read).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub enum ReadError<E> {
    /// The requested key is not present in the database.
    KeyNotFound,
    /// The requested key is larger than [`MAX_KEY_SIZE`](crate::config::MAX_KEY_SIZE)
    KeyTooBig,
    /// The requested key was found, but the value was larger than the provided buffer.
    BufferTooSmall,
    /// Database is corrupted, or not formatted yet.
    Corrupted,
    /// Some operation on the underlying [`Flash`](crate::flash::Flash) failed.
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

/// Error returned by [`WriteTransaction::write`](crate::WriteTransaction::write).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub enum WriteError<E> {
    /// The key is not lexicographically larger than the last written key in this transaction.
    ///
    /// Writes in a transaction must be sorted in ascending order, and you may not write the same
    /// key twice.
    NotSorted,
    /// The key is larger than [`MAX_KEY_SIZE`](crate::config::MAX_KEY_SIZE)
    KeyTooBig,
    /// The value is larger than [`MAX_VALUE_SIZE`](crate::config::MAX_VALUE_SIZE)
    ValueTooBig,
    /// Transaction is canceled. See [`WriteTransaction`](crate::WriteTransaction) for details.
    TransactionCanceled,
    /// The database storage is full.
    Full,
    /// Database is corrupted, or not formatted yet.
    Corrupted,
    /// Some operation on the underlying [`Flash`](crate::flash::Flash) failed.
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

/// Error returned by [`WriteTransaction::commit`](crate::WriteTransaction::commit).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub enum CommitError<E> {
    /// Transaction is canceled. See [`WriteTransaction`](crate::WriteTransaction) for details.
    TransactionCanceled,
    /// Database is corrupted, or not formatted yet.
    Corrupted,
    /// Some operation on the underlying [`Flash`](crate::flash::Flash) failed.
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

/// Error returned by [`Cursor::next`](crate::Cursor::next).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub enum CursorError<E> {
    /// The provided buffer for the key was too small.
    KeyBufferTooSmall,
    /// The provided buffer for the value was too small.
    ValueBufferTooSmall,
    /// Database is corrupted, or not formatted yet.
    Corrupted,
    /// Some operation on the underlying [`Flash`](crate::flash::Flash) failed.
    Flash(E),
}

impl<E> From<Error<E>> for CursorError<E> {
    fn from(e: Error<E>) -> Self {
        match e {
            Error::Flash(e) => Self::Flash(e),
            Error::Corrupted => Self::Corrupted,
        }
    }
}

/// Database is corrupted, or not formatted yet.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub(crate) struct CorruptedError;

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

impl<E> From<CorruptedError> for CursorError<E> {
    fn from(_: CorruptedError) -> Self {
        Self::Corrupted
    }
}

pub(crate) fn no_eof<T>(e: PageReadError<T>) -> Error<T> {
    match e {
        PageReadError::Corrupted => Error::Corrupted,
        #[cfg(not(feature = "_panic-on-corrupted"))]
        PageReadError::Eof => Error::Corrupted,
        #[cfg(feature = "_panic-on-corrupted")]
        PageReadError::Eof => panic!("corrupted"),
        PageReadError::Flash(x) => Error::Flash(x),
    }
}

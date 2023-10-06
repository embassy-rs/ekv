#![doc = include_str!("../README.md")]
#![cfg_attr(not(feature = "std"), no_std)]
#![deny(unused_must_use)]
#![feature(result_option_inspect)]
#![feature(try_blocks)]
#![feature(async_fn_in_trait)]
#![allow(clippy::large_enum_variant)]
#![allow(clippy::new_without_default)]
#![warn(missing_docs)]

// MUST go first.
mod fmt;
mod macros;

mod alloc;
pub mod config;
mod errors;
pub mod flash;
mod types;

pub use errors::{CommitError, FormatError, MountError, ReadError, WriteError};
pub use record::{Config, Database, ReadTransaction, WriteTransaction};

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

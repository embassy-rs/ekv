#![deny(unused_must_use)]

// MUST go first.
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

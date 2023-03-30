# ekv

Key-value database for embedded systems, for raw NOR flash, using an LSM-Tree.

## <a href="https://crates.io/crates/ekv">crates.io</a> - <a href="https://docs.rs/ekv">Docs</a> - <a href="https://docs.embassy.dev/ekv">Docs for git</a> - <a href="https://matrix.to/#/#ekv:matrix.org">Chat</a>

## Features

- Keys and values are arbitrary-length byte arrays. The database is essentially an on-disk `Map<Vec<u8>, Vec<u8>>`.
- `O(log n)` reads. Amortized `O(log n)` writes. No linear scans!
- Power-fail safe. Powering off in the middle of writes never corrupts the database.
- Transaction support:
  - Atomic writes: Start a write transaction, write multiple keys, commit. If power fails midway, either all or no writes are committed.
  - Consistent reads: Read transactions see a consistent snapshot of the database, unaffected by concurrent writes.
  - Unlimited read transactions and one write transaction are allowed concurrently.
  - Read transactions are only blocked by a write transaction commit, not by the whole write transaction. Commit is fast, `O(1)`.
- Wear leveling: erase cycles are spread out evenly between all flash pages. Pages are allocated cyclically. At boot, a random seed is required to decide which is the first.
- Corruption-resistant: A corrupted or deliberately manipulated flash image cannot cause crashes, panics or infinite loops, only `Err(Corrupted)` errors.
- Optional CRC32 protection of headers and data on flash.
- Extensively tested, using unit tests and fuzzing.

## Current status

The project is in **production ready** stage. The author is using it in production, it is fully functional and has no known bugs. This does not mean it's feature-complete, see the limitations below.

The on-disk format is **not stable** yet. 
- Major releases can do fully breaking changes to the on-disk format. New code won't be able to read old databases and vice-versa. No code to upgrade in-place will be provided. You'll have to either format and lose all data, or read out the data and write it back in the newer format.
- Minor releases can do backwards-compatible changes: they'll always be able to read databases written by older versions, but they might write databases using new features that older versions can't read.
- Patch releases will maintain full backwards and forwards on-disk compatibility.

## Future work

- Optimize tiny write transactions: append to the last file if possible, instead of starting a new one. Currently each write transaction opens a new file, which will have to erase at least one full page, even if the transaction writes just one small key. It is recommended to batch multiple writes in a single transaction
for performance.
- Support access align higher than 4. Currently reads/writes are (optionally) aligned up to 4 bytes. Some flash out there can only be written in 8-byte words or higher.
- Add a max chunk size, to reduce the RAM requirement in PageReader.
- Allow writes within a transaction to be unsorted.
- Allow reads within a write transaction. They should see the the not yet committed writes in the current transaction.
- Allow iterating the records in the database.
- Add optional encryption + authentication support (which disables CRCs)
- Integrate with `embedded-storage`.

## Alternatives

- If the dataset fits in RAM, you could read/write it all at once. Either making it `repr(C)` and transmuting, or serializing it with some compact `serde` flavor such as [`postcard`](https://docs.rs/postcard)
- [sequential-storage](https://docs.rs/sequential-storage) - Rust. Linear search. No multi-key transactions. Multiple single-key transactions can be written to the same page, unlike `ekv`.
- [Tock's tickv](https://docs.rs/tickv) - Rust. Hash table. No multi-key transactions.
- [pigweed's pw_kvs](https://pigweed.dev/pw_kvs/) - C. Linear search. No multi-key transactions. Multiple single-key transactions can be written to the same page, unlike `ekv`.

## Why the name?

Embedded Key-Value! :)

## License

This work is licensed under either of

- Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE) or
  <http://www.apache.org/licenses/LICENSE-2.0>)
- MIT license ([LICENSE-MIT](LICENSE-MIT) or <http://opensource.org/licenses/MIT>)

at your option.


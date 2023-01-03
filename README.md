# ekv

Key-value database for embedded systems, for raw NOR flash, using an LSM-Tree.

## Features

None yet. This is a work in progress. Don't use it. When it's done, it will have:

- Arbitrary length keys and values. (TODO: document limits)
- `O(log n)` reads. Amortized `O(log n)` writes. No linear scans!
- Power-fail safe. Powering off in the middle of writes never corrupts the database.
- Transaction support:
  - Atomic writes: Start a write transaction, write multiple keys, commit. If power fails midway, either all or no writes are committed.
  - Consistent reads: Read transactions see a consistent snapshot of the database, unaffected by concurrent writes.

## TODO

- Handle storage full condition. Currently panics. It should trigger compactions, then return error if still full.
- Add skiplist to file header, to make seeking O(log n) instead of O(n)
- Add binary search within a file. This makes reads O(log n).
- Add (optional) CRCs to check data integrity. Both headers and data.
- Allow appending to already-written pages.
  - Use it to optimize the metadata page: append to the existing one instead of erasing+writing a new one if possible.
  - Use it to optimize tiny write transactions: append to the last file if possible, instead of starting a new one.
- Allow writes within a transaction to be unsorted.
- Allow reads within a write transaction. They should see the the not yet committed writes in the current transaction.
- Allow N read transactions + 1 write transaction concurrently.
- Support "progressive compaction": instead of compacting 2 whole files into one, do it page by page.
- Support write align. Currently writes are not aligned, but most flash out there can only write in 4-byte or 8-byte blocks.
- Add optional encryption + authentication support (which disables CRCs)
- Async
- Integrate with `embedded-storage`.

## Why the name?

Embedded Key-Value! :)

## License

This work is licensed under either of

- Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE) or
  <http://www.apache.org/licenses/LICENSE-2.0>)
- MIT license ([LICENSE-MIT](LICENSE-MIT) or <http://opensource.org/licenses/MIT>)

at your option.


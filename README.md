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
  - Unlimited read transactions and one write transaction are allowed concurrently.

## TODO

Soon:

- Add (optional) CRCs to check data integrity. Both headers and data.
- Free uncommitted pages on transaction drop.
- Remove tombstone records when compacting the topmost level.
- Allow the empty key `[]` (compaction assumes they're nonempty)

Later:

- Support access align higher than 4. Currently reads/writes are (optionally) aligned up to 4 bytes. Some flash out there can only be written in 8-byte words or higher.
- Add a max chunk size, to reduce the RAM requirement in PageReader.
- Optimize tiny write transactions: append to the last file if possible, instead of starting a new one.
- Allow writes within a transaction to be unsorted.
- Allow reads within a write transaction. They should see the the not yet committed writes in the current transaction.
- Add optional encryption + authentication support (which disables CRCs)
- Integrate with `embedded-storage`.

## Why the name?

Embedded Key-Value! :)

## License

This work is licensed under either of

- Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE) or
  <http://www.apache.org/licenses/LICENSE-2.0>)
- MIT license ([LICENSE-MIT](LICENSE-MIT) or <http://opensource.org/licenses/MIT>)

at your option.


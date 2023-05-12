#!/bin/bash

set -euxo pipefail

export RUSTFLAGS=-Dwarnings

cargo fmt --check
cargo test --release
cargo test --release --features crc
cargo clippy
cargo clippy --features crc
(cd examples/nrf; cargo fmt --check; cargo build --release --features defmt)
(cd examples/rp2040; cargo fmt --check; cargo build --release)

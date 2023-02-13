#!/bin/bash

set -euxo pipefail

export RUSTFLAGS=-Dwarnings

cargo fmt --check
cargo test
cargo clippy
(cd examples/nrf; cargo fmt --check; cargo build --release)
#!/bin/bash

set -euxo pipefail

export RUSTFLAGS=-Dwarnings

cargo test
cargo clippy
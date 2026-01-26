#!/bin/bash

set -euxo pipefail

cargo install cargo-fuzz

export RUSTFLAGS=-Dwarnings

cargo fmt --check

FEATURESET=(
    ekv/page-size-256,ekv/max-page-count-64,ekv/max-value-size-128,ekv/scratch-page-count-4,ekv/align-1
    ekv/page-size-256,ekv/max-page-count-256,ekv/max-value-size-1024,ekv/scratch-page-count-8,ekv/align-2
    ekv/page-size-256,ekv/max-page-count-256,ekv/max-value-size-1024,ekv/scratch-page-count-8,ekv/align-4
    ekv/page-size-4096,ekv/max-page-count-256,ekv/max-chunk-size-512,ekv/max-value-size-1024,ekv/scratch-page-count-4,ekv/crc,ekv/align-4
    ekv/page-size-1024,ekv/max-page-count-16,ekv/max-value-size-16,ekv/scratch-page-count-0
    ekv/page-size-128,ekv/max-page-count-32,ekv/max-value-size-16,ekv/scratch-page-count-0
    ekv/page-size-128,ekv/max-page-count-32,ekv/max-value-size-16,ekv/scratch-page-count-0,ekv/crc
)

for FEATURES in ${FEATURESET[@]}; do
    cargo test --release --features $FEATURES
    cargo clippy --features $FEATURES

    # Run `file` fuzzer
    cargo fuzz run --sanitizer none -j$(nproc) file --features $FEATURES -- -max_total_time=30

    # Run `ops` fuzzer
    cargo fuzz run --sanitizer none -j$(nproc) ops --features $FEATURES -- -max_total_time=30

    # Run `read` fuzzer. Seed it with a flash image with stuff in it.
    cargo run --release --example smoke --features $FEATURES
    rm -rf fuzz/corpus/read
    mkdir -p fuzz/corpus/read
    mv out.bin fuzz/corpus/read
    cargo fuzz run --sanitizer none -j$(nproc) read --features $FEATURES -- -max_total_time=30
done

(cd examples/nrf; cargo fmt --check; cargo build --release --features defmt)
(cd examples/rp2040; cargo fmt --check; cargo build --release)

#!/bin/bash

set -euxo pipefail

CPUS=32
FEATURES=ekv/page-size-128,ekv/max-page-count-32,ekv/max-value-size-16,ekv/scratch-page-count-0

rm -rf fuzz/corpus
mkdir -p fuzz/corpus/read

rm -f fuzz/corpus/read/*
cargo run --release --example smoke --features $FEATURES
mv out.bin fuzz/corpus/read
cargo fuzz run --sanitizer none -j$CPUS read --features $FEATURES

#cargo fuzz run --sanitizer none ops --features ekv/page-size-128,ekv/max-page-count-128
#cargo fuzz run --sanitizer none ops --features ekv/page-size-128,ekv/max-page-count-32,ekv/max-value-size-16,ekv/scratch-page-count-0
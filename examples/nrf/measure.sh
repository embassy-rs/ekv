#!/bin/bash

set -euo pipefail
cd $(dirname $0)

cargo build --release
probe-run --chip nRF52840_xxAA target/thumbv7em-none-eabi/release/ekv-nrf-example --measure-stack 2>&1 | grep 'of stack space'
arm-none-eabi-size target/thumbv7em-none-eabi/release/ekv-nrf-example
stack-sizes target/thumbv7em-none-eabi/release/ekv-nrf-example | sort -k2,2n | tac | head -n 15
arm-none-eabi-objdump -x target/thumbv7em-none-eabi/release/ekv-nrf-example > dump.txt
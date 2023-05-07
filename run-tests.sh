#!/bin/bash
set -e -x

cargo +stable test --target-dir=target-stable \
    -p mvbitfield \
    -p mvbitfield-macros

cargo +stable doc --target-dir=target-stable -p mvbitfield --no-deps

cargo +nightly test --target-dir=target-nightly \
    --all-features \
    -p mvbitfield \
    -p mvbitfield-macros

cargo +nightly doc --target-dir=target-nightly --all-features -p mvbitfield --no-deps

cargo +nightly miri test --target-dir=target-nightly \
    -p mvbitfield

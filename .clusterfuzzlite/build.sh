#!/bin/bash -eu
# SPDX-License-Identifier: MPL-2.0
cd "$SRC"/echidna
cargo +nightly fuzz build
for target in $(cargo +nightly fuzz list); do
    cp ./target/x86_64-unknown-linux-gnu/release/$target $OUT/
done

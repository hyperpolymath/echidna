#!/bin/bash -eu
# SPDX-License-Identifier: MPL-2.0
cd "$SRC"/echidna
cargo +nightly fuzz build
# `fuzz` is excluded from the workspace (`Cargo.toml:154-157`), so
# cargo-fuzz writes artefacts into the fuzz crate's own target dir
# (`fuzz/target/<TRIPLE>/release/`) rather than the workspace
# `./target/`. cp from the correct path or every iteration of the
# loop fails with `cp: cannot stat …/target/x86_64-…/release/<bin>`
# and bash -eu exits on the first miss (echidna#143).
for target in $(cargo +nightly fuzz list); do
    cp ./fuzz/target/x86_64-unknown-linux-gnu/release/$target $OUT/
done

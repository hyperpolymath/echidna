# SPDX-License-Identifier: MPL-2.0
# Imported by the root Justfile (hotspot split); recipes moved verbatim.

# ── Creusot formal verification (Stage 8c) ──────────────────

# Run Creusot formal verification on the trust-pipeline kernel.
#
# Prerequisites: Creusot + Why3 + Z3/CVC5 (see crates/echidna-core-creusot/CREUSOT-SETUP.adoc).
# The nightly pin lives in crates/echidna-core-creusot/rust-toolchain.toml.
#
# This recipe is currently in report-only mode: CI runs it and posts
# results but does not block the merge until Stage 8c-M3.
verify-trust-pipeline:
    @echo "Running Creusot formal verification on echidna-core-creusot..."
    cargo +nightly creusot \
        -p echidna-core-creusot \
        -- \
        --features creusot \
        --why3 "$(which why3)"
    @echo "Creusot obligations discharged. See Why3 output above."

# Stable-Rust test suite for the Creusot-annotated trust pipeline.
# Runs on any Rust version; does not require Creusot or Why3.
test-trust-pipeline:
    cargo test -p echidna-core-creusot
    @echo "Trust-pipeline invariant tests passed ($(cargo test -p echidna-core-creusot 2>&1 | grep 'test result' | head -1 | grep -oP '\d+ passed') tests)."

# SPDX-License-Identifier: MPL-2.0
# Imported by the root Justfile (hotspot split); recipes moved verbatim.

# Build debug
build:
    cargo build

# Build release
build-release:
    cargo build --release

# Run unit tests
test:
    cargo test --lib

# Self-test the wave gates (scripts/gates/*.selftest.sh): fixtures, no network
test-gates:
    bash scripts/gates/lib.selftest.sh
    bash scripts/gates/w0.selftest.sh

# Run all tests (unit + integration)
test-all:
    cargo test

# Run tests verbose
test-verbose:
    cargo test -- --nocapture

# Run integration tests only
test-integration:
    cargo test --test integration_tests

# Run neural integration tests (requires Julia server)
test-neural:
    ./scripts/test-integration.sh

# Run the S4 loop-closure integration test against a VeriSimDB instance.
# Skips with a notice when VeriSimDB is unreachable (no failure).
# Set VERISIM_URL to override the default of http://localhost:8080.
#
# Local dev: start verisim-api beforehand (see docs/runbooks/s4-loop-closure.md);
# the test will exercise the full record_proof_attempt → query_by_goal_hash loop.
test-s4-loop:
    @echo "Running S4 loop-closure test against ${VERISIM_URL:-http://localhost:8080}"
    @echo "Test will skip cleanly if the endpoint is unreachable."
    cargo test --features verisim --test s4_loop_closure -- --nocapture

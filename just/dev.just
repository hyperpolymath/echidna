# SPDX-License-Identifier: MPL-2.0
# Imported by the root Justfile (hotspot split); recipes moved verbatim.

# Format code
fmt:
    cargo fmt

# Check formatting
fmt-check:
    cargo fmt -- --check

# Run clippy lints
lint:
    cargo clippy -- -D warnings

# Check without building
check:
    cargo check

# Clean build artifacts
clean:
    cargo clean

# Run the project
run *ARGS:
    cargo run -- {{ARGS}}

# Run Invariant Path overlay tools for this repository
invariant-path *ARGS:
    ./scripts/invariant-path.sh {{ARGS}}

# Rebuild the canonical seed vocabulary (training_data/vocabulary_CANON.txt).
# Two stages: (1) mine frequency-filtered identifiers from the per-prover
# proof corpora, then (2) union with the hand-curated sets. Consumed by
# src/julia/training/dataloader.jl:build_vocabulary_from_data.
vocab-canon:
    julia scripts/vocabulary_mine_corpus.jl
    julia scripts/vocabulary_canonicalize.jl

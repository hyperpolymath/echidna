# echidna - Rust Development Tasks
set shell := ["bash", "-uc"]
set dotenv-load := true

project := "echidna"

# Show all recipes
default:
    @just --list --unsorted

# Build debug
build:
    cargo build

# Build release
build-release:
    cargo build --release

# Run unit tests
test:
    cargo test --lib

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

# Generate docs
doc:
    cargo doc --no-deps --open

# Update dependencies
update:
    cargo update

# Audit dependencies
audit:
    cargo audit

# All checks before commit
pre-commit: fmt-check lint test
    @echo "All checks passed!"

# MVP 1.0 smoke checks
mvp:
    ./scripts/mvp-smoke.sh

# MVP 1.0 dependency checklist (best-effort)
mvp-env:
    ./scripts/mvp-smoke.sh || true

# Build minimal container image (Z3, CVC5, Lean, Idris2)
container-build:
    podman build -f .containerization/Containerfile -t echidna:latest .

# Build full container image (all provers + Julia)
container-build-full:
    podman build -f .containerization/Containerfile.full -t echidna:full .

# Run echidna container
container-run *ARGS:
    podman run --rm -it echidna:latest {{ARGS}}

# ── Chapel Accelerator ──────────────────────────────────────

# Build Zig FFI bridge for Chapel (prerequisite for --features chapel)
build-chapel-ffi:
    @echo "Building Zig FFI bridge..."
    cd src/zig_ffi && zig build -Doptimize=ReleaseSafe
    @echo "Library built at src/zig_ffi/zig-out/lib/"

# Build Chapel PoC (requires Chapel compiler)
build-chapel-poc:
    @echo "Building Chapel proof-of-concept..."
    cd chapel_poc && chpl parallel_proof_search.chpl -o proof_search --fast
    @echo "Built chapel_poc/proof_search"

# Run Chapel PoC benchmark
run-chapel-poc:
    cd chapel_poc && ./proof_search

# Build with Chapel support enabled (requires Zig FFI built first)
build-chapel: build-chapel-ffi
    cargo build --features chapel

# Test Chapel integration
test-chapel: build-chapel-ffi
    cargo test --features chapel -- proof_search

# Test Zig FFI bridge independently
test-chapel-ffi:
    cd src/zig_ffi && zig build test

# Full Chapel build + test
chapel-all: build-chapel-poc build-chapel-ffi test-chapel
    @echo "Chapel accelerator fully built and tested"

# ── Other ───────────────────────────────────────────────────

# [AUTO-GENERATED] Multi-arch / RISC-V target
build-riscv:
	@echo "Building for RISC-V..."
	cross build --target riscv64gc-unknown-linux-gnu

# Run panic-attacker pre-commit scan
assail:
    @command -v panic-attack >/dev/null 2>&1 && panic-attack assail . || echo "panic-attack not found — install from https://github.com/hyperpolymath/panic-attacker"

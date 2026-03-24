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

# ── Onboarding ────────────────────────────────────────────────

# Check that all required tools are installed and working
doctor:
    #!/usr/bin/env bash
    set -euo pipefail
    PASS=0; FAIL=0; WARN=0
    check() {
        local name="$1" cmd="$2"
        if command -v "$cmd" >/dev/null 2>&1; then
            ver=$("$cmd" --version 2>/dev/null | head -1 || echo "unknown")
            echo "  [OK] $name: $ver"
            PASS=$((PASS + 1))
        else
            echo "  [FAIL] $name: '$cmd' not found"
            FAIL=$((FAIL + 1))
        fi
    }
    check_optional() {
        local name="$1" cmd="$2"
        if command -v "$cmd" >/dev/null 2>&1; then
            ver=$("$cmd" --version 2>/dev/null | head -1 || echo "unknown")
            echo "  [OK] $name: $ver"
            PASS=$((PASS + 1))
        else
            echo "  [WARN] $name: '$cmd' not found (optional)"
            WARN=$((WARN + 1))
        fi
    }
    echo "=== echidna: Doctor ==="
    echo ""
    echo "Required tools:"
    check "Rust/cargo" "cargo"
    check "just" "just"
    check "pkg-config" "pkg-config"
    # Check openssl headers
    if pkg-config --exists openssl 2>/dev/null; then
        echo "  [OK] openssl-devel: $(pkg-config --modversion openssl)"
        PASS=$((PASS + 1))
    else
        echo "  [FAIL] openssl-devel: not found (install openssl-devel or libssl-dev)"
        FAIL=$((FAIL + 1))
    fi
    echo ""
    echo "Optional tools (full stack):"
    check_optional "Podman" "podman"
    check_optional "Idris2" "idris2"
    check_optional "Zig" "zig"
    check_optional "Julia" "julia"
    check_optional "Deno" "deno"
    check_optional "Chapel" "chpl"
    check_optional "panic-attack" "panic-attack"
    echo ""
    echo "Prover backends (spot check):"
    check_optional "Z3" "z3"
    check_optional "CVC5" "cvc5"
    echo ""
    echo "Build artefacts:"
    if [ -f "target/debug/echidna" ] || [ -f "target/release/echidna" ]; then
        echo "  [OK] echidna binary built"
    else
        echo "  [INFO] echidna not built — run 'just build'"
    fi
    echo ""
    echo "=== Results: $PASS passed, $FAIL failed, $WARN warnings ==="
    if [ "$FAIL" -gt 0 ]; then
        echo "Run 'just heal' for install instructions."
        exit 1
    fi

# Show install instructions for missing tools
heal:
    #!/usr/bin/env bash
    set -euo pipefail
    echo "=== echidna: Heal ==="
    echo ""
    echo "Install missing tools:"
    echo ""
    if ! command -v cargo >/dev/null 2>&1; then
        echo "  Rust (REQUIRED):"
        echo "    asdf install rust nightly"
        echo "    # Or: curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh"
        echo ""
    fi
    if ! pkg-config --exists openssl 2>/dev/null; then
        echo "  OpenSSL development headers (REQUIRED):"
        echo "    Fedora: sudo dnf install openssl-devel pkg-config"
        echo "    Ubuntu: sudo apt install libssl-dev pkg-config"
        echo ""
    fi
    if ! command -v podman >/dev/null 2>&1; then
        echo "  Podman (for containers):"
        echo "    Fedora: sudo dnf install podman"
        echo "    Ubuntu: sudo apt install podman"
        echo ""
    fi
    if ! command -v idris2 >/dev/null 2>&1; then
        echo "  Idris2 (for ABI layer):"
        echo "    Install via pack: https://github.com/stefan-hoeck/idris2-pack"
        echo ""
    fi
    if ! command -v zig >/dev/null 2>&1; then
        echo "  Zig (for FFI bridge):"
        echo "    asdf plugin add zig && asdf install zig 0.13.0"
        echo ""
    fi
    if ! command -v julia >/dev/null 2>&1; then
        echo "  Julia (for ML layer):"
        echo "    asdf plugin add julia && asdf install julia latest"
        echo ""
    fi
    if ! command -v z3 >/dev/null 2>&1; then
        echo "  Z3 (SMT solver):"
        echo "    Fedora: sudo dnf install z3"
        echo "    Ubuntu: sudo apt install z3"
        echo ""
    fi
    if ! command -v panic-attack >/dev/null 2>&1; then
        echo "  panic-attack (pre-commit scans):"
        echo "    cargo install --git https://github.com/hyperpolymath/panic-attacker"
        echo ""
    fi
    echo "After installing, run 'just doctor' to verify."

# Guided tour of the repository structure
tour:
    #!/usr/bin/env bash
    set -euo pipefail
    echo "=== ECHIDNA: Guided Tour ==="
    echo ""
    echo "ECHIDNA is a neurosymbolic theorem proving platform with 48 prover backends."
    echo ""
    echo "1. RUST CORE: src/rust/"
    echo "   The main implementation. 48 prover backends, trust pipeline, CLI, REPL."
    echo "     src/rust/main.rs          - CLI entry point"
    echo "     src/rust/repl.rs          - Interactive REPL"
    echo "     src/rust/server.rs        - HTTP API server"
    echo "     src/rust/provers/         - 30 prover backend implementations"
    echo "     src/rust/verification/    - Trust pipeline (portfolio, certificates, axioms)"
    echo "     src/rust/integrity/       - Solver binary integrity (SHAKE3-512, BLAKE3)"
    echo "     src/rust/executor/        - Sandboxed execution (Podman, bubblewrap)"
    echo "     src/rust/exchange/        - Cross-prover proof exchange"
    echo "     src/rust/agent/           - Agentic proof search (actor model)"
    echo ""
    echo "2. API INTERFACES: src/interfaces/"
    echo "     graphql/   - async-graphql (port 8080)"
    echo "     grpc/      - tonic gRPC (port 50051)"
    echo "     rest/       - axum + OpenAPI (port 8000)"
    echo ""
    echo "3. ML LAYER: src/julia/"
    echo "   Julia-based tactic prediction and premise selection."
    echo ""
    echo "4. ABI/FFI:"
    echo "     src/abi/   - Idris2 formal type definitions"
    echo "     ffi/zig/   - Zig FFI bridge (4 shared libraries)"
    echo ""
    echo "5. UI: src/rescript/"
    echo "   ReScript + Deno frontend (28 files)."
    echo ""
    echo "6. BUILD SYSTEM:"
    echo "   Cargo.toml   - Rust workspace"
    echo "   Justfile      - Primary build system"
    echo "   guix.scm      - Guix package definition"
    echo "   flake.nix      - Nix flake"
    echo ""
    echo "Try: just build       (compile Rust core)"
    echo "     just test        (run 232 unit tests)"
    echo "     just run repl    (interactive theorem prover)"

# Show available recipes with descriptions
help-me:
    #!/usr/bin/env bash
    echo "=== ECHIDNA: Help ==="
    echo ""
    echo "Onboarding:"
    echo "  just doctor          - Check required tools are installed"
    echo "  just heal            - Show install instructions for missing tools"
    echo "  just tour            - Guided walkthrough of repo structure"
    echo "  just help-me         - This help message"
    echo ""
    echo "Build:"
    echo "  just build           - Build debug binary"
    echo "  just build-release   - Build optimised release binary"
    echo "  just build-riscv     - Cross-compile for RISC-V"
    echo ""
    echo "Testing:"
    echo "  just test            - Run unit tests (232)"
    echo "  just test-all        - Run all tests (389)"
    echo "  just test-verbose    - Run tests with output"
    echo "  just test-integration - Integration tests only"
    echo "  just test-neural     - Neural integration tests (requires Julia)"
    echo ""
    echo "Quality:"
    echo "  just fmt             - Format code"
    echo "  just fmt-check       - Check formatting"
    echo "  just lint            - Run clippy lints"
    echo "  just check           - Cargo check (fast)"
    echo "  just pre-commit      - Full pre-commit checks"
    echo "  just assail          - panic-attacker scan"
    echo ""
    echo "Running:"
    echo "  just run repl        - Interactive REPL"
    echo "  just run serve       - Start API server"
    echo "  just run prove <f>   - Prove a file"
    echo ""
    echo "Containers:"
    echo "  just container-build      - Minimal image"
    echo "  just container-build-full - Full image (all provers)"
    echo "  just container-run        - Run container"
    echo ""
    echo "Chapel accelerator:"
    echo "  just chapel-all      - Build + test Chapel layer"
    echo ""
    echo "Housekeeping:"
    echo "  just clean           - Remove build artefacts"
    echo "  just doc             - Generate and open docs"
    echo "  just update          - Update dependencies"
    echo "  just audit           - Audit dependencies"

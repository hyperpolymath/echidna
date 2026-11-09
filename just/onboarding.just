# SPDX-License-Identifier: MPL-2.0
# Imported by the root Justfile (hotspot split); recipes moved verbatim.

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
    check_optional "Bun" "bun"
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
    echo "     graphql/   - async-graphql (port 8082)"
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
    echo "5. UI: src/ui/"
    echo "   AffineScript-TEA (src/ui/tea/) + static shell (src/ui/public/)."
    echo ""
    echo "6. BUILD SYSTEM:"
    echo "   Cargo.toml   - Rust workspace"
    echo "   Justfile      - Primary build system"
    echo "   guix.scm      - Guix package definition (PRIMARY; no Guix mirror — estate ruling 2026-05-18)"
    echo "   .containerization/Containerfile.wave3 - sealed-container escape hatch (Tier-3 provers)"
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
    echo "  just container-build          - Minimal image"
    echo "  just container-build-full     - Full image (all provers)"
    echo "  just container-build-tier3    - All Wave-3 prover images (except imandra)"
    echo "  just container-build-tamarin  - Tamarin security protocol prover"
    echo "  just container-build-proverif - ProVerif cryptographic protocol verifier"
    echo "  just container-build-metamath - Metamath (pure-Rust in-process + bundled databases)"
    echo "  just container-build-twelf    - Twelf LF meta-logical framework"
    echo "  just container-build-or-tools - OR-Tools combinatorial optimisation C++ library"
    echo "  just container-build-scip     - SCIP constraint integer programming solver"
    echo "  just container-build-hol4     - HOL4 (Poly/ML build, slow)"
    echo "  just container-build-acl2     - ACL2 (SBCL build, slow)"
    echo "  just container-build-imandra  - Imandra stub (proprietary licence required)"
    echo "  just container-run            - Run container"
    echo ""
    echo "Chapel accelerator:"
    echo "  just chapel-all      - Build + test Chapel layer"
    echo ""
    echo "Housekeeping:"
    echo "  just clean           - Remove build artefacts"
    echo "  just doc             - Generate and open docs"
    echo "  just update          - Update dependencies"
    echo "  just audit           - Audit dependencies"


# Print the current CRG grade (reads from READINESS.md '**Current Grade:** X' line)
crg-grade:
    @grade=$$(grep -oP '(?<=\*\*Current Grade:\*\* )[A-FX]' READINESS.md 2>/dev/null | head -1); \
    [ -z "$$grade" ] && grade="X"; \
    echo "$$grade"

# Generate a shields.io badge markdown for the current CRG grade
# Looks for '**Current Grade:** X' in READINESS.md; falls back to X
crg-badge:
    @grade=$$(grep -oP '(?<=\*\*Current Grade:\*\* )[A-FX]' READINESS.md 2>/dev/null | head -1); \
    [ -z "$$grade" ] && grade="X"; \
    case "$$grade" in \
      A) color="brightgreen" ;; B) color="green" ;; C) color="yellow" ;; \
      D) color="orange" ;; E) color="red" ;; F) color="critical" ;; \
      *) color="lightgrey" ;; esac; \
    echo "[![CRG $$grade](https://img.shields.io/badge/CRG-$$grade-$$color?style=flat-square)](https://github.com/hyperpolymath/standards/tree/main/component-readiness-grades)"

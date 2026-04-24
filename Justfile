# echidna - Rust Development Tasks
set shell := ["bash", "-uc"]
set dotenv-load := true

import? "contractile.just"

project := "echidna"

# Show all recipes
default:
    @just --list --unsorted

# Initialize from RSR template (placeholder replacement)
init:
    #!/usr/bin/env bash
    set -euo pipefail

    echo "═══════════════════════════════════════════════════"
    echo "  RSR Project Bootstrap"
    echo "═══════════════════════════════════════════════════"
    echo ""

    # --- Load defaults from config (if exists) ---
    # Create yours: ~/.config/rsr/defaults
    # Format: OWNER=myorg  AUTHOR="My Name"  AUTHOR_EMAIL=me@example.org ...
    DEFAULTS="${XDG_CONFIG_HOME:-$HOME/.config}/rsr/defaults"
    if [ -f "$DEFAULTS" ]; then
        echo "Loading defaults from $DEFAULTS"
        # shellcheck source=/dev/null
        source "$DEFAULTS"
        echo ""
    fi

    # --- Required values (pre-filled from defaults if available) ---
    read -rp "Project name (human-readable, e.g. My Project): " PROJECT_NAME
    [ -z "$PROJECT_NAME" ] && echo "Error: project name required" && exit 1

    read -rp "Repository slug (e.g. my-project): " REPO
    [ -z "$REPO" ] && echo "Error: repo slug required" && exit 1

    read -rp "Owner [${OWNER:-}]: " _OWNER
    OWNER="${_OWNER:-${OWNER:-}}"
    [ -z "$OWNER" ] && echo "Error: owner required" && exit 1

    read -rp "Author full name [${AUTHOR:-}]: " _AUTHOR
    AUTHOR="${_AUTHOR:-${AUTHOR:-}}"
    [ -z "$AUTHOR" ] && echo "Error: author name required" && exit 1

    read -rp "Author email [${AUTHOR_EMAIL:-}]: " _AUTHOR_EMAIL
    AUTHOR_EMAIL="${_AUTHOR_EMAIL:-${AUTHOR_EMAIL:-}}"
    [ -z "$AUTHOR_EMAIL" ] && echo "Error: email required" && exit 1

    # --- Optional values (pre-filled from defaults if available) ---
    read -rp "Author organization [${AUTHOR_ORG:-none}]: " _AUTHOR_ORG
    AUTHOR_ORG="${_AUTHOR_ORG:-${AUTHOR_ORG:-}}"

    read -rp "Previous/alt email [${AUTHOR_EMAIL_ALT:-none}]: " _AUTHOR_EMAIL_ALT
    AUTHOR_EMAIL_ALT="${_AUTHOR_EMAIL_ALT:-${AUTHOR_EMAIL_ALT:-}}"

    read -rp "Project description []: " PROJECT_DESCRIPTION

    read -rp "Forge domain [${FORGE:-github.com}]: " _FORGE
    FORGE="${_FORGE:-${FORGE:-github.com}}"

    read -rp "Security contact email [${SECURITY_EMAIL:-$AUTHOR_EMAIL}]: " _SECURITY_EMAIL
    SECURITY_EMAIL="${_SECURITY_EMAIL:-${SECURITY_EMAIL:-$AUTHOR_EMAIL}}"

    read -rp "Conduct contact email [${CONDUCT_EMAIL:-$AUTHOR_EMAIL}]: " _CONDUCT_EMAIL
    CONDUCT_EMAIL="${_CONDUCT_EMAIL:-${CONDUCT_EMAIL:-$AUTHOR_EMAIL}}"

    read -rp "Project type (library|binary|monorepo|service|website) [library]: " PROJECT_TYPE
    PROJECT_TYPE="${PROJECT_TYPE:-library}"

    read -rp "Website URL [https://${FORGE}/${OWNER}/${REPO}]: " WEBSITE
    WEBSITE="${WEBSITE:-https://${FORGE}/${OWNER}/${REPO}}"

    # --- Container values (optional — only relevant if container/ exists) ---
    if [ -d "container" ]; then
        echo ""
        echo "── Container configuration (optional) ─────────"
        read -rp "Service name [${REPO}]: " _SERVICE_NAME
        SERVICE_NAME="${_SERVICE_NAME:-${REPO}}"
        read -rp "Primary port [8080]: " _PORT
        PORT="${_PORT:-8080}"
        read -rp "Container registry [ghcr.io/${OWNER}]: " _REGISTRY
        REGISTRY="${_REGISTRY:-ghcr.io/${OWNER}}"
    else
        SERVICE_NAME="${REPO}"
        PORT="8080"
        REGISTRY="ghcr.io/${OWNER}"
    fi

    # --- Derived values ---
    PROJECT_UPPER=$(echo "$REPO" | tr '[:lower:]-' '[:upper:]_')
    PROJECT_LOWER=$(echo "$REPO" | tr '[:upper:]-' '[:lower:]_')
    CURRENT_YEAR=$(date +%Y)
    CURRENT_DATE=$(date +%Y-%m-%d)
    VERSION="0.1.0"

    # Derive citation name parts (best-effort split on last space)
    AUTHOR_LAST="${AUTHOR##* }"
    AUTHOR_FIRST="${AUTHOR% *}"
    FIRST_INITIAL="${AUTHOR_FIRST:0:1}."
    if [ "$AUTHOR_LAST" = "$AUTHOR_FIRST" ]; then
        AUTHOR_FIRST="$AUTHOR"
        AUTHOR_LAST=""
        FIRST_INITIAL=""
    fi

    echo ""
    echo "── Summary ──────────────────────────────────────"
    echo "  Project:     $PROJECT_NAME"
    echo "  Repo:        $REPO"
    echo "  Owner:       $OWNER"
    echo "  Author:      $AUTHOR <$AUTHOR_EMAIL>"
    [ -n "$AUTHOR_ORG" ] && echo "  Organization: $AUTHOR_ORG"
    echo "  Forge:       $FORGE"
    echo "  Year:        $CURRENT_YEAR"
    echo "────────────────────────────────────────────────"
    echo ""
    read -rp "Proceed? [Y/n] " CONFIRM
    [[ "${CONFIRM:-Y}" =~ ^[Nn] ]] && echo "Aborted." && exit 0

    echo ""
    echo "Replacing placeholders..."

    # Brace tokens as variables (hex avoids just interpolation)
    LB=$(printf '\x7b\x7b')
    RB=$(printf '\x7d\x7d')

    # Build the sed expression list
    # Note: using | as delimiter since URLs contain /
    SED_ARGS=(
        -e "s|${LB}PROJECT_NAME${RB}|${PROJECT_NAME}|g"
        -e "s|${LB}PROJECT_DESCRIPTION${RB}|${PROJECT_DESCRIPTION}|g"
        -e "s|${LB}PROJECT${RB}|${PROJECT_UPPER}|g"
        -e "s|${LB}project${RB}|${PROJECT_LOWER}|g"
        -e "s|${LB}REPO${RB}|${REPO}|g"
        -e "s|${LB}OWNER${RB}|${OWNER}|g"
        -e "s|${LB}AUTHOR${RB}|${AUTHOR}|g"
        -e "s|${LB}AUTHOR_EMAIL${RB}|${AUTHOR_EMAIL}|g"
        -e "s|${LB}AUTHOR_ORG${RB}|${AUTHOR_ORG}|g"
        -e "s|${LB}AUTHOR_LAST${RB}|${AUTHOR_LAST}|g"
        -e "s|${LB}AUTHOR_FIRST${RB}|${AUTHOR_FIRST}|g"
        -e "s|${LB}AUTHOR_INITIALS${RB}|${FIRST_INITIAL}|g"
        -e "s|${LB}FORGE${RB}|${FORGE}|g"
        -e "s|${LB}CURRENT_YEAR${RB}|${CURRENT_YEAR}|g"
        -e "s|${LB}CURRENT_DATE${RB}|${CURRENT_DATE}|g"
        -e "s|${LB}DATE${RB}|${CURRENT_DATE}|g"
        -e "s|${LB}SECURITY_EMAIL${RB}|${SECURITY_EMAIL}|g"
        -e "s|${LB}CONDUCT_EMAIL${RB}|${CONDUCT_EMAIL}|g"
        -e "s|${LB}LICENSE${RB}|PMPL-1.0-or-later|g"
        -e "s|${LB}CONDUCT_TEAM${RB}|Code of Conduct Committee|g"
        -e "s|${LB}RESPONSE_TIME${RB}|48 hours|g"
        -e "s|${LB}MAIN_BRANCH${RB}|main|g"
        -e "s|${LB}PROJECT_PURPOSE${RB}|${PROJECT_DESCRIPTION}|g"
        -e "s|${LB}PROJECT_ROLE${RB}|${PROJECT_TYPE}|g"
        -e "s|${LB}PROJECT_TYPE${RB}|${PROJECT_TYPE}|g"
        -e "s|${LB}WEBSITE${RB}|${WEBSITE}|g"
        -e "s|${LB}SERVICE_NAME${RB}|${SERVICE_NAME}|g"
        -e "s|${LB}PORT${RB}|${PORT}|g"
        -e "s|${LB}REGISTRY${RB}|${REGISTRY}|g"
        -e "s|${LB}IMAGE${RB}|${REGISTRY}/${SERVICE_NAME}|g"
        -e "s|${LB}VERSION${RB}|${VERSION}|g"
        -e "s|${LB}EMAIL${RB}|${AUTHOR_EMAIL}|g"
    )
    [ -n "$AUTHOR_EMAIL_ALT" ] && SED_ARGS+=(-e "s|${LB}AUTHOR_EMAIL_ALT${RB}|${AUTHOR_EMAIL_ALT}|g")

    # Replace in all text files (skip .git, LICENSE text, and binaries)
    find . -type f \
        -not -path './.git/*' \
        -not -name 'PMPL-1.0-or-later.txt' \
        -not -name '*.png' -not -name '*.jpg' -not -name '*.gif' \
        -not -name '*.woff' -not -name '*.woff2' \
        | while read -r file; do
        if file --brief "$file" | grep -qi 'text\|ascii\|utf'; then
            sed -i "${SED_ARGS[@]}" "$file"
        fi
    done

    # Also replace [YOUR-REPO-NAME] and [YOUR-NAME/ORG] in AI manifest
    sed -i "s|\[YOUR-REPO-NAME\]|${PROJECT_NAME}|g" 0-AI-MANIFEST.a2ml 2>/dev/null || true
    sed -i "s|\[YOUR-NAME/ORG\]|${OWNER}|g" 0-AI-MANIFEST.a2ml 2>/dev/null || true

    echo ""
    echo "── Validation ───────────────────────────────────"

    # Check for remaining placeholders
    PATTERN="${LB}[A-Z_]*${RB}"
    REMAINING=$(grep -rl "$PATTERN" . --include='*.md' --include='*.adoc' --include='*.yml' --include='*.yaml' --include='*.a2ml' --include='*.toml' --include='*.scm' --include='*.ncl' --include='*.nix' --include='*.json' --include='*.sh' 2>/dev/null | grep -v '.git/' | grep -v '.machine_readable/ai/PLACEHOLDERS.adoc' || true)
    if [ -n "$REMAINING" ]; then
        echo "WARNING: Remaining placeholders in:"
        echo "$REMAINING" | sed 's/^/  /'
        echo ""
        echo "Run: grep -rn '$LB' . --include='*.md' to inspect"
    else
        echo "All placeholders replaced successfully!"
    fi

    echo ""
    echo "Done! Next steps:"
    echo "  1. Review changes: git diff"
    echo "  2. Remove template cruft: rm .machine_readable/ai/PLACEHOLDERS.adoc"
    echo "  3. Customize README.adoc for your project"
    echo "  4. Commit: git add -A && git commit -m 'feat: initialize from RSR template'"
    echo "  5. Push: git remote add origin git@github.com:{{OWNER}}/{{REPO}}.git && git push -u origin main"

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

# ── Corpus / training pipeline ─────────────────────────────────
#
# Five steps in order: provision upstream mirrors, run every extractor,
# merge per-prover proof_states into UNIFIED, align the premise files
# to UNIFIED's fresh ids, then retrain.  Each step is idempotent;
# re-running only touches what has changed.  See
# scripts/provision_corpora.sh --list for the source catalogue.

# Clone every upstream prover corpus into external_corpora/.
# Pass specific names to provision a subset: `just provision-corpora metamath mathlib4`.
provision-corpora *NAMES:
    @if [ -z "{{NAMES}}" ]; then \
        scripts/provision_corpora.sh --all; \
    else \
        scripts/provision_corpora.sh {{NAMES}}; \
    fi

# Report which upstream corpora are on disk and their sizes.
corpora-status:
    scripts/provision_corpora.sh --status

# Run every scripts/extract_*.jl against the provisioned corpora.
# Pass names to run a subset: `just extract-corpora metamath mathlib4`.
extract-corpora *NAMES:
    scripts/extract_all.sh {{NAMES}}

# Merge per-prover proof_states_*.jsonl into proof_states_UNIFIED.jsonl
# with fresh sequential ids (dedupes by prover+theorem).
merge-corpora:
    julia --project=src/julia scripts/merge_corpus.jl

# Rebuild premises_COMPLETE.jsonl with proof_ids that match UNIFIED.
# merge-corpora rewrites every proof_state id to a fresh sequential
# counter; the premise files keep the original extractor ids, so this
# step re-joins premises to UNIFIED via (prover, theorem) — the durable
# key merge_corpus.jl already dedupes on.  Without this step the
# dataloader's proof_id join matches ~0% of records.
align-premises:
    julia --project=src/julia scripts/align_premises.jl

# Full retrain from provisioned corpora.  Honours ECHIDNA_MAX_PROOF_STATES
# (0 = unlimited), ECHIDNA_NUM_EPOCHS, ECHIDNA_NUM_NEGATIVES.
#
# Depends on align-premises: without that step the dataloader joins
# premise.proof_id against proof_state.id and fails at ~0% match because
# merge_corpus.jl rewrites proof_state ids to fresh sequential counters
# while the premise files keep the original per-extractor ids.  Running
# align-premises is idempotent and cheap (seconds on a 2M premise set).
retrain: align-premises
    julia --project=src/julia src/julia/run_training.jl

# Retrain without the align-premises prerequisite — use only when you
# know premises_COMPLETE.jsonl is already aligned (e.g. you just ran
# just align-premises manually and want to iterate on model code).
retrain-skip-align:
    julia --project=src/julia src/julia/run_training.jl

# End-to-end pipeline: provision → extract → merge → align → retrain.
# Use `ECHIDNA_MAX_PROOF_STATES=0 just corpus-refresh` to lift the sample cap.
corpus-refresh: provision-corpora extract-corpora merge-corpora align-premises retrain

# Run the eight-axis metrics suite against the current corpus and post
# results to VeriSimDB. Falls back to training_data/metrics_<run_id>.jsonl
# if VERISIM_URL is unreachable. Target values are documented in
# metrics/README.md.
metrics:
    julia --project=src/julia metrics/run_all.jl

# Report corpus balance across provers from stats_UNIFIED.json.
corpus-stats:
    @julia -e 'using JSON3, Printf; \
      s = JSON3.read(read("training_data/stats_UNIFIED.json", String)); \
      counts = s.per_prover_counts; \
      pairs = sort(collect(counts), by = x -> -x[2]); \
      total = sum(last.(pairs)); \
      println("Total proofs: ", total, "   provers with data: ", length(pairs)); \
      println("Rank  Prover                     Count    Share"); \
      for (i,(p,c)) in enumerate(pairs); \
          @printf("%3d   %-25s  %7d   %5.2f%%\n", i, p, c, 100c/total); \
      end'

# Generate docs
doc:
    cargo doc --no-deps --open

# Update dependencies
update:
    cargo update

# Audit dependencies
audit:
    cargo audit

# ── UI Management ──────────────────────────────────────────

# Build ReScript frontend (Deno caches npm: deps automatically — no install step)
build-ui:
    cd src/rescript && deno task res:build && deno task build

# Start ReScript compiler in watch mode
watch-ui:
    cd src/rescript && deno task res:dev

# Start Deno dev server for UI
dev-ui:
    cd src/rescript && deno task dev

# Serve production UI build
serve-ui:
    cd src/rescript && deno task serve

# Launch full ECHIDNA GUI (Backend + UI + Browser)
gui:
    #!/usr/bin/env bash
    set -euo pipefail
    echo "Launching ECHIDNA GUI..."
    # Start backend
    cargo run -- server --port 8081 --cors > /dev/null 2>&1 & BACKEND_PID=$!
    echo "Started backend (PID $BACKEND_PID)"
    # Start UI server
    cd src/rescript && deno task serve > /dev/null 2>&1 & UI_PID=$!
    echo "Started UI server (PID $UI_PID)"
    # Cleanup on exit
    trap "kill $BACKEND_PID $UI_PID 2>/dev/null || true" EXIT
    # Wait for servers to start
    echo "Waiting for servers to initialize..."
    sleep 2
    # Open browser
    URL="http://localhost:3000"
    echo "Opening $URL..."
    xdg-open "$URL" > /dev/null 2>&1 || open "$URL" > /dev/null 2>&1 || echo "Please open $URL in your browser"
    echo "ECHIDNA GUI is running. Press Ctrl+C in this terminal to stop."
    # Wait for background processes
    wait

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
    echo "     graphql/   - async-graphql (port 8081)"
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
    echo "   ReScript + Deno frontend (33 files, zero TypeScript)."
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

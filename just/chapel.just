# SPDX-License-Identifier: MPL-2.0
# Imported by the root Justfile (hotspot split); recipes moved verbatim.

# ── Chapel Accelerator ──────────────────────────────────────

# Compile the Chapel metalayer into a static library.
# --static (not --dynamic) because the apt-shipped Chapel runtime is
# CHPL_LIB_PIC=none only; see .github/workflows/chapel-ci.yml for the
# longer explanation and #133 for the closure trace.
chapel-build:
    @echo "Compiling Chapel metalayer (static)..."
    cd src/chapel && chpl --library --static -I ../zig_ffi \
        -o libechidna_chapel \
        chapel_ffi_exports.chpl parallel_proof_search.chpl
    @echo "Built src/chapel/lib/libechidna_chapel.a"

# Build the Chapel "hello" smoke target — exercises coforall + atomic
# CAS + reduction. Used in CI as the toolchain-health signal.
chapel-smoke:
    cd src/chapel && chpl -o chapel_smoke smoke.chpl && ./chapel_smoke

# Run the Chapel-gated Rust tests (`--features chapel`).
chapel-test: build-chapel-ffi
    cargo test --locked --features chapel --lib -- proof_search verify_proof_parallel

# Speedup baseline: compares sequentialProofSearch /
# parallelProofSearch / parallelProofSearchSpeculative against the
# fixture corpus in tests/chapel_fixtures/. Emits CSV to stdout. Doc:
# docs/bench/2026-05-30-chapel-mrr-baseline.adoc.
#
# IDRIS2_PREFIX is derived from `which idris2` because Idris2's prelude
# resolution requires the env var to be set when invoking `--check`;
# the per-prover cwd hook (#158) sets the subprocess working dir but
# doesn't help if the parent never had the env var (see
# src/chapel/parallel_proof_search.chpl ProverInfo[4]). The derived
# prefix is `dirname(dirname(realpath(which idris2)))` — works for
# both source builds and asdf-shimmed installs.
bench-chapel-mrr:
    #!/usr/bin/env bash
    set -euo pipefail
    if command -v idris2 >/dev/null 2>&1 && [ -z "${IDRIS2_PREFIX:-}" ]; then
      export IDRIS2_PREFIX="$(dirname "$(dirname "$(readlink -f "$(command -v idris2)")")")"
      echo "# IDRIS2_PREFIX=$IDRIS2_PREFIX (derived from which idris2)" >&2
    fi
    cd src/chapel
    chpl -o bench_mrr bench_mrr.chpl
    ./bench_mrr --verbose=false --timeout=10
    echo "# wrote src/chapel/bench_mrr_telemetry.csv + src/chapel/bench_mrr_summary.csv" >&2

# Same bench, but surface only the corpus-level outcome breakdown: the
# per-prover preempted / timed-out / success counts and the preemption
# rate next to wall-clock, one line per strategy. This is the #162 view —
# it answers "how much of the speculative win is preemption?" without
# opening the 360-row telemetry file.
bench-chapel-mrr-telemetry:
    #!/usr/bin/env bash
    set -euo pipefail
    if command -v idris2 >/dev/null 2>&1 && [ -z "${IDRIS2_PREFIX:-}" ]; then
      export IDRIS2_PREFIX="$(dirname "$(dirname "$(readlink -f "$(command -v idris2)")")")"
    fi
    cd src/chapel
    chpl -o bench_mrr bench_mrr.chpl
    ./bench_mrr --verbose=false --timeout=10 --telemetry-only=true
    echo "corpus-level outcome breakdown (fixture=ALL):"
    grep '^ALL,' bench_mrr_summary.csv | while IFS=, read -r _ strategy att ok fail preempt timeout na err notatt rate wall _ _; do
      printf '  %-22s attempted=%-3s success=%-3s failure=%-3s preempted=%-3s timed_out=%-3s rate=%s wall=%ss\n' \
        "$strategy" "$att" "$ok" "$fail" "$preempt" "$timeout" "$rate" "$wall"
    done

# Rebuild Chapel 2.8.0 from source with CHPL_LIB_PIC=pic so that
# `chpl --library --dynamic` can produce a shared-library form of the
# metalayer. The apt deb ships only the `lib_pic-none` runtime
# variant. ~25-35 min wall on a 4-core x86_64. ~5 GB disk under
# ~/.cache/echidna/chapel-pic. Procedure + tradeoffs:
# docs/decisions/2026-05-30-chapel-pic-rebuild.adoc. NOT a CI step.
chapel-pic-from-source:
    #!/usr/bin/env bash
    set -euo pipefail
    CACHE_DIR="${ECHIDNA_CHAPEL_PIC_CACHE:-$HOME/.cache/echidna/chapel-pic}"
    CHPL_VERSION="${CHPL_VERSION:-2.8.0}"
    mkdir -p "$CACHE_DIR"
    cd "$CACHE_DIR"
    if [ ! -f "chapel-${CHPL_VERSION}.tar.gz" ]; then
      echo "Downloading chapel ${CHPL_VERSION}..."
      curl -fL "https://github.com/chapel-lang/chapel/releases/download/${CHPL_VERSION}/chapel-${CHPL_VERSION}.tar.gz" \
        -o "chapel-${CHPL_VERSION}.tar.gz"
    fi
    if [ ! -d "chapel-${CHPL_VERSION}" ]; then
      tar xf "chapel-${CHPL_VERSION}.tar.gz"
    fi
    cd "chapel-${CHPL_VERSION}"
    export CHPL_LIB_PIC=pic
    export CHPL_LLVM=bundled
    export CHPL_HOME="$PWD"
    source util/setchplenv.bash
    echo "Building chapel runtime with CHPL_LIB_PIC=pic (~30 min)..."
    make -j"$(nproc)"
    echo "Verifying lib_pic-pic variant landed..."
    if find lib -name 'lib_pic-pic' -type d | head -1 | grep -q .; then
      echo "OK: PIC runtime built at $CHPL_HOME"
      echo "Use:  PATH=$CHPL_HOME/bin/linux64-x86_64:\$PATH chpl --library --dynamic ..."
    else
      echo "ERROR: lib_pic-pic variant not found after build" >&2
      exit 1
    fi

# Build Zig FFI bridge for Chapel (prerequisite for --features chapel)
build-chapel-ffi:
    @echo "Building Zig FFI bridge..."
    cd src/zig_ffi && zig build -Doptimize=ReleaseSafe
    @echo "Library built at src/zig_ffi/zig-out/lib/"

# Build the feature against explicit unavailable stubs.
build-chapel: build-chapel-ffi
    ECHIDNA_CHAPEL_EXPECT_MODE=stubs cargo build --locked --features chapel

# Build the real static bridge and let Cargo consume Chapel's runtime closure.
build-chapel-real: chapel-build
    cd src/zig_ffi && zig build -Doptimize=ReleaseSafe -Dstubs=false
    ECHIDNA_CHAPEL_EXPECT_MODE=real cargo build --locked --features chapel

chapel-test-real: build-chapel-real
    ECHIDNA_CHAPEL_EXPECT_MODE=real cargo test --locked --features chapel --lib -- proof_search verify_proof_parallel

# Alias retained for muscle-memory; same as chapel-test.
test-chapel: chapel-test

# Test Zig FFI bridge independently
test-chapel-ffi:
    cd src/zig_ffi && zig build test

# Full local real-library path, with the independent stub bridge unit tests.
chapel-all: chapel-smoke test-chapel-ffi chapel-test-real
    @echo "Real Chapel build and selected Rust/FFI tests completed"

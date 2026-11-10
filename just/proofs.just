# SPDX-License-Identifier: MPL-2.0
# Imported by the root Justfile (hotspot split); recipes moved verbatim.

# ── Dogfood proof corpus (proofs/{coq,lean,agda} + src/idris validator) ──
# Each recipe assumes its toolchain is already installed (see `just doctor`);
# CI installs the toolchains first, then calls these so local and CI run the
# exact same commands.

# Type-check the whole dogfood proof corpus across every assistant.
proofs: proofs-coq proofs-lean proofs-agda proofs-idris proofs-verif-lean proofs-verif-idris

# Compile the Coq proof corpus (proofs/coq/**/*.v).
proofs-coq:
    #!/usr/bin/env bash
    set -euo pipefail
    cd proofs/coq
    for f in $(find . -name '*.v' | sort); do
        echo "coqc $f"
        coqc -q "$f"
    done
    echo "Coq corpus: all files type-check"

# Build the Lean 4 proof corpus via Lake (proofs/lean).
proofs-lean:
    cd proofs/lean && lake build

# Type-check the Agda proof corpus (proofs/agda/*.agda).
proofs-agda:
    #!/usr/bin/env bash
    set -euo pipefail
    # Agda writes UTF-8 to stdout and aborts under a non-UTF-8 locale (C/POSIX).
    export LC_ALL="${LC_ALL:-C.UTF-8}"
    cd proofs/agda
    for f in $(find . -name '*.agda' -not -path './_build/*' -not -path './dist-newstyle/*' | sort); do
        echo "agda --safe --without-K --cubical-compatible $f"
        agda --safe --without-K --cubical-compatible "$f"
    done
    echo "Agda corpus: all files type-check"

# Type-check the Idris2 validator (src/idris) — --typecheck needs no codegen backend.
proofs-idris:
    cd src/idris && idris2 --typecheck echidna-validator.ipkg

# Distinct from proofs-lean: the verification-pipeline *property* proofs
# (ConfidenceLattice, ParetoMaximality, ParetoStrongMaximality, IntegrityVerification,
# PortfolioCompleteness) under verification/proofs/lean4, not the dogfood corpus under
# proofs/lean. No mathlib dependency (lake-manifest packages: []), so the build is light.
# Build the Lean 4 trust-pipeline property proofs via Lake (verification/proofs/lean4).
proofs-verif-lean:
    cd verification/proofs/lean4 && lake build

# DispatchCorrectness imports EchidnaABI.Types, so the echidnaabi package
# (src/abi) is installed first (--install builds it on the way); the ipkg then
# type-checks all 11 modules with a reliable aggregate exit code. A bare per-file
# `idris2 --check` is unsafe here -- it exits 0 even on an unresolved import -- so
# the ipkg build is the gate and any "Error" line is also treated as failure.
# Type-check the Idris2 trust-pipeline property proofs (verification/proofs/idris2).
proofs-verif-idris:
    #!/usr/bin/env bash
    set -euo pipefail
    (cd src/abi && idris2 --install echidnaabi.ipkg >/dev/null)
    cd verification/proofs/idris2
    out=$(idris2 --typecheck echidna-verif-proofs.ipkg 2>&1)
    printf '%s\n' "$out"
    if printf '%s\n' "$out" | grep -qE '^Error'; then
        echo "Idris2 verification corpus: TYPE ERRORS DETECTED" >&2
        exit 1
    fi
    echo "Idris2 verification corpus: all files type-check"

# Accept fixtures must type-check, reject fixtures must be refused (tests/abi).
# Type-check the Idris2 ABI accept/reject fixtures (mechanical falsifier).
abi-fixtures:
    bash scripts/abi-fixtures.sh

# Heavy (downloads the ~500MB Isabelle release), so this is gated by the weekly
# verification-proofs-cron workflow, not the per-PR `proofs` rollup. Covers the
# base-HOL theories; algebra/GroupTheory.thy is excluded (see proofs/isabelle/ROOT).
# Verify the Isabelle/HOL self-proof corpus (proofs/isabelle) via `isabelle build`.
proofs-isabelle:
    cd proofs/isabelle && isabelle build -d . -v Echidna_Isabelle

# Mizar is not packaged for apt and ships only from mizar.org (Tier-4 in this
# project); like Isabelle it is gated by the weekly cron, not per-PR. MIZFILES
# must point at the Mizar share dir. Errors are reported in a per-file .err file
# (the verifier's exit code is not reliable), so a non-empty .err fails the recipe.
# Verify the Mizar self-proof corpus (proofs/mizar) with the Mizar verifier.
proofs-mizar:
    #!/usr/bin/env bash
    # Not -e: makeenv/verifier signal errors via a per-file .err (line col code),
    # not a reliable exit code, so inspect that rather than abort on first non-zero.
    set -uo pipefail
    : "${MIZFILES:?MIZFILES must point at the Mizar share dir}"
    cd proofs/mizar
    rc=0
    for f in *.miz; do
        base="${f%.miz}"
        echo "=== $f ==="
        makeenv "$f" || echo "(makeenv exit $?)"
        verifier "$f" || echo "(verifier exit $?)"
        if [ -s "$base.err" ]; then
            echo "--- $base.err (line col code) ---"
            cat "$base.err"
            while read -r line col code; do
                src="$(sed -n "${line}p" "$f" 2>/dev/null)"
                [ -n "$src" ] && echo "    L${line}:${col} (code ${code}): ${src}"
            done < "$base.err"
            rc=1
        else
            echo "($f verifies clean)"
        fi
    done
    [ "$rc" -eq 0 ] || { echo "Mizar corpus: VERIFICATION ERRORS (see .err above)" >&2; exit 1; }
    echo "Mizar corpus: all files verify"

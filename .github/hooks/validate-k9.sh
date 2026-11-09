#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
#
# validate-k9.sh — pre-push K9 check, through the canonical validator.
#
# One validator per family (hyperpolymath/standards,
# docs/CONTRACTILE-DESCRIPTILE-VALIDATION.adoc): the grep checks that used to
# live here were a second validator, and they accepted files that contract
# v1.0.0 (D173) rejects. This runs 1-formats/k9/tools/k9-validate.sh from a
# standards checkout over the tracked K9 files, strict, layers L0–L2 (L0–L1
# when nickel is not installed), as the k9-conformance lane does in CI (.github/workflows/dogfood-gate.yml). The lane
# is the gate; this is the early warning.
#
# Environment variables:
#   INPUT_PATH     — Repository to check (default: .)
#   STANDARDS_DIR  — A hyperpolymath/standards checkout
#                    (default: ../standards beside the repository)
#
# Exit codes:
#   0 — Every tracked K9 file passes, or no validator is available (skipped
#       with a notice: CI still runs the lane)
#   1 — A file failed

set -euo pipefail

REPO="${INPUT_PATH:-.}"
STANDARDS_DIR="${STANDARDS_DIR:-$(cd "$REPO/.." && pwd)/standards}"
case "$STANDARDS_DIR" in
    /*) ;;
    *) STANDARDS_DIR="$PWD/$STANDARDS_DIR" ;;
esac
VALIDATOR="$STANDARDS_DIR/1-formats/k9/tools/k9-validate.sh"

if [ ! -f "$VALIDATOR" ]; then
    echo "::notice::K9: no standards checkout at $STANDARDS_DIR (set STANDARDS_DIR to run the validator locally); the k9-conformance lane validates in CI"
    exit 0
fi

# L2 is the Nickel evaluation against the contract; without nickel the
# validator reports those checks as SKIPPED and refuses to call that a pass,
# so stop at L1 here and say so. The lane checks L2 in CI either way.
LAYER=L2
if ! command -v nickel >/dev/null 2>&1; then
    echo "::notice::K9: nickel is not installed, so layer L2 (Nickel semantics) is left to the CI lane; checking L0–L1"
    LAYER=L1
fi

cd "$REPO"
mapfile -t files < <(git ls-files -- '*.k9.ncl' '*.k9' '*.k9.lock' | sort)
if [ "${#files[@]}" -eq 0 ]; then
    echo "::notice::K9: no tracked K9 file"
    exit 0
fi

errors=0
for f in "${files[@]}"; do
    echo "  Validating: $f"
    if ! bash "$VALIDATOR" --strict --layer "$LAYER" "$f"; then
        errors=$((errors + 1))
    fi
done

echo "K9: ${#files[@]} file(s), ${errors} failing (validator: $VALIDATOR)"
[ "$errors" -eq 0 ] || { echo "::error::K9 validation failed for ${errors} file(s)"; exit 1; }
echo "K9 validation passed."

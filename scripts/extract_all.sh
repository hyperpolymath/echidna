#!/usr/bin/env bash
# SPDX-License-Identifier: PMPL-1.0-or-later
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
#
# ECHIDNA — run every scripts/extract_*.jl once, non-interactively.
#
# Assumes scripts/provision_corpora.sh has already populated
# external_corpora/; extractors whose upstream is absent short-circuit
# with a print line (they already handle missing inputs gracefully).
#
# Usage
# -----
#   scripts/extract_all.sh                    # run every extractor
#   scripts/extract_all.sh NAME ...           # run only the named extractors
#                                             # (matches scripts/extract_<NAME>.jl)
#   scripts/extract_all.sh --list             # list available extractors
#
# Environment
#   ECHIDNA_JULIA_PROJECT — path passed to `julia --project=`
#     (default: src/julia).
#
# Exit code is the number of extractors that failed (0 on clean run,
# N on partial failure).  Suitable for a nightly cron.

set -uo pipefail  # NOTE: not `set -e` — we want to collect failures, not abort.

ECHIDNA_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
JULIA_PROJECT="${ECHIDNA_JULIA_PROJECT:-$ECHIDNA_ROOT/src/julia}"

list_extractors() {
    ( cd "$ECHIDNA_ROOT/scripts" && ls extract_*.jl 2>/dev/null | sed 's/^extract_//; s/\.jl$//' )
}

# Handle info flags before probing the environment.
case "${1:-}" in
    --list)
        list_extractors
        exit 0
        ;;
    -h|--help)
        sed -n '4,22p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'
        exit 0
        ;;
esac

if ! command -v julia >/dev/null 2>&1; then
    echo "error: julia not on PATH; install Julia to run the extractors." >&2
    exit 127
fi

# Build the list of extractors to run.
if [[ $# -gt 0 ]]; then
    targets=()
    for name in "$@"; do
        path="$ECHIDNA_ROOT/scripts/extract_${name}.jl"
        if [[ ! -f "$path" ]]; then
            echo "error: no such extractor: extract_${name}.jl" >&2
            exit 2
        fi
        targets+=("$path")
    done
else
    mapfile -t targets < <(find "$ECHIDNA_ROOT/scripts" -maxdepth 1 -name 'extract_*.jl' | sort)
fi

echo "Running ${#targets[@]} extractor(s) with --project=$JULIA_PROJECT"
echo

failed=()
for script in "${targets[@]}"; do
    name="$(basename "$script" .jl)"
    echo "========================================"
    echo "  $name"
    echo "========================================"
    if julia --project="$JULIA_PROJECT" "$script"; then
        echo "  [ok] $name"
    else
        echo "  [FAIL] $name"
        failed+=("$name")
    fi
    echo
done

if [[ ${#failed[@]} -gt 0 ]]; then
    echo "Extractors that failed: ${failed[*]}"
    exit "${#failed[@]}"
fi

echo "All extractors completed."

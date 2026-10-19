#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
#
# lexicon-check.sh — apply the lexicon v2 Nickel contract
# (data/synonyms/schema.ncl) to every shipped table, and prove the contract
# still bites: every fixture under tests/lexicon_fixtures/accept/ must pass
# and every fixture under tests/lexicon_fixtures/reject/ must fail.
#
# Usage: scripts/lexicon-check.sh        (from the repository root)
# Needs: nickel (>= 1.12) on PATH, or NICKEL=/path/to/nickel.
set -euo pipefail

nickel="${NICKEL:-nickel}"
command -v "$nickel" >/dev/null || { echo "lexicon-check: nickel not found (set NICKEL)" >&2; exit 2; }
root="$(pwd)"
schema="$root/data/synonyms/schema.ncl"
[ -f "$schema" ] || { echo "lexicon-check: run from the repository root" >&2; exit 2; }

# check FILE -> exit status of applying the contract to FILE.
check() {
  printf '(import "%s") | (import "%s").Table\n' "$1" "$schema" \
    | "$nickel" export --format json >/dev/null 2>"$errfile"
}

errfile="$(mktemp)"
trap 'rm -f "$errfile"' EXIT
bad=0 n=0

for f in "$root"/data/synonyms/*.toml "$root"/tests/lexicon_fixtures/accept/*.toml; do
  n=$((n + 1))
  if ! check "$f"; then
    echo "FAIL (must pass): ${f#"$root"/}"
    sed -n '1,12p' "$errfile"
    bad=$((bad + 1))
  fi
done

for f in "$root"/tests/lexicon_fixtures/reject/*.toml; do
  n=$((n + 1))
  if check "$f"; then
    echo "FAIL (must be rejected): ${f#"$root"/}"
    bad=$((bad + 1))
  fi
done

if [ "$bad" -ne 0 ]; then
  echo "lexicon-check: $bad of $n files failed"
  exit 1
fi
echo "lexicon-check: $n files, all as expected"

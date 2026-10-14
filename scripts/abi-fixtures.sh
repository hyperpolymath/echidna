#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
#
# Mechanical falsifier for the Idris2 ABI (src/abi): every fixture under
# tests/abi/accept must type-check, and every fixture under tests/abi/reject
# must be refused with a unification error. Each reject fixture names the
# accept fixture it mirrors, so a refusal is attributable to the one change.
#
# Exit codes alone are not trusted: `idris2 --check` exits 0 on an
# unresolved import (see the proofs-verif-idris recipe in the Justfile), so
# accept requires no `Error` in the output and reject requires a unification
# error specifically.
set -euo pipefail

root="$(cd "$(dirname "$0")/.." && pwd)"
abi="$root/src/abi"
status=0

# Fixtures import EchidnaABI.* from the package's build output.
(cd "$abi" && idris2 --build echidnaabi.ipkg >/dev/null)
export IDRIS2_PATH="$abi/build/ttc${IDRIS2_PATH:+:$IDRIS2_PATH}"

check() {
  # Each fixture is checked in a fresh directory: a build/ cache left next
  # to a fixture by an earlier run can make idris2 skip the check entirely.
  local tmp
  tmp="$(mktemp -d)"
  cp "$1" "$tmp/"
  (cd "$tmp" && idris2 --check "$(basename "$1")" 2>&1) || true
  rm -rf "$tmp"
}

for f in "$root"/tests/abi/accept/*.idr; do
  rel="${f#"$root"/}"
  out="$(check "$f")"
  if printf '%s\n' "$out" | grep -q 'Error'; then
    echo "FAIL accept fixture refused: $rel"
    printf '%s\n' "$out" | sed 's/^/    /'
    status=1
  else
    echo "ok   accept: $rel"
  fi
done

for f in "$root"/tests/abi/reject/*.idr; do
  rel="${f#"$root"/}"
  out="$(check "$f")"
  if printf '%s\n' "$out" | grep -q 'Mismatch between'; then
    echo "ok   reject: $rel"
    printf '%s\n' "$out" | grep -m1 'Mismatch between' | sed 's/^/    /'
  elif printf '%s\n' "$out" | grep -q 'Error'; then
    echo "FAIL reject fixture refused for a non-type reason: $rel"
    printf '%s\n' "$out" | sed 's/^/    /'
    status=1
  else
    echo "FAIL reject fixture type-checked: $rel"
    status=1
  fi
done

exit "$status"

#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# fs-fingerprint-drift.sh A B
#
# A and B are fs-fingerprint.sh outputs ("<sha256>  <path>" per line).
# Prints the deepest paths whose digest differs or that exist on one side
# only. An ancestor of a printed path is left out, since it differs only
# because the path beneath it does.
set -euo pipefail
a=${1:?usage: fs-fingerprint-drift.sh A B}; b=${2:?usage: fs-fingerprint-drift.sh A B}
t=$(mktemp -d); trap 'rm -rf -- "$t"' EXIT
# "path<TAB>digest", keyed on path; awk keeps names with spaces whole.
key() { awk '{ d = substr($0, 1, 64); p = substr($0, 67); print p "\t" d }' "$1" | LC_ALL=C sort -t "$(printf '\t')" -k1,1; }
key "$a" > "$t/a"; key "$b" > "$t/b"
LC_ALL=C join -t "$(printf '\t')" -a 1 -a 2 -e MISSING -o 0,1.2,2.2 "$t/a" "$t/b" \
  | awk -F '\t' '$2 != $3 { print $1 }' > "$t/drift"
# Keep a path only if no other drifting path lies beneath it.
awk 'NR == FNR { all[$0] = 1; next }
     { for (q in all) if (index(q, $0 "/") == 1) next; print }' "$t/drift" "$t/drift" | LC_ALL=C sort

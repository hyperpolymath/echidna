#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
#
# false_friend_scan.sh — lexical cognate / false-friend / homonym census over
# training_data/proof_states_<prover>.jsonl for one prover pair.
#
# Evidence class: LEXICAL ONLY. Nothing here is fidelity evidence in the
# ECH-05 sense (src/rust/verification/result_arbiter.rs); the output is a
# candidate list for lexicon curation and for consequence probing. See
# docs/decisions/2026-10-19-lexicon-v2-and-identity-arbitration.adoc.
#
# Usage:  scripts/false_friend_scan.sh [TRAINING_DIR] [PROVER_A] [PROVER_B]
# Default: training_data hol4 hol_light   (the stage-6a first pair)
# Needs:   jq + coreutils (sort, join, comm, awk, cut, uniq). Deterministic.
set -euo pipefail

dir="${1:-training_data}"
a="${2:-hol4}"
b="${3:-hol_light}"
tab="$(printf '\t')"
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

# prover -> TSV "name<TAB>goal" with whitespace normalised, one row per
# distinct (name, goal) pair, sorted on the name for join(1).
extract() {
  local f="$dir/proof_states_$1.jsonl"
  [ -s "$f" ] || { echo "no records: $f" >&2; return 1; }
  jq -r 'select(.theorem != null and .goal != null)
         | [.theorem, (.goal | gsub("[[:space:]]+"; " ") | gsub("^ | $"; ""))]
         | @tsv' "$f" | LC_ALL=C sort -u | LC_ALL=C sort -t "$tab" -k1,1 -s
}

# prover tsv -> one census row: records, distinct names, homonymous names
# (one name, more than one distinct goal), homonym rate.
census() {
  local r n h
  r=$(wc -l < "$2")
  n=$(cut -f1 "$2" | LC_ALL=C sort -u | wc -l)
  h=$(cut -f1 "$2" | LC_ALL=C sort | uniq -d | wc -l)
  awk -v p="$1" -v r="$r" -v n="$n" -v h="$h" \
    'BEGIN { printf "%-14s %9d %9d %9d %6.1f%%\n", p, r, n, h, (n ? 100*h/n : 0) }'
}

extract "$a" > "$work/a.tsv"
extract "$b" > "$work/b.tsv"

echo "== within-prover census"
printf "%-14s %9s %9s %9s %7s\n" prover records names homonyms rate
census "$a" "$work/a.tsv"
census "$b" "$work/b.tsv"

cut -f1 "$work/a.tsv" | LC_ALL=C sort -u > "$work/na"
cut -f1 "$work/b.tsv" | LC_ALL=C sort -u > "$work/nb"
echo
echo "== cross-prover name overlap: $a vs $b"
echo "shared names: $(LC_ALL=C comm -12 "$work/na" "$work/nb" | wc -l)"
echo "$a-only: $(LC_ALL=C comm -23 "$work/na" "$work/nb" | wc -l)"
echo "$b-only: $(LC_ALL=C comm -13 "$work/na" "$work/nb" | wc -l)"

LC_ALL=C join -t "$tab" "$work/a.tsv" "$work/b.tsv" > "$work/joined.tsv"
echo
echo "== shared names, statement text agreement (name-pairs: $(wc -l < "$work/joined.tsv"))"
awk -F'\t' '{ if ($2 == $3) s++; else d++ }
  END { printf "cognate (identical statement text): %d\ndiffering statement text (false-friend or specialisation candidates): %d\n", s, d }' \
  "$work/joined.tsv"
echo
echo "== first differing name-pairs (deterministic order)"
awk -F'\t' -v A="$a" -v B="$b" '$2 != $3 {
  printf "%s\n  %s: %s\n  %s: %s\n", $1, A, substr($2, 1, 100), B, substr($3, 1, 100) }' \
  "$work/joined.tsv" | head -24

#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Copyright (c) 2026 Jonathan D.A. Jewell
#
# agda-cone-receipt.sh ENTRY.agda — the PROOF-POLICY §8.2 receipt for the
# theory theorems in ENTRY: the Agda version, the standard-library pin, the
# flags in force, the import cone with a SHA-256 per file, and a
# comment-aware scan of that cone for postulates, unsafe pragmas and
# primTrustMe (§8.4). Writes one JCS object to stdout.
#
# Run from meta-checker/ after scripts/ci/check-agda.sh, in the environment
# scripts/ci/setup-agda.sh prepares (AGDA_LIBRARIES_FILE, Agda_datadir).
# AGDA_STDLIB_SHA256 names the pinned stdlib archive digest.
#
# The scan reads Agda source with nested {- -} block comments and -- line
# comments removed and {-# #-} pragmas kept. It does not lex string
# literals; a literal holding "{-" would hide text from it, and --safe is
# still the check that refuses escape hatches. The scan is the record §8.4
# asks for, not a replacement for --safe.
#
# Postulates in the Agda data directory (Agda.Primitive's universe-level
# primitives) belong to the Agda kernel's trust base. They are listed in the
# receipt, not counted as findings.
#
# Exit codes: 0 receipt written and the scan is clean, 1 a finding outside
# the kernel's own primitives, 2 cannot run.
set -euo pipefail
export LC_ALL=C.UTF-8

# strip <file>: source with comments removed and pragmas kept.
strip() {
  awk '
    { line = $0; out = ""; i = 1; n = length(line)
      while (i <= n) {
        two = substr(line, i, 2); three = substr(line, i, 3)
        if (depth == 0 && inpragma == 0 && three == "{-#") { inpragma = 1; out = out three; i += 3; continue }
        if (inpragma == 1 && three == "#-}") { inpragma = 0; out = out three; i += 3; continue }
        if (inpragma == 1) { out = out substr(line, i, 1); i++; continue }
        if (depth == 0 && two == "--") break
        if (two == "{-") { depth++; i += 2; continue }
        if (depth > 0 && two == "-}") { depth--; i += 2; continue }
        if (depth == 0) out = out substr(line, i, 1)
        i++
      }
      print out }' "$1"
}

# scan: the escape hatches the receipt records, one "line:text" per hit.
scan() {
  { strip "$1" | grep -nE '(^|[[:space:](){};])postulate($|[[:space:](){};])|\{-#[[:space:]]*(TERMINATING|NON_TERMINATING|NO_POSITIVITY_CHECK|NO_UNIVERSE_CHECK|NON_COVERING)|primTrustMe' || true; }
}

# Sourced by scripts/ci/test-agda-cone-receipt.sh for strip and scan only.
# shellcheck disable=SC2317 # exit runs only when executed rather than sourced
if [[ "${AGDA_CONE_RECEIPT_FUNCTIONS_ONLY:-}" == 1 ]]; then return 0 2>/dev/null || exit 0; fi

entry=${1:?usage: agda-cone-receipt.sh ENTRY.agda}
flags=(--safe --without-K --cubical-compatible)
if ! command -v agda >/dev/null 2>&1 || [[ ! -f "${AGDA_LIBRARIES_FILE:-}" ]]; then
  echo "agda-cone-receipt: pinned Agda setup missing" >&2; exit 2
fi
command -v jq >/dev/null 2>&1 || { echo "agda-cone-receipt: jq missing" >&2; exit 2; }

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

agda --no-default-libraries --library-file "$AGDA_LIBRARIES_FILE" "${flags[@]}" \
  --dependency-graph="$tmp/cone.dot" "$entry" > "$tmp/agda.log" 2>&1 \
  || { cat "$tmp/agda.log" >&2; echo "agda-cone-receipt: agda failed" >&2; exit 2; }

data_dir=$(agda --print-agda-data-dir)
# Include roots: the Agda data directory's lib/prim, then every library's
# include directories from the library file (one .agda-lib path per line).
roots=("$data_dir/lib/prim")
while IFS= read -r lib; do
  [[ -n "$lib" ]] || continue
  libdir=$(dirname -- "$lib")
  while IFS= read -r inc; do
    roots+=("$libdir/$inc")
  done < <(awk '/^include:/ { sub(/^include:[[:space:]]*/, ""); n = split($0, a, /[[:space:]]+/); for (i = 1; i <= n; i++) if (a[i] != "") print a[i] }' "$lib")
done < "$AGDA_LIBRARIES_FILE"

# Module names from the dot file's node labels.
grep -oE 'label="[^"]+"' "$tmp/cone.dot" | sed -E 's/^label="//; s/"$//' | sort -u > "$tmp/modules"
[[ -s "$tmp/modules" ]] || { echo "agda-cone-receipt: empty dependency graph" >&2; exit 2; }

: > "$tmp/cone.jsonl"; : > "$tmp/findings.jsonl"; : > "$tmp/kernel.jsonl"
while IFS= read -r module; do
  rel="${module//.//}"
  file=""
  for root in "${roots[@]}"; do
    for ext in agda lagda lagda.md; do
      [[ -f "$root/$rel.$ext" ]] && { file="$root/$rel.$ext"; break 2; }
    done
  done
  [[ -n "$file" ]] || { echo "agda-cone-receipt: cannot locate module $module" >&2; exit 2; }
  file=$(realpath -- "$file")
  case "$file" in
    "$(realpath -- "$data_dir")"/*) origin=agda-kernel ;;
    "$(realpath -- "$PWD")"/*) origin=first-party ;;
    *) origin=library ;;
  esac
  digest=$(sha256sum "$file" | cut -d' ' -f1)
  jq -cn --arg m "$module" --arg o "$origin" --arg d "$digest" '{module: $m, origin: $o, sha256: $d}' >> "$tmp/cone.jsonl"
  scan "$file" \
    | while IFS=: read -r ln text; do
        if [[ "$origin" == agda-kernel ]]; then target="$tmp/kernel.jsonl"; else target="$tmp/findings.jsonl"; fi
        jq -cn --arg m "$module" --argjson l "$ln" --arg t "$text" '{module: $m, line: $l, text: ($t | gsub("^\\s+|\\s+$"; ""))}' >> "$target"
      done
done < "$tmp/modules"

commit=$(git rev-parse HEAD)
dirty=$(git status --porcelain -- . | head -1)
agda_bin=$(command -v agda)
jq -cnS \
  --arg commit "$commit" --arg dirty "${dirty:+yes}" --arg entry "$entry" \
  --arg agda "$(agda --version)" --arg agda_sha "$(sha256sum "$agda_bin" | cut -d' ' -f1)" \
  --arg stdlib_sha "${AGDA_STDLIB_SHA256:-unrecorded}" \
  --argjson flags "$(printf '%s\n' "${flags[@]}" | jq -R . | jq -s .)" \
  --slurpfile cone "$tmp/cone.jsonl" --slurpfile findings "$tmp/findings.jsonl" \
  --slurpfile kernel "$tmp/kernel.jsonl" '
  {
    schema_version: 1,
    kind: "agda-cone-receipt",
    policy: "standards 3-practice/PROOF-POLICY.adoc §8.2, §8.4",
    source: {repository: "https://github.com/hyperpolymath/echidna", commit: $commit,
             uncommitted_changes_under_entry_dir: ($dirty == "yes"), entrypoint: $entry},
    toolchain: {agda: $agda, agda_executable_sha256: $agda_sha,
                stdlib_archive_sha256: $stdlib_sha, flags: $flags},
    import_cone: {count: ($cone | length), modules: $cone},
    postulate_scan: {
      method: "comment-aware: nested block and line comments removed, pragmas kept; string literals not lexed",
      kernel_primitives: $kernel,
      findings: $findings,
      result: (if ($findings | length) == 0 then "clean" else "findings" end)
    }
  }'
[[ ! -s "$tmp/findings.jsonl" ]]

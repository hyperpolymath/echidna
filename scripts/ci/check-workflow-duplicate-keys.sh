#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
#
# Reject GitHub Actions workflows containing duplicate YAML keys.
#
# WHY THIS EXISTS AS A SEPARATE CHECK
# -----------------------------------
# GitHub Actions rejects a workflow with duplicate keys outright. The run is
# recorded as `failure` with NO jobs, NO log and NO check run — a red mark on
# the board with nothing behind it to read, and `gh pr checks` shows no row.
#
# Nothing else in the toolchain sees this, because ordinary YAML parsers
# SILENTLY KEEP THE LAST duplicate and report success. The file "parses".
# Linters, formatters and sweep scripts are all structurally blind to it.
#
# Measured 2026-08-05: nine workflows in `hypatia` were in this state,
# including a CodeQL workflow with 18 failures, 12 startup_failures and ZERO
# successes in its lifetime — the repository had never once been scanned by
# its own scanner.
#
# WHY SHELL. This check first shipped in Python, which estate language policy
# bans with no exceptions, so it blocked the very pull requests it was meant to
# protect. A Deno port was the obvious second choice — the language-policy gate
# has that precedent — but Deno is being retired from the estate, so it would
# have been a port onto a disappearing runtime. Shell is what 29 of the 33
# scripts here already use, needs no runtime beyond awk, and adds no setup step
# to any job.
#
# WHY A STRUCTURAL SCANNER AND NOT A PARSER. A parser that rejects duplicates
# is what is wanted, but the available YAML libraries do the opposite by
# design: they resolve duplicates silently, which is the whole reason this
# check exists. So this walks the document tracking sibling keys per mapping
# level. The constructs that would otherwise produce FALSE positives are
# handled explicitly, because a duplicate-key checker that cries wolf gets
# switched off:
#
#   * BLOCK SCALARS — a `run: |` body routinely contains `foo: bar` shell
#     lines that are not YAML keys at all.
#   * LIST ITEMS — every step in a job legitimately repeats `name:`.
#   * DOCUMENT SEPARATORS — `---` starts a fresh sibling scope.
#   * QUOTED KEYS — `"on":` and `on:` are the same key.
set -uo pipefail

scan_one() {
  awk '
    function clear_deeper(ind,   k) {
      for (k in seen) { split(k, p, SUBSEP); if (p[1] + 0 > ind) delete seen[k] }
    }
    function clear_from(ind,   k) {
      for (k in seen) { split(k, p, SUBSEP); if (p[1] + 0 >= ind) delete seen[k] }
    }
    BEGIN { block = -1; dupes = 0 }
    {
      line = $0
      sub(/\r$/, "", line)
      # indent width
      match(line, /^ */); ind = RLENGTH
      trimmed = line; sub(/^ +/, "", trimmed); sub(/ +$/, "", trimmed)

      # inside a block scalar: body text, not keys
      if (block >= 0) {
        if (trimmed == "" || ind > block) next
        block = -1
      }
      if (trimmed == "" || substr(trimmed, 1, 1) == "#") next

      if (trimmed == "---") { delete seen; next }
      if (trimmed == "...") { delete seen; next }

      # a list item opens a fresh mapping scope
      if (substr(trimmed, 1, 2) == "- " || trimmed == "-") {
        clear_from(ind)
        rest = substr(trimmed, 3)
        if (match(rest, /^("[^"]*"|\x27[^\x27]*\x27|[^ #][^:]*):( |$)/)) {
          key = substr(rest, RSTART, RLENGTH)
          sub(/:.*$/, "", key); gsub(/^["\x27]|["\x27]$/, "", key)
          seen[ind + 2, key] = 1
        }
        if (match(trimmed, /:[ ]*[|>][-+0-9]*$/)) block = ind
        next
      }

      if (!match(trimmed, /^("[^"]*"|\x27[^\x27]*\x27|[^ #][^:]*):( |$)/)) {
        if (match(trimmed, /:[ ]*[|>][-+0-9]*$/)) block = ind
        next
      }
      key = substr(trimmed, RSTART, RLENGTH)
      sub(/:.*$/, "", key); gsub(/^["\x27]|["\x27]$/, "", key)
      sub(/ +$/, "", key)

      clear_deeper(ind)
      if ((ind, key) in seen) { printf "%s|%d\n", key, NR; dupes++ }
      seen[ind, key] = 1

      if (match(trimmed, /:[ ]*[|>][-+0-9]*$/)) block = ind
    }
    END { exit (dupes > 0 ? 1 : 0) }
  ' "$1"
}

targets=("$@")
[ ${#targets[@]} -eq 0 ] && targets=(".github/workflows")

files=()
for t in "${targets[@]}"; do
  if [ -d "$t" ]; then
    while IFS= read -r f; do files+=("$f"); done < <(
      find "$t" -maxdepth 1 -type f \( -name '*.yml' -o -name '*.yaml' \) | sort)
  elif [ -e "$t" ]; then
    files+=("$t")
  fi
done

failed=0
for f in "${files[@]}"; do
  out="$(scan_one "$f")" || {
    detail="$(printf '%s' "$out" | awk -F'|' '{printf "%s\x27%s\x27 (line %s)", sep, $1, $2; sep=", "}')"
    echo "::error file=${f}::duplicate key(s): ${detail}"
    echo "FAIL ${f}: duplicate key(s): ${detail}"
    failed=$((failed + 1))
  }
done

if [ "$failed" -gt 0 ]; then
  echo
  echo "${failed} of ${#files[@]} workflow file(s) contain duplicate keys."
  echo "GitHub Actions rejects these before any job is created — they fail with"
  echo "no log and no check run. An ordinary YAML parser does NOT catch this;"
  echo "it keeps the last duplicate and reports success."
  exit 1
fi
echo "duplicate-key check: ${#files[@]} workflow file(s) clean"

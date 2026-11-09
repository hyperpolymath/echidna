#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Copyright (c) 2026 Jonathan D.A. Jewell
# idris-code-lines.sh DIR — print every line of code in DIR's .idr files as
# FILE:LINE:TEXT, with comments removed: `--` line comments (including
# `|||` documentation comments) and nested `{- -}` blocks. idris2-abi-ci
# greps this output for escape hatches, so prose such as "NO postulate" in a
# documentation comment is not a finding and a real one is never hidden by
# being near one. String literals are not lexed.
set -euo pipefail
dir=${1:?usage: idris-code-lines.sh DIR}
while IFS= read -r -d '' f; do
  awk -v file="$f" '
    { s = $0; out = ""; i = 1; n = length(s)
      if (depth == 0 && s ~ /^[[:space:]]*\|\|\|/) { next }
      while (i <= n) {
        two = substr(s, i, 2)
        if (depth == 0 && two == "--") break
        if (two == "{-") { depth++; i += 2; continue }
        if (depth > 0 && two == "-}") { depth--; i += 2; continue }
        if (depth == 0) out = out substr(s, i, 1)
        i++
      }
      if (out ~ /[^[:space:]]/) print file ":" NR ":" out }' "$f"
done < <(find "$dir" -type f -name '*.idr' -print0 | sort -z)

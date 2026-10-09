#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
#
# Fail CI when an allow-fail unit lacks an owner or an expiry, or has expired.
#
# Every workflow line that sets `continue-on-error` to anything other than the
# literal `false` must carry, on the same line:
#
#     # allow-fail: issue=#<n> expires=YYYY-MM-DD
#
# The checker is deliberately text-based: it needs no YAML library, and it sees
# the same literal the runner sees. It does not decide what happens at expiry.
# A person does (ultraplan Phase 2.3, tracking issue #416).
#
# Usage: check-allow-fail-expiry.sh [--today YYYY-MM-DD] [--warn-days N] [DIR ...]
#
# Exit codes: 0 all units owned and in date, 1 a unit is unowned, undated,
# or expired, 2 bad arguments.

set -euo pipefail
export TZ=UTC

today=""
warn_days=21
dirs=()

while [ $# -gt 0 ]; do
  case "$1" in
    --today) [ $# -ge 2 ] || { echo "--today needs a value" >&2; exit 2; }; today="$2"; shift 2 ;;
    --warn-days) [ $# -ge 2 ] || { echo "--warn-days needs a value" >&2; exit 2; }; warn_days="$2"; shift 2 ;;
    -h|--help) sed -n '3,20p' "$0"; exit 0 ;;
    --) shift; dirs+=("$@"); break ;;
    -*) echo "unknown option: $1" >&2; exit 2 ;;
    *) dirs+=("$1"); shift ;;
  esac
done

if [ ${#dirs[@]} -eq 0 ]; then
  dirs=(.github/workflows)
fi
if [ -z "$today" ]; then
  today=$(date +%F)
fi
if ! today_s=$(date -d "$today" +%s 2>/dev/null); then
  echo "invalid --today: $today" >&2
  exit 2
fi
if ! [[ $warn_days =~ ^[0-9]+$ ]]; then
  echo "--warn-days must be a non-negative integer" >&2
  exit 2
fi

shopt -s nullglob
files=()
for d in "${dirs[@]}"; do
  for f in "$d"/*.yml "$d"/*.yaml; do
    files+=("$f")
  done
done

errors=()
warnings=()
units=0

for file in "${files[@]}"; do
  lineno=0
  while IFS= read -r line || [ -n "$line" ]; do
    lineno=$((lineno + 1))
    # Same shape as the old Python KEY pattern: the key must open the line.
    [[ $line =~ ^[[:space:]]*continue-on-error:[[:space:]]*(.*)$ ]] || continue
    value=$(printf '%s' "${BASH_REMATCH[1]}" | sed -E 's/[[:space:]]*(#.*)?$//')
    [ "$value" = "false" ] && continue

    units=$((units + 1))
    where="$file:$lineno"
    mark=$(printf '%s' "$line" \
      | grep -oE '#[[:space:]]*allow-fail:[[:space:]]*issue=#[0-9]+[[:space:]]+expires=[0-9]{4}-[0-9]{2}-[0-9]{2}([^[:alnum:]_]|$)' \
      | head -1 || true)
    if [ -z "$mark" ]; then
      errors+=("$where: continue-on-error without '# allow-fail: issue=#N expires=YYYY-MM-DD'")
      continue
    fi
    issue=$(printf '%s' "$mark" | sed -E 's/.*issue=#([0-9]+).*/\1/')
    expiry=$(printf '%s' "$mark" | sed -E 's/.*expires=([0-9]{4}-[0-9]{2}-[0-9]{2}).*/\1/')
    if ! expiry_s=$(date -d "$expiry" +%s 2>/dev/null); then
      errors+=("$where: invalid expiry date $expiry")
      continue
    fi
    if [ "$expiry_s" -lt "$today_s" ]; then
      errors+=("$where: allow-fail expired on $expiry (issue #$issue); make it blocking, re-justify, or remove")
    elif [ $(( (expiry_s - today_s) / 86400 )) -le "$warn_days" ]; then
      warnings+=("$where: expires $expiry (issue #$issue)")
    fi
  done < "$file"
done

for w in ${warnings[@]+"${warnings[@]}"}; do
  echo "::warning::$w"
done
echo "allow-fail units checked: $units"
if [ ${#errors[@]} -gt 0 ]; then
  for e in "${errors[@]}"; do
    echo "::error::$e"
  done
  exit 1
fi
exit 0

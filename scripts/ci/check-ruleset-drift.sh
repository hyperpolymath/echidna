#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
#
# Compare the committed ruleset snapshot with the rulesets GitHub enforces.
#
# Snapshot files live in .github/rulesets/live/<name>.json, one per ruleset,
# keyed by the ruleset `id`. The top-level .github/rulesets/*.json files are
# historical payloads and are not compared.
#
# Reading rulesets needs repository administration read. Run this with a token
# that has it (`GH_TOKEN=... scripts/ci/check-ruleset-drift.sh`). The default
# GITHUB_TOKEN may not be enough in Actions; see the workflow note in
# .github/rulesets/README.adoc. Exit codes: 0 no drift, 1 drift, 2 cannot read.
#
# Regenerate the snapshot after an intentional change, not to silence drift:
#     scripts/ci/check-ruleset-drift.sh --write
#
# Requires gh and jq.

set -euo pipefail

repo="hyperpolymath/echidna"
dir=".github/rulesets/live"
write=0

while [ $# -gt 0 ]; do
  case "$1" in
    --repo) [ $# -ge 2 ] || { echo "--repo needs a value" >&2; exit 2; }; repo="$2"; shift 2 ;;
    --dir) [ $# -ge 2 ] || { echo "--dir needs a value" >&2; exit 2; }; dir="$2"; shift 2 ;;
    --write) write=1; shift ;;
    -h|--help) sed -n '3,19p' "$0"; exit 0 ;;
    *) echo "unknown argument: $1" >&2; exit 2 ;;
  esac
done

for tool in gh jq; do
  if ! command -v "$tool" >/dev/null 2>&1; then
    echo "cannot read rulesets for $repo: $tool is not installed" >&2
    exit 2
  fi
done

# Fields that change without a configuration change. Removed at every depth,
# then keys are sorted, so the comparison is on configuration only.
NORM='
  def norm:
    if type == "object" then
      with_entries(select(.key as $k | (["_links","created_at","updated_at","node_id","current_user_can_bypass","source","source_type"] | index($k)) == null))
      | map_values(norm)
    elif type == "array" then map(norm)
    else . end;
  norm'

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

# Read the enforced rulesets. Any failure here is "cannot read", exit 2.
if ! listing=$(gh api "repos/$repo/rulesets" 2>"$tmp/err"); then
  echo "cannot read rulesets for $repo: $(cat "$tmp/err")" >&2
  exit 2
fi
if ! jq -e 'type == "array"' <<<"$listing" >/dev/null 2>&1; then
  echo "cannot read rulesets for $repo: listing is not a JSON array" >&2
  exit 2
fi

live_ids=()
while IFS= read -r rid; do
  [ -n "$rid" ] || continue
  live_ids+=("$rid")
  if ! gh api "repos/$repo/rulesets/$rid" 2>"$tmp/err" \
      | jq -S "$NORM" > "$tmp/live-$rid.json" 2>>"$tmp/err"; then
    echo "cannot read ruleset $rid for $repo: $(cat "$tmp/err")" >&2
    exit 2
  fi
done < <(jq -r '.[].id' <<<"$listing")

if [ "$write" -eq 1 ]; then
  mkdir -p "$dir"
  for rid in ${live_ids[@]+"${live_ids[@]}"}; do
    name=$(jq -r '.name' "$tmp/live-$rid.json" | tr '/' '-')
    cp "$tmp/live-$rid.json" "$dir/$name.json"
  done
  echo "wrote ${#live_ids[@]} ruleset snapshot(s) to $dir"
  exit 0
fi

drift=()
seen=()
shopt -s nullglob
for snap in "$dir"/*.json; do
  rid=$(jq -r '.id // empty' "$snap")
  name=$(jq -r '.name // ""' "$snap")
  seen+=("$rid")
  if [ -z "$rid" ] || [ ! -f "$tmp/live-$rid.json" ]; then
    drift+=("$snap: ruleset $rid ($name) is in the snapshot but not enforced")
    continue
  fi
  snap_c=$(jq -S -c "$NORM" "$snap")
  live_c=$(jq -S -c . "$tmp/live-$rid.json")
  if [ "$snap_c" != "$live_c" ]; then
    drift+=("$snap: ruleset $rid ($name) differs from the enforced state")
  fi
done

for rid in ${live_ids[@]+"${live_ids[@]}"}; do
  found=0
  for s in ${seen[@]+"${seen[@]}"}; do
    [ "$s" = "$rid" ] && { found=1; break; }
  done
  if [ "$found" -eq 0 ]; then
    lname=$(jq -r '.name // ""' "$tmp/live-$rid.json")
    drift+=("ruleset $rid ($lname) is enforced but has no snapshot")
  fi
done

for d in ${drift[@]+"${drift[@]}"}; do
  echo "::error::$d"
done

uniq_seen=$(printf '%s\n' ${seen[@]+"${seen[@]}"} | sort -u | grep -c . || true)
echo "rulesets enforced: ${#live_ids[@]}, snapshots: $uniq_seen, drift: ${#drift[@]}"
if [ ${#drift[@]} -gt 0 ]; then
  exit 1
fi
exit 0

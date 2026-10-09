#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
#
# Synchronise the ParadisEO roadmap issues (ECH-01..04) on
# hyperpolymath/echidna with their specs under issues/.
#
# For each issue the body is generated fresh from its own spec file
# (everything after the "# " title line, so the SPDX header is dropped),
# and the spec's labels are added. Existing labels are kept. Nothing is
# closed, recreated or retitled.
#
# Usage:
#   scripts/issues/sync-roadmap-issues.sh            # dry run (default)
#   scripts/issues/sync-roadmap-issues.sh --apply    # write to GitHub
#   scripts/issues/sync-roadmap-issues.sh --apply --overwrite
#                                     # also replace bodies a human has edited
#   scripts/issues/sync-roadmap-issues.sh --verify   # check only
#
# Needs: gh (authenticated with Issues: write for --apply), jq, awk, sed.
# A 403 "Resource not accessible by integration" means the token or App
# lacks Issues: write. The script stops at the first failed write.
#
# Safety: --apply only replaces a body that still carries the original
# SPDX header (the known-bad first upload) or already equals the spec.
# Any other body was edited deliberately; it is left alone and reported
# unless --overwrite is also given.

set -euo pipefail

REPO="${REPO:-hyperpolymath/echidna}"
ROOT="$(git rev-parse --show-toplevel)"
SPECS="$ROOT/issues"
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT

# issue-number  spec-file  labels (space-separated; enhancement is already attached)
MAP=(
  "420|echidna-01-pareto-moeo.md|area:verification rust optimization"
  "421|echidna-02-cmaes-julia-gnn.md|area:ml julia tuning"
  "422|echidna-03-chapel-island-migration.md|area:parallel chapel concurrency"
  "424|echidna-04-ffi-abi-bridge.md|area:abi zig idris2 ffi"
)

mode="dry-run"
overwrite=0
for arg in "$@"; do
  case "$arg" in
    --apply) mode="apply" ;;
    --verify) mode="verify" ;;
    --dry-run) mode="dry-run" ;;
    --overwrite) overwrite=1 ;;
    *) echo "unknown argument: $arg" >&2; exit 2 ;;
  esac
done

body_of() {
  # Everything after the first "# " heading, minus one leading blank line.
  awk 'f;/^# /{f=1}' "$1" | sed '1{/^$/d}'
}

# Pre-flight: every spec exists, every body is well formed and distinct.
declare -A seen=()
for row in "${MAP[@]}"; do
  IFS='|' read -r n file labels <<<"$row"
  spec="$SPECS/$file"
  [[ -f "$spec" ]] || { echo "missing spec: $spec" >&2; exit 1; }
  body_of "$spec" >"$WORK/body-$n.md"
  head -1 "$WORK/body-$n.md" | grep -q '^- \*\*Repository:\*\* ' \
    || { echo "#$n: body does not start with '- **Repository:**'" >&2; exit 1; }
  ! grep -q 'SPDX' "$WORK/body-$n.md" \
    || { echo "#$n: body contains SPDX" >&2; exit 1; }
  sum="$(sha256sum <"$WORK/body-$n.md" | cut -d' ' -f1)"
  [[ -z "${seen[$sum]:-}" ]] || { echo "#$n: body identical to #${seen[$sum]}" >&2; exit 1; }
  seen[$sum]="$n"
done

# Make sure every label exists before writing anything.
existing="$(gh label list --repo "$REPO" --limit 500 --json name --jq '.[].name')"
for row in "${MAP[@]}"; do
  IFS='|' read -r n _ labels <<<"$row"
  for l in $labels; do
    grep -qxF "$l" <<<"$existing" || { echo "label missing on $REPO: $l" >&2; exit 1; }
  done
done

# Classify the live body: spdx (known-bad upload), spec (in sync), edited.
classify() {
  local n="$1" live
  live="$(gh issue view "$n" --repo "$REPO" --json body --jq .body | tr -d '\r')"
  if [[ "$live" == "$(cat "$WORK/body-$n.md")" ]]; then echo spec
  elif grep -q 'SPDX-License-Identifier' <<<"$live"; then echo spdx
  else echo edited
  fi
}

skipped=0
if [[ "$mode" == "apply" ]]; then
  for row in "${MAP[@]}"; do
    IFS='|' read -r n _ labels <<<"$row"
    state="$(classify "$n")"
    if [[ "$state" == "spec" ]]; then
      echo "#$n: body already matches spec"
    elif [[ "$state" == "edited" && "$overwrite" -eq 0 ]]; then
      echo "#$n: live body was edited by hand; NOT replacing (use --overwrite)"
      skipped=1
    else
      echo "#$n: updating body (was: $state)"
      gh api -X PATCH "repos/$REPO/issues/$n" -F "body=@$WORK/body-$n.md" --silent
    fi
    args=()
    for l in $labels; do args+=(-f "labels[]=$l"); done
    echo "#$n: adding labels: $labels"
    gh api -X POST "repos/$REPO/issues/$n/labels" "${args[@]}" --silent
  done
elif [[ "$mode" == "dry-run" ]]; then
  for row in "${MAP[@]}"; do
    IFS='|' read -r n file labels <<<"$row"
    state="$(classify "$n")"
    case "$state" in
      spec) action="body already matches spec" ;;
      spdx) action="would replace body (live body is the SPDX upload)" ;;
      edited) action="live body was edited by hand; would replace only with --overwrite" ;;
    esac
    echo "#$n: $action; would ensure labels: $labels"
  done
fi

# Verification (all modes): compare live state with the specs.
fail=0
for row in "${MAP[@]}"; do
  IFS='|' read -r n _ labels <<<"$row"
  live="$(gh issue view "$n" --repo "$REPO" --json body,labels)"
  live_body="$(jq -r .body <<<"$live" | tr -d '\r')"
  live_labels="$(jq -r '.labels[].name' <<<"$live")"
  status="ok"
  [[ "$live_body" == "$(cat "$WORK/body-$n.md")" ]] || status="body differs from spec"
  for l in enhancement $labels; do
    grep -qxF -- "$l" <<<"$live_labels" || status="$status; missing label $l"
  done
  echo "#$n: $status (labels: $(paste -sd, <<<"$live_labels"))"
  [[ "$status" == "ok" ]] || fail=1
done

if [[ "$mode" == "dry-run" && "$fail" -ne 0 ]]; then
  echo "dry run: differences above are expected until --apply is run"
  exit 0
fi
[[ "$skipped" -eq 0 ]] || echo "some bodies were left alone because they were edited by hand"
exit "$fail"

#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Copyright (c) 2026 Jonathan D.A. Jewell
# Exit 0: audited without vulnerabilities; 1: finding; 2: incomplete/NOT RUN.
set -euo pipefail

for tool in cargo-audit jq; do
  if ! command -v "$tool" >/dev/null 2>&1; then
    echo "::error::$tool is missing; dependency audit NOT RUN"
    exit 2
  fi
done
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)
cd -- "$repo_root"
report_dir=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/echidna-audit-report.XXXXXX")
summary="${GITHUB_STEP_SUMMARY:-$report_dir/summary.md}"
{
  echo '## Dependency audit'
  echo
  printf 'Revision: `%s`. Tool: `%s`.\n\n' "$(git rev-parse HEAD)" "$(cargo-audit --version)"
} >> "$summary"

status=0
for lockfile in Cargo.lock fuzz/Cargo.lock; do
  if [[ ! -f "$lockfile" ]]; then
    echo "::error::$lockfile is missing; dependency audit NOT RUN"
    printf '### %s — NOT RUN (lockfile missing)\n\n' "$lockfile" >> "$summary"
    status=2
    continue
  fi
  report="$report_dir/${lockfile//\//-}.json"
  stderr="$report.stderr"
  audit_exit=0
  cargo-audit audit --file "$lockfile" --json > "$report" 2> "$stderr" || audit_exit=$?
  cat "$stderr"
  if ! jq -e '(.vulnerabilities.found | type) == "boolean"' "$report" >/dev/null 2>&1; then
    result='NOT RUN (no complete audit report)'
    status=2
  elif jq -e '.vulnerabilities.found' "$report" >/dev/null; then
    result='FAILED (vulnerabilities found)'
    if [[ "$status" -eq 0 ]]; then status=1; fi
  elif [[ "$audit_exit" -ne 0 ]]; then
    result="NOT RUN (tool exited $audit_exit)"
    status=2
  else
    result='PASSED (no known vulnerabilities)'
  fi
  printf '%s: %s\n' "$lockfile" "$result"
  {
    printf '### %s — %s\n\n' "$lockfile" "$result"
    printf 'Lockfile SHA-256: `%s`.\n\n' "$(sha256sum "$lockfile" | cut -d ' ' -f 1)"
    echo 'Tool output from this execution (no second audit):'
    echo
    echo '```json'
    cat "$report"
    echo
    echo '```'
    echo
  } >> "$summary"
done
exit "$status"

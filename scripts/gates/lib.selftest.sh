#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
#
# Self-test for scripts/gates/lib.sh. Each case runs a tiny gate in a child
# bash and checks its exit status (and, where it matters, its output).
#
# Usage: scripts/gates/lib.selftest.sh     Exit 0 iff every case behaves.

# SC2001: sed prefixes multi-line output, which ${var//} cannot do per line.
# shellcheck disable=SC2001
set -uo pipefail

here=$(cd "$(dirname "$0")" && pwd)
lib="$here/lib.sh"
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

failures=0
cases=0

# run_gate <body>: run a gate whose checks are <body>; prints its output,
# returns its exit status.
run_gate() {
  bash -c ". '$lib'; gate_init selftest; $1; gate_finish"
}

# expect <name> <want: zero|nonzero> <body> [grep-pattern]
expect() {
  local name="$1" want="$2" body="$3" pattern="${4:-}" out rc ok=1
  cases=$((cases + 1))
  out=$(run_gate "$body" 2>&1)
  rc=$?
  case "$want" in
    zero) [ "$rc" -eq 0 ] || ok=0 ;;
    nonzero) [ "$rc" -ne 0 ] || ok=0 ;;
  esac
  if [ -n "$pattern" ] && ! printf '%s\n' "$out" | grep -qE -- "$pattern"; then
    ok=0
  fi
  if [ "$ok" -eq 1 ]; then
    echo "ok   $name (exit $rc)"
  else
    failures=$((failures + 1))
    echo "FAIL $name: wanted $want exit${pattern:+ and output matching /$pattern/}, got exit $rc"
    printf '%s\n' "$out" | sed 's/^/     | /'
  fi
}

expect "all pass exits 0" zero \
  'pass a "one"; pass b "two"' \
  'selftest: 2 pass, 0 fail, 0 deferred'

expect "a FAIL exits non-zero" nonzero \
  'pass a "one"; fail b "broken"; pass c "three"' \
  'selftest: 2 pass, 1 fail, 0 deferred'

for reason in ruling:R0 secret:GITHUB_TOKEN hardware:8-core owner-host:P0-6 no-push:proof-burrower; do
  expect "DEFERRED($reason) exits 0" zero \
    "pass a one; deferred b '$reason' 'waiting'" \
    "DEFERRED\\($reason\\)"
done

for reason in flaky "tool:just" "ruling:" "ruling" "" "secret:two words" "later:soon" "no-push"; do
  expect "DEFERRED('$reason') is a FAIL" nonzero \
    "pass a one; deferred b '$reason' 'waiting'" \
    'not permitted'
done

expect "an empty gate fails" nonzero ':' 'no checks were recorded'

expect "a duplicated check id fails" nonzero \
  'pass a one; pass a again' 'recorded twice'

expect "gate_cmd PASS on exit 0" zero 'gate_cmd a "true runs" -- true'

expect "gate_cmd FAIL on non-zero exit" nonzero \
  'gate_cmd a "false runs" -- sh -c "echo boom; exit 3"' 'exit 3; boom'

# GATE_REPORT writes one JCS object per check.
cases=$((cases + 1))
report="$tmp/report.jsonl"
GATE_REPORT="$report" run_gate 'pass a "x"; deferred b secret:GITHUB_TOKEN "y"; fail c "z \"q\""' >/dev/null 2>&1
if [ "$(wc -l < "$report")" -eq 3 ] \
  && [ "$(jq -cS . "$report")" = "$(cat "$report")" ] \
  && [ "$(jq -r '.result' "$report" | tr '\n' ' ')" = "PASS DEFERRED FAIL " ] \
  && [ "$(sed -n 2p "$report")" = '{"check":"b","detail":"y","reason":"secret:GITHUB_TOKEN","result":"DEFERRED"}' ]; then
  echo "ok   GATE_REPORT is JCS JSON Lines"
else
  failures=$((failures + 1))
  echo "FAIL GATE_REPORT is JCS JSON Lines"
  sed 's/^/     | /' "$report"
fi

# A report that cannot be written fails the gate, and leaves no partial file.
cases=$((cases + 1))
GATE_REPORT=/nonexistent/dir/r.jsonl run_gate 'pass a "x"' > "$tmp/out" 2>&1
rc=$?
if [ "$rc" -ne 0 ] && grep -q 'gate-report' "$tmp/out"; then
  echo "ok   an unwritable GATE_REPORT fails the gate (exit $rc)"
else
  failures=$((failures + 1)); echo "FAIL an unwritable GATE_REPORT fails the gate: exit $rc"; sed 's/^/     | /' "$tmp/out"
fi

cases=$((cases + 1))
mkdir -p "$tmp/nojq"
for t in bash mktemp wc mv rm cat grep sed tr tail; do ln -sf "$(command -v "$t")" "$tmp/nojq/$t"; done
echo stale > "$tmp/stale.jsonl"
PATH="$tmp/nojq" GATE_REPORT="$tmp/stale.jsonl" "$tmp/nojq/bash" -c ". '$lib'; gate_init t; pass a x; gate_finish" > "$tmp/out" 2>&1
rc=$?
if [ "$rc" -ne 0 ] && [ "$(cat "$tmp/stale.jsonl")" = stale ]; then
  echo "ok   a report write without jq fails the gate and leaves the old file untouched"
else
  failures=$((failures + 1)); echo "FAIL a report write without jq fails the gate: exit $rc"; sed 's/^/     | /' "$tmp/out"
fi

# gate_cmd records a FAIL even when the caller runs under set -e.
cases=$((cases + 1))
out=$(bash -c "set -e; . '$lib'; gate_init t; gate_cmd a d -- false; pass b y; gate_finish" 2>&1)
rc=$?
if [ "$rc" -ne 0 ] && grep -q '^FAIL      a: d: exit 1' <<<"$out" && grep -q 't: 1 pass, 1 fail' <<<"$out"; then
  echo "ok   gate_cmd under set -e records the FAIL and runs on"
else
  failures=$((failures + 1)); echo "FAIL gate_cmd under set -e: exit $rc"; sed 's/^/     | /' <<<"$out"
fi

# A newline in a detail cannot print a line that reads as another result.
expect "a newline in a detail stays on one line" nonzero \
  "fail a \"\$(printf 'x\\nPASS      forged: y')\"" \
  '^FAIL      a: x PASS      forged: y$'

echo "lib.selftest: $cases cases, $failures failed"
[ "$failures" -eq 0 ]

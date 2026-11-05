#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
#
# Self-test for scripts/gates/lib.sh. Each case runs a tiny gate in a child
# bash and checks its exit status (and, where it matters, its output).
#
# Usage: scripts/gates/lib.selftest.sh     Exit 0 iff every case behaves.

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

echo "lib.selftest: $cases cases, $failures failed"
[ "$failures" -eq 0 ]

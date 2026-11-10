#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
# Offline planted controls for the execution/receipt boundary, not scanner detections.
set -euo pipefail
repo=$(git rev-parse --show-toplevel)
adapter="$repo/scripts/ci/static-analysis-evidence.sh"
tmp=$(mktemp -d)
trap 'rm -rf -- "$tmp"' EXIT
mkdir "$tmp/input"
git -C "$tmp/input" init -q
printf 'fn main() {}\n' > "$tmp/input/main.rs"
git -C "$tmp/input" add main.rs
git -C "$tmp/input" -c user.name='Scanner fixture' -c user.email='fixture@example.invalid' \
  -c commit.gpgsign=false commit -qm 'Synthetic scanner input'
export SCAN_ROOT="$tmp/input" SCAN_EXPECTED_SHA
SCAN_EXPECTED_SHA=$(git -C "$SCAN_ROOT" rev-parse HEAD)
export GITHUB_REPOSITORY=fixture/static-analysis GITHUB_RUN_ID=123 GITHUB_RUN_ATTEMPT=2
export HYPATIA_REF=aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
export PANIC_ATTACK_REF=bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb
unset GITHUB_OUTPUT GITHUB_STEP_SUMMARY
export MOCK_REPORT="$tmp/report.json" MOCK_ARGS="$tmp/args" MOCK_EXIT=0

cat > "$tmp/scanner" <<'MOCK'
#!/usr/bin/env bash
set -euo pipefail
printf '%s\n' "$@" > "$MOCK_ARGS"
if [[ "$1" = scan ]]; then
  cat "$MOCK_REPORT"
else
  while [[ "$#" -gt 0 ]]; do
    if [[ "$1" = --output ]]; then cp "$MOCK_REPORT" "$2"; break; fi
    shift
  done
fi
exit "$MOCK_EXIT"
MOCK
chmod +x "$tmp/scanner"
digest=$(sha256sum "$tmp/scanner" | cut -d' ' -f1)
jq -cn --arg sha "$HYPATIA_REF" --arg digest "$digest" '{source_sha:$sha,binary_sha256:$digest}' > "$tmp/hypatia-source.json"
jq -cn --arg sha "$PANIC_ATTACK_REF" --arg digest "$digest" '{source_sha:$sha,binary_sha256:$digest}' > "$tmp/panic-source.json"
passed=0

expect_exit() {
  local wanted=$1 actual=0
  shift
  "$@" > "$tmp/control.log" 2>&1 || actual=$?
  if [[ "$actual" -ne "$wanted" ]]; then
    cat "$tmp/control.log" >&2
    printf 'Expected exit %s, received %s: %s\n' "$wanted" "$actual" "$*" >&2
    exit 1
  fi
  passed=$((passed + 1))
}

hypatia() {
  bash "$adapter" scan hypatia "$HYPATIA_REF" "$tmp/scanner" "$tmp/hypatia-source.json" "$tmp/hypatia"
}
panic() {
  bash "$adapter" scan panic-attack "$PANIC_ATTACK_REF" "$tmp/scanner" "$tmp/panic-source.json" "$tmp/panic"
}
bridge() {
  bash "$adapter" scan patch-bridge "$PANIC_ATTACK_REF" "$tmp/scanner" "$tmp/panic-source.json" "$tmp/bridge"
}

# Complete clean output is legitimate; empty bytes, malformed and multiple
# JSON documents are not a substitute for that successful scan.
printf '[]\n' > "$MOCK_REPORT"
expect_exit 0 hypatia
jq -e '.status == "ran" and .counts.total == 0' "$tmp/hypatia/receipt.json" >/dev/null
expect_exit 0 bash "$adapter" gate "$tmp/hypatia/receipt.json"
# A failed-jobs-only rerun may reuse earlier successful jobs from this same
# run and exact source. Future/invalid attempts and another run are rejected.
jq '.provenance.run_attempt = "1"' "$tmp/hypatia/receipt.json" > "$tmp/prior-attempt.json"
expect_exit 0 bash "$adapter" gate "$tmp/prior-attempt.json"
for bad_attempt in 0 3 invalid; do
  jq --arg attempt "$bad_attempt" '.provenance.run_attempt = $attempt' \
    "$tmp/hypatia/receipt.json" > "$tmp/bad-attempt.json"
  expect_exit 2 bash "$adapter" gate "$tmp/bad-attempt.json"
done
jq '.provenance.run_id = "124"' "$tmp/prior-attempt.json" > "$tmp/other-run.json"
expect_exit 2 bash "$adapter" gate "$tmp/other-run.json"
: > "$MOCK_REPORT"
expect_exit 2 hypatia
jq -e '.status == "error" and .counts == null and .report == null' "$tmp/hypatia/receipt.json" >/dev/null
printf 'not-json\n' > "$MOCK_REPORT"
expect_exit 2 hypatia
printf '[]\n[]\n' > "$MOCK_REPORT"
expect_exit 2 hypatia
printf '[]\n' > "$MOCK_REPORT"
export MOCK_EXIT=2
expect_exit 2 hypatia
jq -e '.exit_code == 2 and .counts == null' "$tmp/hypatia/receipt.json" >/dev/null
export MOCK_EXIT=0
printf '[{"severity":"critical","reason":"planted critical control"}]\n' > "$MOCK_REPORT"
expect_exit 0 hypatia
expect_exit 1 bash "$adapter" gate "$tmp/hypatia/receipt.json"
jq -e '.report[0].reason == "planted critical control" and .counts.critical == 1' "$tmp/hypatia/receipt.json" >/dev/null
cp "$tmp/hypatia/receipt.json" "$tmp/qualified-hypatia.json"
jq '.counts.critical = 0' "$tmp/qualified-hypatia.json" > "$tmp/inconsistent-receipt.json"
expect_exit 2 bash "$adapter" gate "$tmp/inconsistent-receipt.json"
printf '{"status":"ran","tool":"hypatia","counts":{"critical":null}}\n' > "$tmp/inconsistent-receipt.json"
expect_exit 2 bash "$adapter" gate "$tmp/inconsistent-receipt.json"

expect_exit 2 bash "$adapter" scan hypatia "$HYPATIA_REF" "$tmp/missing" "$tmp/hypatia-source.json" "$tmp/missing-tool"
jq -e '.status == "not_run" and .exit_code == null and .counts == null' "$tmp/missing-tool/receipt.json" >/dev/null
expect_exit 2 bash "$adapter" scan hypatia "$HYPATIA_REF" "$tmp/scanner" "$tmp/missing-source" "$tmp/missing-source-result"
printf '// changed input\n' >> "$SCAN_ROOT/main.rs"
expect_exit 2 hypatia
jq -e '.status == "not_run" and .provenance.worktree_clean == false' "$tmp/hypatia/receipt.json" >/dev/null
git -C "$SCAN_ROOT" checkout -- main.rs

# panic-attack reports an object with explicit coverage. The pinned scanner's
# own suppressed markers remain in raw evidence, and never inflate gate counts.
printf '%s\n' '{"schema_version":"2.6","coverage":{"status":"complete","candidate_files":1,"analyzed_files":1},"weak_points":[{"severity":"Critical","description":"suppressed fixture","suppressed":true},{"severity":"High","description":"live fixture"}]}' > "$MOCK_REPORT"
expect_exit 0 panic
grep -Fxq -- '--fail-on-incomplete' "$MOCK_ARGS"
jq -e '.counts.critical == 0 and .counts.high == 1 and (.report.weak_points|length) == 2' "$tmp/panic/receipt.json" >/dev/null
cp "$tmp/panic/receipt.json" "$tmp/qualified-panic.json"
# Real repositories have large coverage inventories: do not pass reports as
# shell arguments (Linux limits a single argument to roughly 128 KiB).
jq '.coverage.candidate_files = 2000 | .coverage.analyzed_files = 2000 |
  .coverage.inputs = [range(0;2000) | {path:("fixture/source/" + tostring + "/long-module-name-for-coverage-regression.rs"),status:"analyzed"}]' \
  "$MOCK_REPORT" > "$tmp/large-report.json"
cp "$tmp/large-report.json" "$MOCK_REPORT"
expect_exit 0 panic
jq -e '(.coverage.inputs|length) == 2000 and .status == "ran"' "$tmp/panic/receipt.json" >/dev/null
jq '.coverage.status = "partial"' "$MOCK_REPORT" > "$tmp/partial.json"
cp "$tmp/partial.json" "$MOCK_REPORT"
expect_exit 2 panic
jq -e '.counts == null and .report == null' "$tmp/panic/receipt.json" >/dev/null
jq -e '.coverage.status == "partial"' "$tmp/panic/report.json" >/dev/null
printf '[]\n' > "$MOCK_REPORT"
expect_exit 2 panic

# Bridge needs its real subcommand and output-file contract. CLI/parser errors
# cannot turn into a fabricated zero-CVE report; no offline zero is requested.
printf '%s\n' '{"schema_version":"0.3.0","vulnerability_data":"queried","total_dependencies":2,"vulnerable_dependencies":1,"cves":[{"classification":"unmitigable"}],"mitigated":0,"unmitigable":1,"concatenative":0,"informational":0}' > "$MOCK_REPORT"
expect_exit 0 bridge
grep -Fxq bridge "$MOCK_ARGS"
grep -Fxq triage "$MOCK_ARGS"
if grep -Fxq -- '--offline' "$MOCK_ARGS"; then exit 1; fi
expect_exit 0 bash "$adapter" gate "$tmp/bridge/receipt.json"
cp "$tmp/bridge/receipt.json" "$tmp/qualified-bridge.json"
export MOCK_EXIT=2
expect_exit 2 bridge
export MOCK_EXIT=0
jq '.unmitigable = 0' "$MOCK_REPORT" > "$tmp/inconsistent.json"
cp "$tmp/inconsistent.json" "$MOCK_REPORT"
expect_exit 2 bridge
# A report that never reached the vulnerability feed is not a zero-CVE result.
# Paired: the same zero-CVE report qualifies only when the feed was queried.
printf '%s\n' '{"schema_version":"0.3.0","vulnerability_data":"queried","total_dependencies":2,"vulnerable_dependencies":0,"cves":[],"mitigated":0,"unmitigable":0,"concatenative":0,"informational":0}' > "$MOCK_REPORT"
expect_exit 0 bridge
expect_exit 0 bash "$adapter" gate "$tmp/bridge/receipt.json"
printf '%s\n' '{"schema_version":"0.3.0","vulnerability_data":"offline-unavailable","total_dependencies":2,"vulnerable_dependencies":0,"cves":[],"mitigated":0,"unmitigable":0,"concatenative":0,"informational":0}' > "$MOCK_REPORT"
expect_exit 2 bridge
# A 0.3.0 report with no feed status at all must not qualify either.
printf '%s\n' '{"schema_version":"0.3.0","total_dependencies":2,"vulnerable_dependencies":0,"cves":[],"mitigated":0,"unmitigable":0,"concatenative":0,"informational":0}' > "$MOCK_REPORT"
expect_exit 2 bridge
# The pre-0.3.0 contract has no feed status, so it cannot qualify either.
printf '%s\n' '{"schema_version":"0.2.0","total_dependencies":2,"vulnerable_dependencies":1,"cves":[{"classification":"unmitigable"}],"mitigated":0,"unmitigable":1,"concatenative":0,"informational":0}' > "$MOCK_REPORT"
expect_exit 2 bridge

# B1 (bridge-gate.yml): exit 1 only for a reachable unmitigable CVE in a
# qualified report. No qualified report, or an unknown reachability value, is
# exit 2: it is never a pass.
b1() { bash "$adapter" bridge-b1 "$tmp/bridge/receipt.json"; }
bridge_report() { # <vulnerability_data> <classification> <reachability status>
  local data=$1 class=$2 reach=$3
  jq -cn --arg data "$data" --arg class "$class" --arg reach "$reach" '
    {schema_version:"0.3.0",vulnerability_data:$data,total_dependencies:2,vulnerable_dependencies:1,
     cves:[{classification:$class,reachability:{status:$reach},vulnerability:{id:"FIXTURE-0001"},rationale:"planted"}],
     mitigated:(if $class == "mitigable" then 1 else 0 end),unmitigable:(if $class == "unmitigable" then 1 else 0 end),
     concatenative:0,informational:(if $class == "informational" then 1 else 0 end)}' > "$MOCK_REPORT"
}
bridge_report queried unmitigable reachable
expect_exit 0 bridge
expect_exit 1 b1
grep -Fq 'FIXTURE-0001: planted' "$tmp/control.log"
# Paired: the same CVE does not block when it is not reachable or is mitigable.
for reach in unreachable phantom-declared phantom-transitive; do
  bridge_report queried unmitigable "$reach"
  expect_exit 0 bridge
  expect_exit 0 b1
done
bridge_report queried mitigable reachable
expect_exit 0 bridge
expect_exit 0 b1
printf '%s\n' '{"schema_version":"0.3.0","vulnerability_data":"queried","total_dependencies":2,"vulnerable_dependencies":0,"cves":[],"mitigated":0,"unmitigable":0,"concatenative":0,"informational":0}' > "$MOCK_REPORT"
expect_exit 0 bridge
expect_exit 0 b1
# The spelling the workflow compared before #481 never matched the report.
# An unknown status is refused, so a renamed value cannot pass in silence.
bridge_report queried unmitigable Reachable
expect_exit 0 bridge
expect_exit 2 b1
# A report whose feed was not queried leaves no qualified receipt to judge.
for data in offline-unavailable no-dependencies; do
  bridge_report "$data" unmitigable reachable
  expect_exit 2 bridge
  expect_exit 2 b1
done
# The verdict checks the report itself, not only that a receipt exists: a
# receipt whose report says the feed was not queried, or says nothing about
# the feed, is refused. Without that check this zero-CVE report would pass.
printf '%s\n' '{"schema_version":"0.3.0","vulnerability_data":"queried","total_dependencies":2,"vulnerable_dependencies":0,"cves":[],"mitigated":0,"unmitigable":0,"concatenative":0,"informational":0}' > "$MOCK_REPORT"
expect_exit 0 bridge
jq '.report.vulnerability_data = "offline-unavailable"' "$tmp/bridge/receipt.json" > "$tmp/unqueried-receipt.json"
expect_exit 2 bash "$adapter" bridge-b1 "$tmp/unqueried-receipt.json"
jq 'del(.report.vulnerability_data)' "$tmp/bridge/receipt.json" > "$tmp/unqueried-receipt.json"
expect_exit 2 bash "$adapter" bridge-b1 "$tmp/unqueried-receipt.json"
# Another scanner's receipt and a missing receipt are not CVE results.
expect_exit 2 bash "$adapter" bridge-b1 "$tmp/qualified-hypatia.json"
expect_exit 2 bash "$adapter" bridge-b1 "$tmp/no-such-receipt.json"

# Deposit preserves actual critical findings even though their gate failed.
# Only mutually matching completed scan receipts may create the legacy artifact.
mkdir -p "$tmp/findings/"{panic-attack-findings,hypatia-findings,bridge-report}
cp "$tmp/qualified-panic.json" "$tmp/findings/panic-attack-findings/receipt.json"
cp "$tmp/qualified-hypatia.json" "$tmp/findings/hypatia-findings/receipt.json"
cp "$tmp/qualified-bridge.json" "$tmp/findings/bridge-report/receipt.json"
expect_exit 0 bash "$adapter" deposit "$tmp/findings"
jq -e '.scan_completion.complete and .scan_completion.fleet_ingestion == "not_confirmed"
  and (.findings|length) == 2 and any(.findings[]; .severity == "critical")' "$tmp/findings/unified-findings.json" >/dev/null
mv "$tmp/findings/bridge-report/receipt.json" "$tmp/bridge-backup.json"
expect_exit 2 bash "$adapter" deposit "$tmp/findings"
[[ ! -e "$tmp/findings/unified-findings.json" ]]
jq -e '.complete == false' "$tmp/findings/deposit-status.json" >/dev/null
cp "$tmp/bridge-backup.json" "$tmp/findings/bridge-report/receipt.json"
jq '.provenance.commit_sha = "cccccccccccccccccccccccccccccccccccccccc"' "$tmp/qualified-hypatia.json" > "$tmp/findings/hypatia-findings/receipt.json"
expect_exit 2 bash "$adapter" deposit "$tmp/findings"
[[ ! -e "$tmp/findings/unified-findings.json" ]]
cp "$tmp/qualified-hypatia.json" "$tmp/findings/hypatia-findings/receipt.json"
cp "$tmp/missing-tool/receipt.json" "$tmp/findings/panic-attack-findings/receipt.json"
expect_exit 2 bash "$adapter" deposit "$tmp/findings"
[[ ! -e "$tmp/findings/unified-findings.json" ]]
printf 'not-json\n' > "$tmp/findings/panic-attack-findings/receipt.json"
expect_exit 2 bash "$adapter" deposit "$tmp/findings"
[[ ! -e "$tmp/findings/unified-findings.json" ]]
printf '%s receipt controls passed\n' "$passed"

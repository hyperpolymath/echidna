#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
# Execution receipts for Static Analysis Gate. These are scan observations,
# never verified repair outcomes or evidence that fleet learning occurred.
set -euo pipefail

root=${SCAN_ROOT:-$PWD}
subject=$(git -C "$root" rev-parse HEAD)
subject_tree=$(git -C "$root" rev-parse 'HEAD^{tree}')
worktree_clean=false
if [[ -z "$(git -C "$root" status --porcelain)" ]]; then worktree_clean=true; fi
expected=${SCAN_EXPECTED_SHA:?the workflow must name the exact scanned commit}
repository=${GITHUB_REPOSITORY:-local/fixture}
run_id=${GITHUB_RUN_ID:-local}
run_attempt=${GITHUB_RUN_ATTEMPT:-1}

one_json() {
  local report=$1
  jq -e -s 'length == 1' "$report" >/dev/null 2>&1
}

valid_report() {
  local tool=$1 report=$2
  case "$tool" in
    hypatia)
      jq -e -s 'length == 1 and (.[0] | type == "array" and all(.[];
        type == "object" and (.severity as $s |
          ["critical","high","medium","warn","low","info","informational"] | index($s) != null)))' "$report" >/dev/null 2>&1 ;;
    panic-attack)
      jq -e -s 'length == 1 and (.[0] | type == "object" and .schema_version == "2.6"
        and .coverage.status == "complete" and (.coverage.candidate_files | type == "number" and . > 0 and floor == .)
        and .coverage.analyzed_files == .coverage.candidate_files
        and (.weak_points | type == "array") and all(.weak_points[];
          type == "object" and (.severity as $s | ["Critical","High","Medium","Low"] | index($s) != null)))' "$report" >/dev/null 2>&1 ;;
    patch-bridge)
      jq -e -s 'length == 1 and (.[0] | type == "object" and .schema_version == "0.3.0" and .vulnerability_data == "queried"
        and (.total_dependencies | type == "number" and . > 0 and floor == .)
        and (.cves | type == "array")
        and all(.cves[]; type == "object" and (.classification as $c |
          ["mitigable","unmitigable","informational"] | index($c) != null))
        and all(.mitigated,.unmitigable,.concatenative,.informational,.vulnerable_dependencies;
          type == "number" and . >= 0 and floor == .)
        and .mitigated == ([.cves[] | select(.classification == "mitigable")] | length)
        and .unmitigable == ([.cves[] | select(.classification == "unmitigable")] | length)
        and .informational == ([.cves[] | select(.classification == "informational")] | length)
        and .vulnerable_dependencies == (.cves | length))' "$report" >/dev/null 2>&1 ;;
    *) return 1 ;;
  esac
}

counts() {
  local tool=$1 report=$2
  if [[ "$tool" = patch-bridge ]]; then
    jq -c '{mitigated,unmitigable,concatenative,informational,total:(.cves|length)}' "$report"
  else
    jq -c --arg tool "$tool" '
      (if $tool == "panic-attack" then [.weak_points[] | select(.suppressed != true) | .severity | ascii_downcase]
       else [.[].severity | if . == "warn" then "medium" else . end] end) as $s
      | {total:($s|length),critical:([$s[]|select(. == "critical")]|length),
         high:([$s[]|select(. == "high")]|length),medium:([$s[]|select(. == "medium")]|length),
         low:([$s[]|select(. == "low")]|length),info:([$s[]|select(. == "info" or . == "informational")]|length)}' "$report"
  fi
}

scan() {
  local tool=$1 ref=$2 binary=$3 source=$4 out=$5
  mkdir -p "$out"
  local report="$out/report.json" receipt="$out/receipt.json" log="$out/scanner.log"
  local status=not_run reason="scanner build or source receipt is unavailable" rc=null digest="" source_sha=""
  local command='[]' count_json=null
  local null_report="$out/unavailable-report.json" coverage_file="$out/coverage.json" report_path
  printf 'null\n' > "$null_report"
  printf 'null\n' > "$coverage_file"
  report_path=$null_report
  rm -f -- "$report" "$receipt"

  if [[ "$subject" != "$expected" ]] || [[ "$worktree_clean" != true ]]; then
    reason="checkout is dirty or does not match the requested scan commit"
  elif [[ -x "$binary" ]] && [[ -s "$source" ]] && one_json "$source" &&
       jq -e --arg ref "$ref" '.source_sha == $ref and (.binary_sha256 | test("^[0-9a-f]{64}$"))' "$source" >/dev/null; then
    digest=$(sha256sum "$binary" | cut -d' ' -f1)
    source_sha=$(jq -r '.source_sha' "$source")
    if [[ "$digest" != "$(jq -r '.binary_sha256' "$source")" ]]; then
      reason="scanner binary does not match its build receipt"
    else
      local -a argv
      case "$tool" in
        panic-attack) argv=("$binary" assail "$root" --output "$report" --fail-on-incomplete) ;;
        hypatia) argv=("$binary" scan "$root" --format json --exit-zero) ;;
        patch-bridge) argv=("$binary" bridge triage "$root" --output "$report") ;;
        *) echo "Unknown scanner: $tool" >&2; return 2 ;;
      esac
      command=$(jq -cn --args '$ARGS.positional' -- "${argv[@]}")
      rc=0
      if [[ "$tool" = hypatia ]]; then
        timeout 300 "${argv[@]}" > "$report" 2> "$log" || rc=$?
      else
        timeout 300 "${argv[@]}" > "$log" 2>&1 || rc=$?
      fi
      # Preserve the tool's own partial coverage even when its nonzero exit
      # prevents qualification. A partial report is evidence, not a clean scan.
      if [[ "$tool" = panic-attack ]] && one_json "$report" &&
         jq -e 'type == "object" and (.coverage | type == "object")' "$report" >/dev/null 2>&1; then
        jq -c '.coverage' "$report" > "$coverage_file"
      fi
      status=error
      if [[ "$rc" -ne 0 ]]; then
        reason="scanner execution failed or timed out (exit $rc); raw output retained"
      elif ! valid_report "$tool" "$report"; then
        reason="scanner returned no complete report matching its pinned output contract"
      else
        status=ran
        reason=""
        report_path=$report
        count_json=$(counts "$tool" "$report")
        case "$tool" in
          panic-attack) jq -c '.coverage' "$report" > "$coverage_file" ;;
          patch-bridge) jq -c '{mode:"online",total_dependencies}' "$report" > "$coverage_file" ;;
          hypatia) printf '%s\n' '{"mode":"hypatia-default-rules","severity_threshold":"medium","remote_alert_credentials":"not_supplied"}' > "$coverage_file" ;;
          *) echo "Unknown scanner: $tool" >&2; return 2 ;;
        esac
      fi
    fi
  fi
  jq -cn --arg status "$status" --arg tool "$tool" --arg ref "$ref" --arg reason "$reason" \
    --argjson exit_code "$rc" --argjson counts "$count_json" --slurpfile report "$report_path" \
    --arg repo "$repository" --arg sha "$subject" --arg expected "$expected" --arg run "$run_id" \
    --arg attempt "$run_attempt" --arg source "$source_sha" --arg digest "$digest" \
    --arg tree "$subject_tree" --argjson clean "$worktree_clean" \
    --argjson command "$command" --slurpfile coverage "$coverage_file" '
      {status:$status,tool:$tool,ref:$ref,reason:(if $reason == "" then null else $reason end),
       exit_code:$exit_code,counts:$counts,report:$report[0],coverage:$coverage[0],
       provenance:{repository:$repo,commit_sha:$sha,tree_sha:$tree,worktree_clean:$clean,
         expected_sha:$expected,run_id:$run,run_attempt:$attempt,
         source_sha:(if $source == "" then null else $source end),
         binary_sha256:(if $digest == "" then null else $digest end),command:$command},
       evidence_kind:"scanner_observation"}' > "$receipt"
  rm -f -- "$null_report"
  if [[ -n "${GITHUB_OUTPUT:-}" ]]; then
    printf 'status=%s\n' "$status" >> "$GITHUB_OUTPUT"
  fi
  if [[ -n "${GITHUB_STEP_SUMMARY:-}" ]]; then
    {
      printf '## %s\n\nStatus: **%s**\n\nSource: `%s`\n\nScanned commit: `%s`\n\n' "$tool" "$status" "$ref" "$subject"
      if [[ "$status" = ran ]]; then jq -r '.counts | to_entries[] | "- \(.key): \(.value)"' "$receipt"
      else printf '%s. This is not a clean scan.\n' "$reason"; fi
    } >> "$GITHUB_STEP_SUMMARY"
  fi
  if [[ "$status" != ran ]]; then
    printf '::error::%s: %s\n' "$tool" "$reason" >&2
    [[ ! -f "$log" ]] || cat "$log" >&2
    return 2
  fi
}

expected_ref() {
  case "$1" in
    hypatia) printf '%s' "${HYPATIA_REF:?}" ;;
    panic-attack|patch-bridge) printf '%s' "${PANIC_ATTACK_REF:?}" ;;
    *) return 1 ;;
  esac
}

qualified_receipt() {
  local tool=$1 ref=$2 receipt=$3 report=$4 expected_counts
  [[ "$subject" = "$expected" ]] || return 1
  [[ -s "$receipt" ]] && one_json "$receipt" || return 1
  jq -e --arg tool "$tool" --arg ref "$ref" --arg sha "$expected" --arg tree "$subject_tree" \
    --arg repo "$repository" --arg run "$run_id" --arg attempt "$run_attempt" '
      .tool == $tool and .ref == $ref and .status == "ran" and .exit_code == 0
      and .provenance.repository == $repo and .provenance.commit_sha == $sha
      and .provenance.tree_sha == $tree and .provenance.worktree_clean == true
      and .provenance.expected_sha == $sha and .provenance.source_sha == $ref
      and .provenance.run_id == $run
      and (.provenance.run_attempt | test("^[1-9][0-9]*$"))
      and ((.provenance.run_attempt | tonumber) <= ($attempt | tonumber))
      and (.provenance.binary_sha256 | test("^[0-9a-f]{64}$"))' "$receipt" >/dev/null 2>&1 || return 1
  jq '.report' "$receipt" > "$report" || return 1
  valid_report "$tool" "$report" || return 1
  expected_counts=$(counts "$tool" "$report") || return 1
  jq -e --argjson counts "$expected_counts" '.counts == $counts' "$receipt" >/dev/null
}

gate() {
  local receipt=$1 tool ref report
  one_json "$receipt" || return 2
  tool=$(jq -r '.tool' "$receipt")
  ref=$(expected_ref "$tool") || return 2
  report=$(mktemp)
  if ! qualified_receipt "$tool" "$ref" "$receipt" "$report"; then
    rm -f -- "$report"
    echo '::error::Scanner completion receipt is missing, incomplete or inconsistent.' >&2
    return 2
  fi
  rm -f -- "$report"
  if [[ "$tool" = patch-bridge ]]; then
    if [[ "$(jq -r .counts.unmitigable "$receipt")" -gt 0 ]]; then
      echo '::warning::Patch Bridge found unmitigable CVEs; architectural review is required.'
    fi
  elif [[ "$(jq -r .counts.critical "$receipt")" -gt 0 ]]; then
    echo '::error::Critical scanner findings block merge; the original findings remain in the artifact.'
    return 1
  fi
}

deposit() {
  local dir=$1 complete=true tool ref receipt name temp
  mkdir -p "$dir"
  rm -f -- "$dir/unified-findings.json"
  temp=$(mktemp -d)
  trap 'rm -rf -- "$temp"' RETURN
  for tool in panic-attack hypatia patch-bridge; do
    case "$tool" in
      panic-attack) name=panic-attack-findings; ref=${PANIC_ATTACK_REF:?} ;;
      hypatia) name=hypatia-findings; ref=${HYPATIA_REF:?} ;;
      patch-bridge) name=bridge-report; ref=${PANIC_ATTACK_REF:?} ;;
      *) echo "Unknown scanner: $tool" >&2; return 2 ;;
    esac
    receipt="$dir/$name/receipt.json"
    if qualified_receipt "$tool" "$ref" "$receipt" "$temp/$tool-report.json"; then
      jq '{tool,status,ref,provenance,coverage}' "$receipt" > "$temp/$tool-status.json"
      continue
    fi
    complete=false
    local receipt_status=not_run
    if [[ -e "$receipt" ]]; then receipt_status=error; fi
    jq -cn --arg tool "$tool" --arg status "$receipt_status" \
      '{tool:$tool,status:$status,reason:"missing, failed, malformed or mismatched scan receipt"}' > "$temp/$tool-status.json"
  done
  jq -cs --argjson complete "$complete" \
    '{complete:$complete,evidence_kind:"scanner_observation",scanners:.,fleet_ingestion:"not_confirmed",repair_verification:"not_performed"}' \
    "$temp/panic-attack-status.json" "$temp/hypatia-status.json" "$temp/patch-bridge-status.json" > "$dir/deposit-status.json"
  if [[ "$complete" != true ]]; then
    echo '::error::Incomplete scanner evidence; no unified-findings artifact or clean result is produced.' >&2
    return 2
  fi
  jq -cn --arg repo "$repository" --arg sha "$subject" --arg ref "${GITHUB_REF:-local}" \
    --arg run "$run_id" --arg attempt "$run_attempt" --arg ts "$(date -u +%Y-%m-%dT%H:%M:%SZ)" \
    --slurpfile pa "$temp/panic-attack-report.json" --slurpfile hyp "$temp/hypatia-report.json" \
    --slurpfile bridge "$temp/patch-bridge-report.json" --slurpfile status "$dir/deposit-status.json" '
      {schema_version:"1.1.0",repository:$repo,commit_sha:$sha,ref:$ref,run_id:$run,run_attempt:$attempt,timestamp:$ts,
       evidence_kind:"scanner_observation",scan_completion:$status[0],
       findings:([$pa[0].weak_points[] | select(.suppressed != true) |
         . + {scanner:"panic-attack",source_severity:.severity,severity:(.severity|ascii_downcase),reason:.description}]
         + [$hyp[0][] | . + {scanner:"hypatia"}]),patch_bridge:$bridge[0]}' > "$dir/unified-findings.json"
}

case "${1:-}" in
  scan) shift; scan "$@" ;;
  gate) shift; gate "$@" ;;
  deposit) shift; deposit "$@" ;;
  *) echo 'usage: static-analysis-evidence.sh scan TOOL REF BIN SOURCE-RECEIPT OUTPUT-DIR | gate RECEIPT | deposit ARTIFACT-DIR' >&2; exit 2 ;;
esac

#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
#
# Gate convention for the wave gate scripts (scripts/gates/wN.sh).
#
# Every check ends in exactly one of three results:
#
#   PASS                  the property holds, checked now
#   FAIL                  the property does not hold, or could not be checked
#   DEFERRED(<reason>)    the check cannot run yet for one permitted reason
#
# DEFERRED is permitted only for these reason kinds, each with a non-empty
# name after the colon:
#
#   ruling:<id>           an owner ruling not yet taken          (ruling:R0)
#   secret:<name>         a credential not present here          (secret:GITHUB_TOKEN)
#   hardware:<item>       hardware this host does not have       (hardware:8-core)
#   owner-host:<action>   an action only the owner can take      (owner-host:P0-6)
#   no-push:<repo>        push to a consumer repository refused  (no-push:proof-burrower)
#
# Any other reason is recorded as a FAIL. A missing tool, a missing artefact or
# an unreachable network is not a reason to defer: it is a FAIL. A DEFERRED
# check moves to the next wave's gate script and to STATUS (ultraplan
# convention (a)).
#
# Use from a gate script:
#
#   . "$(dirname "$0")/lib.sh"
#   gate_init W0
#   pass     <id> <detail>
#   fail     <id> <detail>
#   deferred <id> <reason> <detail>
#   gate_finish            # prints the summary, exits 0 iff no FAIL
#
# A gate that records no checks fails: an empty gate is not a green gate.
# A check id recorded twice fails, so a copy-paste slip cannot hide a check.
#
# Set GATE_REPORT=<path> to also write one JCS object per check (JSON Lines,
# keys check/detail/reason/result, all strings) for the STATUS generator.
#
# Requires bash 4 and, only when GATE_REPORT is set, jq.

# Not `set -e` here: the sourcing script owns its shell options.

GATE_ALLOWED_DEFER_KINDS="ruling secret hardware owner-host no-push"

gate_init() {
  GATE_NAME="${1:-gate}"
  GATE_IDS=()
  GATE_RESULTS=()
  GATE_REASONS=()
  GATE_DETAILS=()
  GATE_FAILS=0
  GATE_PASSES=0
  GATE_DEFERS=0
}

# _gate_flat <text>: the text on one line. A newline or carriage return in a
# detail could otherwise print a line that reads like another check's result.
_gate_flat() {
  local s="$1"
  s="${s//$'\r'/ }"
  printf '%s' "${s//$'\n'/ }"
}

# _gate_record <id> <result> <reason> <detail>
_gate_record() {
  local id result="$2" reason="$3" detail seen
  id=$(_gate_flat "$1")
  detail=$(_gate_flat "$4")
  if [ -z "$id" ]; then
    id="(unnamed)"
    result=FAIL
    reason=""
    detail="check recorded without an id: $detail"
  fi
  for seen in ${GATE_IDS[@]+"${GATE_IDS[@]}"}; do
    if [ "$seen" = "$id" ]; then
      result=FAIL
      reason=""
      detail="check id recorded twice: $detail"
      id="$id#dup"
      break
    fi
  done
  GATE_IDS+=("$id")
  GATE_RESULTS+=("$result")
  GATE_REASONS+=("$reason")
  GATE_DETAILS+=("$detail")
  case "$result" in
    PASS) GATE_PASSES=$((GATE_PASSES + 1)); printf 'PASS      %s: %s\n' "$id" "$detail" ;;
    DEFERRED) GATE_DEFERS=$((GATE_DEFERS + 1)); printf 'DEFERRED  %s (%s): %s\n' "$id" "$reason" "$detail" ;;
    *) GATE_FAILS=$((GATE_FAILS + 1)); printf 'FAIL      %s: %s\n' "$id" "$detail" ;;
  esac
}

# gate_reason_allowed <reason>: 0 iff the reason is one permitted DEFERRED kind
# with a non-empty, whitespace-free name.
gate_reason_allowed() {
  local reason="$1" kind name k
  case "$reason" in *:*) ;; *) return 1 ;; esac
  kind="${reason%%:*}"
  name="${reason#*:}"
  [[ $name =~ ^[A-Za-z0-9][A-Za-z0-9._#/@+-]*$ ]] || return 1
  for k in $GATE_ALLOWED_DEFER_KINDS; do
    [ "$k" = "$kind" ] && return 0
  done
  return 1
}

pass() { _gate_record "${1:-}" PASS "" "${2:-}"; }

fail() { _gate_record "${1:-}" FAIL "" "${2:-}"; }

deferred() {
  local id="${1:-}" reason="${2:-}" detail="${3:-}"
  if gate_reason_allowed "$reason"; then
    _gate_record "$id" DEFERRED "$reason" "$detail"
  else
    _gate_record "$id" FAIL "" "DEFERRED reason '$reason' is not permitted (allowed kinds: $GATE_ALLOWED_DEFER_KINDS, as kind:name): $detail"
  fi
}

# gate_cmd <id> <detail> -- <command...>: PASS when the command exits 0,
# otherwise FAIL with its exit status and the last lines of its output.
gate_cmd() {
  local id="$1" detail="$2" out rc
  shift 2
  [ "${1:-}" = "--" ] && shift
  # `&& rc=0 || rc=$?` keeps a failing command from aborting a caller that
  # runs under `set -e` before its FAIL is recorded.
  out=$("$@" 2>&1) && rc=0 || rc=$?
  if [ "$rc" -eq 0 ]; then
    pass "$id" "$detail"
  else
    fail "$id" "$detail: exit $rc; $(printf '%s\n' "$out" | tail -n 5 | tr '\n' ' ')"
  fi
}

gate_summary() {
  local i n="${#GATE_IDS[@]}"
  if [ "$n" -eq 0 ]; then
    _gate_record "gate-nonempty" FAIL "" "no checks were recorded"
    n="${#GATE_IDS[@]}"
  fi
  printf '\n== %s gate summary ==\n' "$GATE_NAME"
  for ((i = 0; i < n; i++)); do
    case "${GATE_RESULTS[$i]}" in
      DEFERRED) printf '  %-34s DEFERRED(%s)\n' "${GATE_IDS[$i]}" "${GATE_REASONS[$i]}" ;;
      *) printf '  %-34s %s\n' "${GATE_IDS[$i]}" "${GATE_RESULTS[$i]}" ;;
    esac
  done
  printf '%s: %d pass, %d fail, %d deferred\n' "$GATE_NAME" "$GATE_PASSES" "$GATE_FAILS" "$GATE_DEFERS"
  if [ -n "${GATE_REPORT:-}" ] && ! _gate_write_report "$n"; then
    # The STATUS generator reads this file. A missing, empty or stale report
    # must not sit beside a green exit.
    printf 'FAIL      gate-report: cannot write GATE_REPORT=%s\n' "$GATE_REPORT"
    return 1
  fi
  [ "$GATE_FAILS" -eq 0 ]
}

# _gate_write_report <n>: write the report to a temporary file beside the
# target and move it into place, so a failed write never leaves a partial or
# stale report under the target name.
_gate_write_report() {
  local n="$1" i tmp
  command -v jq >/dev/null 2>&1 || return 1
  tmp=$(mktemp "${GATE_REPORT}.XXXXXX" 2>/dev/null) || return 1
  for ((i = 0; i < n; i++)); do
    jq -cnS --arg check "${GATE_IDS[$i]}" --arg result "${GATE_RESULTS[$i]}" \
      --arg reason "${GATE_REASONS[$i]}" --arg detail "${GATE_DETAILS[$i]}" \
      '{check: $check, detail: $detail, reason: $reason, result: $result}' >> "$tmp" \
      || { rm -f "$tmp"; return 1; }
  done
  [ "$(wc -l < "$tmp")" -eq "$n" ] || { rm -f "$tmp"; return 1; }
  mv -f "$tmp" "$GATE_REPORT" || { rm -f "$tmp"; return 1; }
}

gate_finish() {
  if gate_summary; then
    exit 0
  fi
  exit 1
}

#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
#
# W0 exit gate (ultraplan, section "W0: unjam the gates ...", checks 1-13).
# Every check is PASS, FAIL or DEFERRED(reason) under scripts/gates/lib.sh.
# Exit 0 iff no check FAILs. Run from anywhere inside the repository.
#
# Checks whose artefact arrives from another W0 lane FAIL until that lane
# lands. That is the point of the gate: do not soften a check to get green.
#
# Environment:
#   GITHUB_TOKEN          read token for the GitHub API (checks 1, 2, 11, 12).
#                         Unset: those checks are DEFERRED(secret:GITHUB_TOKEN).
#   W0_REPO               default hyperpolymath/echidna
#   W0_PROBE_PR           number of the no-op probe PR (check 1). Required.
#   W0_BASE               last main commit before W0 (check 2). Default
#                         6dbfea5 (main before #460, the CI-2 merge).
#   W0_HEAD               ref whose first-parent W0 merges are checked
#                         (check 2). Default HEAD.
#   W0_HOTSPOT_GOLDENS    golden directory for check 5, default
#                         tests/golden/hotspot (see hotspot-goldens.sh).
#   W0_CONSUMER_OWNER     owner of the consumer repositories, default
#                         hyperpolymath.
#   W0_CHECK_RE_<REPO>    extended regex for the conformance check-run name in
#                         a consumer repository (REPO upper-cased, - as _).
#                         Defaults: conformance, and for verisimdb
#                         verisim-api (the crate job that runs the L-7 list
#                         test; a bare "list" also matches "Allowlist").
#   GATE_REPORT           also write the results as JCS JSON Lines (lib.sh).
#
# Cross-repo deferral (checks 11 and 12): a repository counts as
# DEFERRED(no-push:<repo>) only when docs/handover/cross-repo/<repo>/ holds
# both a patch (*.patch or *.diff) and the issue text (a file whose name
# contains "issue"); for check 12 the patch must be the Agda one (its name
# contains "agda").
#
# Shapes this gate reads from other lanes' artefacts (state them, so a lane
# that chooses another shape changes this script in the same PR):
#   tests/fixtures/XFAIL.json   one JCS value: an array of entries, or an
#                               object with "entries"; each entry names its
#                               backend in "backend" (or "prover").
#   docs/decisions/ADR-*-rulings-ledger.adoc
#                               one section heading per ruling naming its id
#                               (D-A, ..., D-N, D2, D3, D5, D6, D7), with an
#                               attribute line `:status: open` or
#                               `:status: ruled` in that section; a ruled
#                               section carries a link to the owner's record.
#   docs/proofs/claims.json     one JCS value; an object whose id, name or
#                               claim mentions the Lean/lake build, whose
#                               text names 4.13.0, and which carries a green
#                               result (result/status/outcome) or a
#                               repair item (repair_item/repair/issue).

set -uo pipefail
export LC_ALL=C

here=$(cd "$(dirname "$0")" && pwd)
# shellcheck source=scripts/gates/lib.sh
. "$here/lib.sh"
root=$(git -C "$here" rev-parse --show-toplevel) || { echo "not inside a git checkout" >&2; exit 2; }
cd "$root" || exit 2

REPO="${W0_REPO:-hyperpolymath/echidna}"
OWNER="${W0_CONSUMER_OWNER:-hyperpolymath}"
W0_BASE="${W0_BASE:-6dbfea562beee3c46d754e380dec3dbef95bff24}"
W0_HEAD="${W0_HEAD:-HEAD}"
GOLDENS="${W0_HOTSPOT_GOLDENS:-tests/golden/hotspot}"

gate_init W0

# ---------------------------------------------------------------- helpers

have_token() { [ -n "${GITHUB_TOKEN:-}" ]; }

# gh_get <api path>: GET from the GitHub REST API, body on stdout.
gh_get() {
  curl -fsS --retry 2 \
    -H "Authorization: Bearer $GITHUB_TOKEN" \
    -H "Accept: application/vnd.github+json" \
    -H "X-GitHub-Api-Version: 2022-11-28" \
    "https://api.github.com/$1"
}

# check_runs <repo> <sha>: every check run on the commit, latest per name,
# as a JSON array of {name, status, conclusion}.
check_runs() {
  local repo="$1" sha="$2" page=1 acc='[]' body n
  while :; do
    body=$(gh_get "repos/$repo/commits/$sha/check-runs?per_page=100&page=$page") || return 1
    acc=$(jq -c --argjson acc "$acc" '$acc + .check_runs' <<<"$body")
    n=$(jq '.check_runs | length' <<<"$body")
    [ "$n" -lt 100 ] && break
    page=$((page + 1))
    [ "$page" -gt 20 ] && break
  done
  jq -c 'group_by(.name) | map(max_by(.id) | {name, status, conclusion})' <<<"$acc"
}

# is_jcs <file>: one JSON value, serialised as JCS, one final LF.
# (jq -cS matches JCS for the strings, integers and plain decimals these
# ledgers hold; it is not a general JCS number serialiser.)
is_jcs() {
  local f="$1"
  [ "$(jq -s 'length' "$f" 2>/dev/null)" = 1 ] || return 1
  cmp -s <(jq -cS . "$f") "$f"
}

handover_dir() { printf 'docs/handover/cross-repo/%s' "$1"; }

# has_handover <repo> [patch-name-substring]
has_handover() {
  local d sub="${2:-}" p i
  d=$(handover_dir "$1")
  [ -d "$d" ] || return 1
  p=$(find "$d" -type f \( -name '*.patch' -o -name '*.diff' \) -iname "*${sub}*" | head -1)
  i=$(find "$d" -type f -iname '*issue*' | head -1)
  [ -n "$p" ] && [ -n "$i" ]
}

# ------------------------------------------- (1) probe PR required contexts

check_1() {
  local id="01-probe-pr-required-contexts" rules req sha runs statuses missing ctx ok
  if ! have_token; then
    deferred "$id" secret:GITHUB_TOKEN "the rules and check-runs APIs need a read token"; return
  fi
  if ! rules=$(gh_get "repos/$REPO/rules/branches/main"); then
    fail "$id" "cannot read the live ruleset for $REPO main"; return
  fi
  req=$(jq -r '[.[] | select(.type == "required_status_checks") | .parameters.required_status_checks[].context] | unique | .[]' <<<"$rules")
  if [ -z "$req" ]; then
    fail "$id" "the live ruleset requires no status context; nothing would gate a merge"; return
  fi
  if ! [[ ${W0_PROBE_PR:-} =~ ^[0-9]+$ ]]; then
    fail "$id" "W0_PROBE_PR is not set to the no-op probe PR number ($(wc -l <<<"$req") required contexts to check)"; return
  fi
  if ! sha=$(gh_get "repos/$REPO/pulls/$W0_PROBE_PR" | jq -er '.head.sha'); then
    fail "$id" "cannot read probe PR #$W0_PROBE_PR"; return
  fi
  if ! runs=$(check_runs "$REPO" "$sha") || ! statuses=$(gh_get "repos/$REPO/commits/$sha/status"); then
    fail "$id" "cannot read check runs for probe PR #$W0_PROBE_PR ($sha)"; return
  fi
  missing=()
  while IFS= read -r ctx; do
    ok=$(jq -r --arg c "$ctx" --argjson s "$statuses" '
      ([.[] | select(.name == $c and .conclusion == "success")] | length > 0)
      or ([$s.statuses[] | select(.context == $c and .state == "success")] | length > 0)' <<<"$runs")
    [ "$ok" = true ] || missing+=("$ctx")
  done <<<"$req"
  if [ ${#missing[@]} -eq 0 ]; then
    pass "$id" "probe PR #$W0_PROBE_PR: all $(wc -l <<<"$req") required contexts are success"
  else
    fail "$id" "probe PR #$W0_PROBE_PR: not success: $(printf '%s; ' "${missing[@]}")"
  fi
}

# --------------------------------------- (2) every W0 merge commit is green

check_2() {
  local id="02-w0-merges-green" commits c runs bad statuses st n=0 problems=()
  if ! have_token; then
    deferred "$id" secret:GITHUB_TOKEN "the check-runs API needs a read token"; return
  fi
  if ! commits=$(git rev-list --first-parent "$W0_BASE..$W0_HEAD" 2>/dev/null); then
    fail "$id" "cannot list commits $W0_BASE..$W0_HEAD (fetch history?)"; return
  fi
  if [ -z "$commits" ]; then
    fail "$id" "no W0 merge commits in $W0_BASE..$W0_HEAD"; return
  fi
  for c in $commits; do
    n=$((n + 1))
    if ! runs=$(check_runs "$REPO" "$c") || ! statuses=$(gh_get "repos/$REPO/commits/$c/status"); then
      problems+=("${c:0:9} unreadable"); continue
    fi
    if [ "$(jq 'length' <<<"$runs")" -eq 0 ] && [ "$(jq '.statuses | length' <<<"$statuses")" -eq 0 ]; then
      problems+=("${c:0:9} has no check runs"); continue
    fi
    # skipped and neutral are not failures (GitHub's required-check meaning);
    # anything else that is not success, including in progress, is.
    bad=$(jq -r '[.[] | select((.conclusion // "pending") as $k | ["success","skipped","neutral"] | index($k) | not) | "\(.name)=\(.conclusion // .status)"] | join(", ")' <<<"$runs")
    st=$(jq -r '[.statuses[] | select(.state != "success") | "\(.context)=\(.state)"] | join(", ")' <<<"$statuses")
    [ -n "$bad$st" ] && problems+=("${c:0:9}: ${bad}${bad:+${st:+, }}${st}")
  done
  if [ ${#problems[@]} -eq 0 ]; then
    pass "$id" "$n W0 first-parent commits, every check run success/skipped/neutral (the bypass log stays an owner checkpoint)"
  else
    fail "$id" "$(printf '%s; ' "${problems[@]}")"
  fi
}

# ------------------------------------------------------- (3) cargo audit

check_3() {
  local id="03-cargo-audit"
  if ! cargo audit --version >/dev/null 2>&1; then
    fail "$id" "cargo-audit is not installed (cargo install cargo-audit --locked)"; return
  fi
  gate_cmd "$id" "cargo audit" -- cargo audit
}

# ---------------------------------------------- (4) the W0 safety-net tests

check_4() {
  local id="04-w0-net-tests" t missing=()
  for t in arbiter_props trust_kernel_characterisation prove_output_json; do
    [ -f "tests/$t.rs" ] || missing+=("tests/$t.rs")
  done
  if [ ${#missing[@]} -gt 0 ]; then
    fail "$id" "missing: ${missing[*]}"; return
  fi
  gate_cmd "$id" "cargo test --locked (arbiter_props, trust_kernel_characterisation, prove_output_json)" -- \
    cargo test --locked --test arbiter_props --test trust_kernel_characterisation --test prove_output_json
}

# --------------------------------------------- (5) hotspot-split goldens

check_5() {
  local id="05-hotspot-goldens"
  if [ ! -d "$GOLDENS" ]; then
    fail "$id" "$GOLDENS is missing; capture it on the pre-split tree with scripts/gates/hotspot-goldens.sh capture"; return
  fi
  gate_cmd "$id" "help, route table and just --list match $GOLDENS" -- \
    "$here/hotspot-goldens.sh" check --dir "$GOLDENS"
}

# ---------------------------------------- (6) live fixtures + XFAIL ledger

# Backends V-3 is scoped to (P1, P2 and P3 lanes of W1a), whose vacuous
# Ok(true) or IR fallback may stand in the ledger until V-3 empties it.
XFAIL_ALLOWED="acl2 agda coq cvc5 hol4 hol_light idris2 isabelle lean metamath pvs rocq z3"

check_6() {
  local idx="06a-xfail-ledger" idl="06b-live-fixtures" f="tests/fixtures/XFAIL.json" backends b bad=()
  if [ ! -f "$f" ]; then
    fail "$idx" "$f is missing"
  elif ! is_jcs "$f"; then
    fail "$idx" "$f is not one JCS value with a final LF"
  elif ! backends=$(jq -r 'if type == "array" then . elif type == "object" and (.entries | type) == "array" then .entries else error("neither an array nor an object with an entries array") end
        | map(if type == "object" and ((.backend // .prover) | type) == "string" then (.backend // .prover) else error("an entry names no backend") end)
        | .[]' "$f" 2>&1); then
    fail "$idx" "$f has an unrecognised shape: $backends"
  elif [ -z "$backends" ]; then
    pass "$idx" "$f is JCS and empty"
  else
    for b in $backends; do
      [[ " $XFAIL_ALLOWED " == *" ${b,,} "* ]] || bad+=("$b")
    done
    if [ ${#bad[@]} -eq 0 ]; then
      pass "$idx" "$f is JCS and lists only V-3 backends/IR fallbacks ($(wc -w <<<"$backends") entries)"
    else
      fail "$idx" "$f lists backends outside V-3 scope: ${bad[*]}"
    fi
  fi

  if [ ! -x scripts/ci/live-fixtures.sh ]; then
    fail "$idl" "scripts/ci/live-fixtures.sh is missing or not executable"; return
  fi
  gate_cmd "$idl" "ECHIDNA_FAIL_ON_SKIP=1 scripts/ci/live-fixtures.sh" -- \
    env ECHIDNA_FAIL_ON_SKIP=1 scripts/ci/live-fixtures.sh
}

# ------------------------------------------------ (7) Idris / Agda hygiene

check_7() {
  local wf=.github/workflows/idris2-abi-ci.yml ipkg=src/abi/echidnaabi.ipkg rel mod missing=()
  if [ -f "$wf" ] && grep -E 'postulate' "$wf" | grep -qE 'grep|rg |for pattern in'; then
    pass "07a-idris-postulate-grep" "$wf greps src/abi for postulate"
  else
    fail "07a-idris-postulate-grep" "$wf does not grep for postulate"
  fi

  for rel in EchidnaABI/CapnSchemas.idr CoprocessorForeign.idr; do
    [ -f "src/abi/$rel" ] || continue
    mod=$(sed 's/\.idr$//; s#/#.#g' <<<"$rel")
    grep -qE "^[[:space:]]*(modules[[:space:]]*=|,)[[:space:]]*${mod//./\\.}[[:space:]]*(,|$)" "$ipkg" || missing+=("$mod")
  done
  if [ ${#missing[@]} -eq 0 ]; then
    pass "07b-ipkg-coverage" "CapnSchemas and CoprocessorForeign are in $ipkg or deleted"
  else
    fail "07b-ipkg-coverage" "present but not in $ipkg: ${missing[*]}"
  fi

  local mc=meta-checker/src/Echidna/MetaChecker.agda awf=.github/workflows/agda-meta-checker.yml
  if [ -f "$awf" ] && grep -qE 'agda .*AxiomTrackerCompleteness\.agda' "$awf"; then
    pass "07c-meta-checker-completeness" "$awf type-checks AxiomTrackerCompleteness.agda directly"
  elif [ -f "$mc" ] && grep -qE '^[[:space:]]*(open[[:space:]]+)?import[[:space:]]+Echidna\.AxiomTrackerCompleteness([[:space:]]|$)' "$mc" \
       && [ -f "$awf" ] && grep -qE 'agda .*MetaChecker\.agda' "$awf"; then
    pass "07c-meta-checker-completeness" "MetaChecker.agda imports Echidna.AxiomTrackerCompleteness and $awf checks MetaChecker.agda"
  else
    fail "07c-meta-checker-completeness" "AxiomTrackerCompleteness is not type-checked by the meta-checker job"
  fi
}

# ------------------------------------------- (8) allow-fail expiry, Dec 1st

check_8() {
  # R0 is ruled (owner, 2026-11-05: each unit blocking or deleted), so the
  # slip rule's DEFERRED(ruling:R0) does not apply.
  gate_cmd "08-allow-fail-expiry" "check-allow-fail-expiry.sh as of 2026-12-01" -- \
    scripts/ci/check-allow-fail-expiry.sh --today 2026-12-01
}

# ------------------------------------- (9) fabricated training metrics gone

check_9() {
  local id="09-no-fabricated-metrics" f=models/training_metrics.json
  # The fabricated file (6e13847): MRR = nDCG = 0.85 over 10011 items,
  # timestamp 2026-04-25T15:26:45.716Z, with no run behind it (L-4).
  if [ ! -e "$f" ]; then
    pass "$id" "$f is gone"
  elif jq -e '(.timestamp == "2026-04-25T15:26:45.716Z") or (.MRR == 0.85 and .nDCG == 0.85 and .training_data_size == 10011)' "$f" >/dev/null 2>&1; then
    fail "$id" "$f still holds the fabricated metrics"
  elif ! jq -e . "$f" >/dev/null 2>&1; then
    fail "$id" "$f is not valid JSON"
  else
    pass "$id" "$f no longer holds the fabricated metrics"
  fi
}

# ------------------------------------------------- (10) rulings ledger ADR

RULING_IDS="D-A D-B D-C D-D D-E D-F D-G D-H D-I D-J D-K D-L D-M D-N D2 D3 D5 D6 D7"

check_10() {
  local id="10a-rulings-ledger" adrs adr r block status problems=()
  adrs=$(find docs/decisions -maxdepth 1 -name 'ADR-*-rulings-ledger.adoc' 2>/dev/null | sort)
  if [ -z "$adrs" ]; then
    fail "$id" "no docs/decisions/ADR-*-rulings-ledger.adoc"
  elif [ "$(wc -l <<<"$adrs")" -ne 1 ]; then
    fail "$id" "more than one rulings ledger: $(tr '\n' ' ' <<<"$adrs")"
  else
    adr="$adrs"
    for r in $RULING_IDS; do
      # The section whose heading names the ruling, up to the next heading.
      block=$(awk -v r="$r" '
        function names(s) { return match(s, "(^|[^A-Za-z0-9-])" r "([^A-Za-z0-9]|$)") }
        /^=+[[:space:]]/ { on = names($0); if (on) found = 1 }
        on { print }
        END { exit found ? 0 : 1 }' "$adr") || { problems+=("$r: no section"); continue; }
      status=$(grep -E '^:status:[[:space:]]*' <<<"$block" | tail -1 | sed -E 's/^:status:[[:space:]]*//; s/[[:space:]]+$//')
      case "$status" in
        open) ;;
        ruled) grep -qE 'https://|link:|xref:|<<' <<<"$block" || problems+=("$r: ruled without a link to the owner's record") ;;
        "") problems+=("$r: no :status:") ;;
        *) problems+=("$r: :status: $status") ;;
      esac
    done
    if [ ${#problems[@]} -eq 0 ]; then
      pass "$id" "$adr records all $(wc -w <<<"$RULING_IDS") rulings as open or ruled-with-link"
    else
      fail "$id" "$adr: $(printf '%s; ' "${problems[@]}")"
    fi
  fi

  if [ ! -x scripts/ci/ruling-cited.sh ]; then
    fail "10b-ruling-cited" "scripts/ci/ruling-cited.sh is missing or not executable"; return
  fi
  gate_cmd "10b-ruling-cited" "scripts/ci/ruling-cited.sh" -- scripts/ci/ruling-cited.sh
}

# ------------------------------------- (11, 12) consumer repositories green

# consumer_green <check id> <repo> <name regex> <what>
consumer_green() {
  local id="$1" repo="$2" re="$3" what="$4" branch sha runs hits bad
  if ! have_token; then
    deferred "$id" secret:GITHUB_TOKEN "reading $OWNER/$repo check runs needs a read token"; return
  fi
  if ! branch=$(gh_get "repos/$OWNER/$repo" | jq -er '.default_branch'); then
    fail "$id" "cannot read $OWNER/$repo, and no handover under $(handover_dir "$repo")/"; return
  fi
  if ! sha=$(gh_get "repos/$OWNER/$repo/commits/$branch" | jq -er '.sha') || ! runs=$(check_runs "$OWNER/$repo" "$sha"); then
    fail "$id" "cannot read check runs on $OWNER/$repo $branch"; return
  fi
  hits=$(jq -c --arg re "$re" '[.[] | select(.name | test($re; "i"))]' <<<"$runs")
  if [ "$(jq length <<<"$hits")" -eq 0 ]; then
    fail "$id" "no $what check run matching /$re/ on $OWNER/$repo $branch (${sha:0:9})"; return
  fi
  bad=$(jq -r '[.[] | select(.conclusion != "success") | "\(.name)=\(.conclusion // .status)"] | join(", ")' <<<"$hits")
  if [ -z "$bad" ]; then
    pass "$id" "$OWNER/$repo $branch (${sha:0:9}): $what green ($(jq -r 'map(.name) | join(", ")' <<<"$hits"))"
  else
    fail "$id" "$OWNER/$repo $branch (${sha:0:9}): $bad"
  fi
}

check_11() {
  local repo var re
  for repo in echidnabot proof-burrower panic-attack verisimdb; do
    if has_handover "$repo"; then
      deferred "11-conformance-$repo" "no-push:$repo" "patch and issue text committed under $(handover_dir "$repo")/"
      continue
    fi
    var="W0_CHECK_RE_$(tr 'a-z-' 'A-Z_' <<<"$repo")"
    if [ "$repo" = verisimdb ]; then re="${!var:-verisim-api}"; else re="${!var:-conformance}"; fi
    consumer_green "11-conformance-$repo" "$repo" "$re" "conformance"
  done
}

check_12() {
  if has_handover proof-burrower agda; then
    deferred "12-proof-burrower-agda" "no-push:proof-burrower" "Agda patch and issue text committed under $(handover_dir proof-burrower)/"
    return
  fi
  consumer_green "12-proof-burrower-agda" proof-burrower "${W0_CHECK_RE_PROOF_BURROWER_AGDA:-agda}" "Agda"
}

# --------------------------------------- (13) Lean build recorded in claims

check_13() {
  local id="13-lean-build-recorded" f=docs/proofs/claims.json hit
  if [ ! -f "$f" ]; then
    fail "$id" "$f is missing"; return
  fi
  if ! is_jcs "$f"; then
    fail "$id" "$f is not one JCS value with a final LF"; return
  fi
  hit=$(jq -c '[.. | objects
      | select(([.id, .name, .claim] | map(strings) | join(" ")) | test("lake|lean[^ ]*[ _-]?build"; "i"))
      | select(tojson | contains("4.13.0"))
      | select(([.result, .status, .outcome] | map(strings | ascii_downcase) | any(. == "green" or . == "pass" or . == "passed" or . == "success"))
               or ([.repair_item, .repair, .issue] | map(strings) | any(length > 0)))] | length' "$f")
  if [ "${hit:-0}" -gt 0 ]; then
    pass "$id" "$f records the Lean 4.13.0 lake build as green or with a repair item"
  else
    fail "$id" "$f has no Lean 4.13.0 lake-build entry with a green result or a repair item"
  fi
}

check_1
check_2
check_3
check_4
check_5
check_6
check_7
check_8
check_9
check_10
check_11
check_12
check_13

gate_finish

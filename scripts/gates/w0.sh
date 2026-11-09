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
#   GITHUB_TOKEN          optional read token for the GitHub API. The
#                         repositories read here are public, so without it
#                         the API is read anonymously (60 requests per hour);
#                         a rate-limited or unreadable API is a FAIL.
#   W0_PROBE_PR           number of the no-op probe PR (check 1). Required.
#   W0_REPO               default hyperpolymath/echidna
#   W0_BASE               last main commit before W0 (check 2). Default
#                         6dbfea5 (main before #460, the CI-2 merge).
#   W0_HEAD               ref whose first-parent W0 merges are checked
#                         (check 2). Default HEAD.
#   W0_HOTSPOT_GOLDENS    golden directory for check 5, default
#                         tests/golden/hotspot (see hotspot-goldens.sh).
#   W0_CONSUMER_OWNER     owner of the consumer repositories, default
#                         hyperpolymath.
#   W0_CHECKS             space-separated check numbers to run instead of all
#                         thirteen. A subset run always exits non-zero: it is
#                         a diagnostic, never a gate result.
#   GATE_REPORT           also write the results as JCS JSON Lines (lib.sh).
#
# The effective configuration is printed first, so a result always shows
# what it was computed over.
#
# Check 2 counts a check run as green when its conclusion is success,
# skipped or neutral. The ultraplan says "at success"; every merge on main
# carries schedule-only and matrix jobs that GitHub records as skipped, so a
# literal reading could never pass. The PASS detail counts the skipped and
# neutral runs so the reading stays visible.
#
# Contracts this gate reads from other lanes' artefacts. A lane that chooses
# another shape changes this script in the same PR.
#
#   Consumer conformance jobs (checks 11, 12): a check run on the default
#   branch's head whose name is exactly the job name below, or ends in
#   " / <name>" (a reusable-workflow prefix):
#     echidnabot, proof-burrower, panic-attack   prove-result-conformance
#     verisimdb                                  verisim-api-list
#     proof-burrower (check 12)                  agda-proofs
#   A consumer check counts as DEFERRED(no-push:<repo>) only when the job is
#   not green AND docs/handover/cross-repo/<repo>/ is committed (tracked,
#   no uncommitted changes) with three non-empty files: a patch (*.patch or
#   *.diff; for check 12 its name contains "agda"), the issue text (a file
#   whose name contains "issue"), and PUSH-REFUSED.txt holding the output of
#   the refused push.
#   tests/fixtures/XFAIL.json
#     One JCS value: an array of entries, or an object with "entries". Each
#     entry names its backend in "backend" (or "prover"), matching
#     ^[a-z0-9_]+$.
#   models/training_metrics.json (check 9)
#     Absent, or a JSON object whose "provenance" object carries "commit"
#     (40 lower-case hex digits) and "run_id" (a non-empty string), and which
#     does not repeat the fabricated values.
#   docs/decisions/ADR-*-rulings-ledger.adoc (check 10)
#     One section per ruling (D-A, ..., D-N, D2, D3, D5, D6, D7) whose
#     heading (== or deeper) names exactly one ruling id, with exactly one
#     attribute line `:status: open` or `:status: ruled`, all outside
#     comment and verbatim blocks (////, ----, ...., ++++, ```). A ruled
#     section links the owner's record on https://github.com/hyperpolymath/.
#   scripts/ci/ruling-cited.sh (check 10b)
#     Called as `ruling-cited.sh <W0_BASE> <W0_HEAD>`; exits 0 iff every W0
#     PR in that range cites the rulings it acts on.
#   docs/proofs/claims.json (check 13)
#     One JCS value whose root is an object (a root array FAILs), holding
#     an object whose id, name or claim names the Lean build ("lake build",
#     "lean build", "lean4 build"), which mentions the version 4.13.0 as a
#     whole token, and which carries either a green result
#     (result/status/outcome: green, pass, passed, success) or a "repair"
#     object with a non-empty "id" and "before": "F-3".

# The checks are called through "check_$c", which shellcheck cannot follow.
# shellcheck disable=SC2317
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

# ---------------------------------------------------------------- helpers

# gh_get <api path>: GET from the GitHub REST API, body on stdout. The
# Authorization header is sent only when a token is present. Every request
# is bounded (connect 10 s, transfer 60 s, retries 120 s in all), so a
# stalled API is a FAIL, not a gate that never ends.
gh_get() {
  local auth=()
  [ -n "${GITHUB_TOKEN:-}" ] && auth=(-H "Authorization: Bearer $GITHUB_TOKEN")
  curl -fsS --connect-timeout 10 --max-time 60 --retry 2 --retry-max-time 120 \
    ${auth[@]+"${auth[@]}"} \
    -H "Accept: application/vnd.github+json" \
    -H "X-GitHub-Api-Version: 2022-11-28" \
    "https://api.github.com/$1"
}

# gh_pages <out file> <api path> <jq path to the page's array>: GET every
# page (per_page=100) of a paginated endpoint and write the bodies to the
# file, one per line. Returns non-zero when any page cannot be read, when a
# page's items are not an array, or when there are more pages than it will
# follow: a partial list must never read as a full one. Pages go to a file,
# not through argv, because a commit with many runs produces arrays larger
# than the argument limit.
gh_pages() {
  local out="$1" path="$2" items="$3" page=1 body n
  : > "$out" || return 1
  while :; do
    if ! body=$(gh_get "$path?per_page=100&page=$page") \
       || ! n=$(jq -e "$items | if type == \"array\" then length else error(\"not an array\") end" <<<"$body" 2>/dev/null); then
      return 1
    fi
    printf '%s\n' "$body" >> "$out"
    [ "$n" -lt 100 ] && return 0
    page=$((page + 1))
    [ "$page" -gt 20 ] && return 1
  done
}

# check_runs <repo> <sha>: every check run on the commit, latest per name
# and app, as a JSON array of {name, status, conclusion, app_id}. Returns
# non-zero, with no output, when the runs cannot be read in full.
check_runs() {
  local repo="$1" sha="$2" tmp out
  tmp=$(mktemp) || return 1
  if ! gh_pages "$tmp" "repos/$repo/commits/$sha/check-runs" '.check_runs' \
     || ! out=$(jq -cs 'map(.check_runs) | add // []
                        | map(. + {app_id: (.app.id // null)})
                        | group_by([.name, .app_id])
                        | map(max_by(.id) | {name, status, conclusion, app_id})' "$tmp") \
     || [ -z "$out" ] || ! jq -e 'type == "array"' <<<"$out" >/dev/null 2>&1; then
    rm -f "$tmp"; return 1
  fi
  rm -f "$tmp"
  printf '%s\n' "$out"
}

# commit_statuses <repo> <sha>: the combined legacy commit status with the
# statuses of every page, as {state, total_count, statuses}. Returns
# non-zero, with no output, when any page cannot be read or the pages do not
# add up to total_count.
commit_statuses() {
  local repo="$1" sha="$2" tmp out
  tmp=$(mktemp) || return 1
  if ! gh_pages "$tmp" "repos/$repo/commits/$sha/status" '.statuses' \
     || ! out=$(jq -cs '{state: .[0].state, total_count: .[0].total_count, statuses: (map(.statuses) | add // [])}
                        | if (.state | type) == "string" and (.total_count | type) == "number"
                             and (.statuses | length) == .total_count
                          then . else error("incomplete combined status") end' "$tmp" 2>/dev/null) \
     || [ -z "$out" ]; then
    rm -f "$tmp"; return 1
  fi
  rm -f "$tmp"
  printf '%s\n' "$out"
}

# is_jcs <file>: one JSON value, serialised as JCS, one final LF.
# (jq -cS matches JCS for the strings, integers and plain decimals these
# ledgers hold; it is not a general JCS number serialiser.)
is_jcs() {
  local f="$1"
  [ "$(jq -s 'length' "$f" 2>/dev/null)" = 1 ] || return 1
  cmp -s <(jq -cS . "$f") "$f"
}

# strip_hash_comments <file>: the file without shell/YAML `#` comments,
# whole-line and inline. A `#` starts a comment at the start of a line or
# after whitespace, outside single and double quotes. A quote opens only
# where it does not follow a letter or digit, so the apostrophe in "don't"
# does not hide a comment after it. Quote state does not span lines.
strip_hash_comments() {
  awk '
    { line = $0; out = ""; q = ""; prev = ""
      for (i = 1; i <= length(line); i++) {
        c = substr(line, i, 1)
        if (q == "\"" && c == "\\") { out = out c substr(line, i + 1, 1); prev = substr(line, i + 1, 1); i++; continue }
        if (q != "") { if (c == q) q = ""; out = out c; prev = c; continue }
        if (c == "#" && (prev == "" || prev ~ /[[:space:]]/)) break
        if ((c == "\"" || c == "'\''") && prev !~ /[[:alnum:]]/) q = c
        out = out c; prev = c
      }
      print out }' "$1"
}

# strip_agda_comments <file>: the file without `--` line comments and
# (nested) `{- ... -}` block comments.
strip_agda_comments() {
  awk '
    { line = $0; out = ""; i = 1
      while (i <= length(line)) {
        two = substr(line, i, 2)
        if (depth == 0 && two == "--") break
        if (two == "{-") { depth++; i += 2; continue }
        if (depth > 0 && two == "-}") { depth--; i += 2; continue }
        if (depth == 0) out = out substr(line, i, 1)
        i++
      }
      print out }' "$1"
}

handover_dir() { printf 'docs/handover/cross-repo/%s' "$1"; }

# handover_ok <repo> [patch-name-substring]: the committed handover the
# contract above describes.
handover_ok() {
  local d sub="${2:-}" f base patch="" issue="" refused=""
  d=$(handover_dir "$1")
  [ -d "$d" ] || return 1
  git diff --quiet HEAD -- "$d" 2>/dev/null || return 1
  [ -z "$(git ls-files --others --exclude-standard -- "$d")" ] || return 1
  while IFS= read -r -d '' f; do
    [ -s "$f" ] || continue
    base="${f##*/}"
    case "$base" in
      PUSH-REFUSED.txt) refused=1 ;;
      *.patch|*.diff) [[ ${base,,} == *"${sub,,}"* ]] && patch=1 ;;
    esac
    [[ ${base,,} == *issue* ]] && issue=1
  done < <(git ls-files -z -- "$d")
  [ -n "$patch" ] && [ -n "$issue" ] && [ -n "$refused" ]
}

# --------------------------------------------- (1) probe PR required contexts

check_1() {
  local id="01-probe-pr-required-contexts" tmp rules req sha runs statuses missing r ctx ok
  # Every page of rules: a required_status_checks rule on page 2 still gates.
  tmp=$(mktemp) || { fail "$id" "cannot create a temporary file"; return; }
  if ! gh_pages "$tmp" "repos/$REPO/rules/branches/main" '.' || ! rules=$(jq -cs 'add // []' "$tmp"); then
    rm -f "$tmp"; fail "$id" "cannot read the live ruleset for $REPO main"; return
  fi
  rm -f "$tmp"
  # One {context, integration_id} per line; integration_id is null when the
  # context is not pinned to an app.
  if ! req=$(jq -ec '[.[] | select(.type == "required_status_checks") | .parameters.required_status_checks[]
                      | {context, integration_id: (.integration_id // null)}] | unique | .[]' <<<"$rules"); then
    fail "$id" "the live ruleset requires no status context; nothing would gate a merge"; return
  fi
  if ! [[ ${W0_PROBE_PR:-} =~ ^[0-9]+$ ]]; then
    fail "$id" "W0_PROBE_PR is not set to the no-op probe PR number ($(wc -l <<<"$req") required contexts to check)"; return
  fi
  if ! sha=$(gh_get "repos/$REPO/pulls/$W0_PROBE_PR" | jq -er '.head.sha'); then
    fail "$id" "cannot read probe PR #$W0_PROBE_PR"; return
  fi
  if ! runs=$(check_runs "$REPO" "$sha") || ! statuses=$(commit_statuses "$REPO" "$sha"); then
    fail "$id" "cannot read check runs for probe PR #$W0_PROBE_PR ($sha)"; return
  fi
  missing=()
  while IFS= read -r r; do
    # A context pinned to an app (integration_id) is satisfied only by a
    # check run from that app; a legacy status cannot satisfy it. Not jq -e:
    # a context that is not green evaluates to false, which is an answer,
    # not an error.
    ok=$(jq -r --argjson r "$r" --slurpfile s <(printf '%s\n' "$statuses") '
        ([.[] | select(.name == $r.context and .conclusion == "success"
                       and ($r.integration_id == null or .app_id == $r.integration_id))] | length > 0)
        or ($r.integration_id == null
            and ([$s[0].statuses[] | select(.context == $r.context and .state == "success")] | length > 0))' <<<"$runs")
    ctx=$(jq -r '.context + (if .integration_id == null then "" else " (app \(.integration_id))" end)' <<<"$r")
    case "$ok" in
      true|false) ;;
      *) fail "$id" "cannot evaluate required context '$ctx'"; return ;;
    esac
    [ "$ok" = true ] || missing+=("$ctx")
  done <<<"$req"
  if [ ${#missing[@]} -eq 0 ]; then
    pass "$id" "probe PR #$W0_PROBE_PR (${sha:0:9}): all $(wc -l <<<"$req") required contexts are success"
  else
    fail "$id" "probe PR #$W0_PROBE_PR: not success: $(printf '%s; ' "${missing[@]}")"
  fi
}

# --------------------------------------- (2) every W0 merge commit is green

check_2() {
  local id="02-w0-merges-green" commits c runs bad statuses st nr ns soft=0 n=0 problems=()
  if ! commits=$(git rev-list --first-parent "$W0_BASE..$W0_HEAD" 2>/dev/null); then
    fail "$id" "cannot list commits $W0_BASE..$W0_HEAD (fetch history?)"; return
  fi
  if [ -z "$commits" ]; then
    fail "$id" "no W0 merge commits in $W0_BASE..$W0_HEAD"; return
  fi
  for c in $commits; do
    n=$((n + 1))
    # Legacy statuses: every page is read, and GitHub's combined state must
    # also be success whenever any status exists. The combined state is
    # computed over every context, so even a page this script failed to
    # read cannot hide a red status; the pages only name which one.
    if ! runs=$(check_runs "$REPO" "$c") || ! statuses=$(commit_statuses "$REPO" "$c") \
       || ! nr=$(jq -e 'length' <<<"$runs") || ! ns=$(jq -e '.total_count' <<<"$statuses"); then
      problems+=("${c:0:9} unreadable"); continue
    fi
    if [ "$nr" -eq 0 ] && [ "$ns" -eq 0 ]; then
      problems+=("${c:0:9} has no check runs"); continue
    fi
    if ! bad=$(jq -er '[.[] | select((.conclusion // "pending") as $k | ["success","skipped","neutral"] | index($k) | not) | "\(.name)=\(.conclusion // .status)"] | join(", ")' <<<"$runs") \
       || ! st=$(jq -er '[.statuses[] | select(.state != "success") | "\(.context)=\(.state)"]
                         + (if .total_count > 0 and .state != "success" then ["combined status=\(.state)"] else [] end)
                         | join(", ")' <<<"$statuses"); then
      problems+=("${c:0:9} unparseable"); continue
    fi
    soft=$((soft + $(jq '[.[] | select(.conclusion == "skipped" or .conclusion == "neutral")] | length' <<<"$runs")))
    [ -n "$bad$st" ] && problems+=("${c:0:9}: ${bad}${bad:+${st:+, }}${st}")
  done
  if [ ${#problems[@]} -eq 0 ]; then
    pass "$id" "$n first-parent commits in ${W0_BASE:0:9}..$W0_HEAD, every check run success ($soft skipped or neutral; the bypass log stays an owner checkpoint)"
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
  local idx="06a-xfail-ledger" idl="06b-live-fixtures" f="tests/fixtures/XFAIL.json" backends b n=0 bad=()
  if [ ! -f "$f" ]; then
    fail "$idx" "$f is missing"
  elif ! is_jcs "$f"; then
    fail "$idx" "$f is not one JCS value with a final LF"
  elif ! backends=$(jq -r 'if type == "array" then . elif type == "object" and (.entries | type) == "array" then .entries else error("neither an array nor an object with an entries array") end
        | map(if type == "object" and ((.backend // .prover) | type) == "string" and ((.backend // .prover) | test("^[a-z0-9_]+$"))
              then (.backend // .prover)
              else error("an entry does not name its backend as ^[a-z0-9_]+$: \(tojson)") end)
        | .[]' "$f" 2>&1); then
    fail "$idx" "$f has an unrecognised shape: $backends"
  else
    while IFS= read -r b; do
      [ -n "$b" ] || continue
      n=$((n + 1))
      [[ " $XFAIL_ALLOWED " == *" $b "* ]] || bad+=("$b")
    done <<<"$backends"
    if [ ${#bad[@]} -gt 0 ]; then
      fail "$idx" "$f lists backends outside V-3 scope: ${bad[*]}"
    elif [ "$n" -eq 0 ]; then
      pass "$idx" "$f is JCS and empty"
    else
      pass "$idx" "$f is JCS and lists only V-3 backends/IR fallbacks ($n entries)"
    fi
  fi

  if [ ! -x scripts/ci/live-fixtures.sh ]; then
    fail "$idl" "scripts/ci/live-fixtures.sh is missing or not executable"; return
  fi
  gate_cmd "$idl" "ECHIDNA_FAIL_ON_SKIP=1 scripts/ci/live-fixtures.sh" -- \
    env ECHIDNA_FAIL_ON_SKIP=1 scripts/ci/live-fixtures.sh
}

# ------------------------------------------------ (7) Idris / Agda hygiene

# ipkg_modules <ipkg>: the module names listed under `modules`, one per line,
# for both the one-line and the leading-comma layouts.
ipkg_modules() {
  sed -E 's/--.*$//' "$1" | awk '
    /^[[:space:]]*[a-z][a-z0-9_]*[[:space:]]*=/ { on = ($1 == "modules" || $0 ~ /^[[:space:]]*modules[[:space:]]*=/); sub(/^[^=]*=/, "") }
    on { gsub(/,/, " "); for (i = 1; i <= NF; i++) print $i }'
}

check_7() {
  local wf=.github/workflows/idris2-abi-ci.yml ipkg=src/abi/echidnaabi.ipkg rel mod mods missing=()
  if [ -f "$wf" ] && strip_hash_comments "$wf" | grep -E '\bpostulate\b' | grep -qE 'grep|rg |for pattern in'; then
    pass "07a-idris-postulate-grep" "$wf greps src/abi for postulate"
  else
    fail "07a-idris-postulate-grep" "$wf does not grep for postulate outside comments"
  fi

  if [ ! -f "$ipkg" ]; then
    fail "07b-ipkg-coverage" "$ipkg is missing"
  else
    mods=$(ipkg_modules "$ipkg")
    for rel in EchidnaABI/CapnSchemas.idr CoprocessorForeign.idr; do
      [ -f "src/abi/$rel" ] || continue
      mod=$(sed 's/\.idr$//; s#/#.#g' <<<"$rel")
      grep -qxF "$mod" <<<"$mods" || missing+=("$mod")
    done
    if [ ${#missing[@]} -eq 0 ]; then
      pass "07b-ipkg-coverage" "CapnSchemas and CoprocessorForeign are in $ipkg or deleted"
    else
      fail "07b-ipkg-coverage" "present but not in $ipkg: ${missing[*]}"
    fi
  fi

  local mc=meta-checker/src/Echidna/MetaChecker.agda awf=.github/workflows/agda-meta-checker.yml
  if [ -f "$awf" ] && strip_hash_comments "$awf" | grep -qE 'agda .*AxiomTrackerCompleteness\.agda'; then
    pass "07c-meta-checker-completeness" "$awf type-checks AxiomTrackerCompleteness.agda directly"
  elif [ -f "$mc" ] && strip_agda_comments "$mc" | grep -qE '^[[:space:]]*(open[[:space:]]+)?import[[:space:]]+Echidna\.AxiomTrackerCompleteness([[:space:]]|$)' \
       && [ -f "$awf" ] && { strip_hash_comments "$awf" | grep -qE 'agda .*MetaChecker\.agda' \
            || { strip_hash_comments "$awf" | grep -qE 'scripts/ci/check-agda\.sh' \
                 && [ -f scripts/ci/check-agda.sh ] && strip_hash_comments scripts/ci/check-agda.sh | grep -qE 'MetaChecker\.agda'; }; }; then
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
  elif ! jq -e 'type == "object"' "$f" >/dev/null 2>&1; then
    fail "$id" "$f is not a JSON object"
  elif jq -e '(.MRR == 0.85 and .nDCG == 0.85) or ((.timestamp // "") | startswith("2026-04-25T15:26"))' "$f" >/dev/null 2>&1; then
    fail "$id" "$f still holds the fabricated metrics"
  elif jq -e '(.provenance | type) == "object"
        and ((.provenance.commit // "") | test("^[0-9a-f]{40}$"))
        and ((.provenance.run_id // "") | type == "string" and length > 0)' "$f" >/dev/null 2>&1; then
    pass "$id" "$f carries run provenance ($(jq -r '.provenance.run_id + " at " + .provenance.commit[0:9]' "$f"))"
  else
    fail "$id" "$f has no run provenance (provenance.commit and provenance.run_id)"
  fi
}

# ------------------------------------------------- (10) rulings ledger ADR

RULING_IDS="D-A D-B D-C D-D D-E D-F D-G D-H D-I D-J D-K D-L D-M D-N D2 D3 D5 D6 D7"

# adoc_strip_blocks <adoc>: the file with every line of a comment (////),
# listing (----), literal (....), passthrough (++++) or fenced (```) block,
# delimiters included, blanked. Line numbers are kept. A block closes only
# on a line equal to its opening delimiter; an unclosed block runs to the
# end of the file, so nothing after a stray delimiter can count.
adoc_strip_blocks() {
  awk '
    delim != "" { if ($0 == delim) delim = ""; print ""; next }
    /^(\/\/\/\/+|----+|\.\.\.\.+|\+\+\+\++)$/ || /^```/ { delim = ($0 ~ /^```/) ? "```" : $0; print ""; next }
    { print }' "$1"
}

# ruling_sections <adr>: for every section heading (== or deeper), the line
# "<heading line number> <ruling ids named in it>".
ruling_sections() {
  awk -v ids="$RULING_IDS" '
    BEGIN { n = split(ids, id, " ") }
    /^==+[[:space:]]/ {
      named = ""
      for (k = 1; k <= n; k++)
        if (match($0, "(^|[^A-Za-z0-9-])" id[k] "([^A-Za-z0-9]|$)")) named = named " " id[k]
      print NR named
    }' "$1"
}

check_10() {
  local id="10a-rulings-ledger" adrs adr r sections line from to block statuses status text problems=()
  adrs=$(find docs/decisions -maxdepth 1 -name 'ADR-*-rulings-ledger.adoc' 2>/dev/null | sort)
  if [ -z "$adrs" ]; then
    fail "$id" "no docs/decisions/ADR-*-rulings-ledger.adoc"
  elif [ "$(wc -l <<<"$adrs")" -ne 1 ]; then
    fail "$id" "more than one rulings ledger: $(tr '\n' ' ' <<<"$adrs")"
  else
    adr="$adrs"
    # Headings, :status: lines and links inside comment or verbatim blocks
    # are not ledger content.
    text=$(adoc_strip_blocks "$adr")
    sections=$(ruling_sections <(printf '%s\n' "$text"))
    while read -r line r rest; do
      [ -n "${rest:-}" ] && problems+=("heading at line $line names more than one ruling ($r $rest)")
    done <<<"$sections"
    for r in $RULING_IDS; do
      line=$(awk -v r="$r" 'NF == 2 && $2 == r { print $1 }' <<<"$sections")
      if [ -z "$line" ]; then problems+=("$r: no section of its own"); continue; fi
      if [ "$(wc -l <<<"$line")" -ne 1 ]; then problems+=("$r: more than one section"); continue; fi
      from="$line"
      to=$(awk -v f="$from" '$1 > f { print $1 - 1; exit }' <<<"$sections")
      block=$(sed -n "${from},${to:-\$}p" <<<"$text")
      statuses=$(grep -cE '^:status:' <<<"$block")
      status=$(grep -E '^:status:' <<<"$block" | sed -E 's/^:status:[[:space:]]*//; s/[[:space:]]+$//')
      if [ "$statuses" -ne 1 ]; then problems+=("$r: $statuses :status: lines"); continue; fi
      case "$status" in
        open) ;;
        ruled) grep -qE 'https://github\.com/hyperpolymath/[^[:space:]]+' <<<"$block" \
                 || problems+=("$r: ruled without a link to the owner's record on github.com/hyperpolymath") ;;
        *) problems+=("$r: :status: $status") ;;
      esac
    done
    if [ ${#problems[@]} -eq 0 ]; then
      pass "$id" "$adr records all $(wc -w <<<"$RULING_IDS") rulings, one section each, as open or ruled-with-record"
    else
      fail "$id" "$adr: $(printf '%s; ' "${problems[@]}")"
    fi
  fi

  if [ ! -x scripts/ci/ruling-cited.sh ]; then
    fail "10b-ruling-cited" "scripts/ci/ruling-cited.sh is missing or not executable"; return
  fi
  gate_cmd "10b-ruling-cited" "scripts/ci/ruling-cited.sh ${W0_BASE:0:9} $W0_HEAD" -- \
    scripts/ci/ruling-cited.sh "$W0_BASE" "$W0_HEAD"
}

# ------------------------------------- (11, 12) consumer repositories green

# consumer_eval <repo> <job name>: sets C_GREEN (1 or empty) and C_DETAIL.
consumer_eval() {
  local repo="$1" job="$2" branch sha runs hits n bad
  C_GREEN=""
  if ! branch=$(gh_get "repos/$OWNER/$repo" | jq -er '.default_branch'); then
    C_DETAIL="cannot read $OWNER/$repo"; return
  fi
  if ! sha=$(gh_get "repos/$OWNER/$repo/commits/$branch" | jq -er '.sha') || ! runs=$(check_runs "$OWNER/$repo" "$sha"); then
    C_DETAIL="cannot read check runs on $OWNER/$repo $branch"; return
  fi
  if ! hits=$(jq -ec --arg j "$job" '[.[] | select(.name == $j or (.name | endswith(" / " + $j)))]' <<<"$runs") \
     || ! n=$(jq -e 'length' <<<"$hits"); then
    C_DETAIL="cannot parse check runs on $OWNER/$repo $branch"; return
  fi
  if [ "$n" -eq 0 ]; then
    C_DETAIL="no check run named '$job' on $OWNER/$repo $branch (${sha:0:9})"; return
  fi
  bad=$(jq -r '[.[] | select(.conclusion != "success") | "\(.name)=\(.conclusion // .status)"] | join(", ")' <<<"$hits")
  if [ -z "$bad" ]; then
    C_GREEN=1
    C_DETAIL="$OWNER/$repo $branch (${sha:0:9}): '$job' green ($(jq -r 'map(.name) | join(", ")' <<<"$hits"))"
  else
    C_DETAIL="$OWNER/$repo $branch (${sha:0:9}): $bad"
  fi
}

# consumer_check <check id> <repo> <job name> [patch-name-substring]
consumer_check() {
  local id="$1" repo="$2" job="$3" sub="${4:-}"
  consumer_eval "$repo" "$job"
  if [ -n "$C_GREEN" ]; then
    pass "$id" "$C_DETAIL"
  elif handover_ok "$repo" "$sub"; then
    deferred "$id" "no-push:$repo" "$C_DETAIL; handover committed under $(handover_dir "$repo")/"
  else
    fail "$id" "$C_DETAIL; no committed handover under $(handover_dir "$repo")/"
  fi
}

check_11() {
  local repo
  for repo in echidnabot proof-burrower panic-attack; do
    consumer_check "11-conformance-$repo" "$repo" prove-result-conformance
  done
  consumer_check "11-conformance-verisimdb" verisimdb verisim-api-list
}

check_12() {
  consumer_check "12-proof-burrower-agda" proof-burrower agda-proofs agda
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
  if ! jq -e 'type == "object"' "$f" >/dev/null 2>&1; then
    fail "$id" "$f is not a JSON object at its root"; return
  fi
  if ! hit=$(jq -e '[.. | objects
      | select(([.id, .name, .claim] | map(strings) | join(" ")) | test("\\blake[ _-]build\\b|\\blean4?[ _-]build\\b"; "i"))
      | select(tojson | test("(^|[^0-9.])4\\.13\\.0([^0-9.]|$)"))
      | select(([.result, .status, .outcome] | map(strings | ascii_downcase) | any(. == "green" or . == "pass" or . == "passed" or . == "success"))
               or ((.repair | type) == "object" and ((.repair.id // "") | type == "string" and length > 0) and .repair.before == "F-3"))]
      | length' "$f"); then
    fail "$id" "$f cannot be evaluated"; return
  fi
  if [ "$hit" -gt 0 ]; then
    pass "$id" "$f records the Lean 4.13.0 lake build as green or with a repair item before F-3"
  else
    fail "$id" "$f has no Lean 4.13.0 lake-build entry with a green result or a repair item before F-3"
  fi
}

# ------------------------------------------------------------------- run

printf 'W0 config: repo=%s base=%s head=%s goldens=%s consumers=%s api=%s probe_pr=%s\n' \
  "$REPO" "$W0_BASE" "$W0_HEAD" "$GOLDENS" "$OWNER" \
  "$([ -n "${GITHUB_TOKEN:-}" ] && echo token || echo anonymous)" "${W0_PROBE_PR:-unset}"

gate_init W0
if [ -n "${W0_CHECKS:-}" ]; then
  for c in $W0_CHECKS; do
    if declare -F "check_$c" >/dev/null; then "check_$c"; else fail "w0-checks" "no check $c"; fi
  done
  fail "w0-subset" "only checks $W0_CHECKS ran (W0_CHECKS); a subset run is not a gate result"
else
  for c in 1 2 3 4 5 6 7 8 9 10 11 12 13; do "check_$c"; done
fi
gate_finish

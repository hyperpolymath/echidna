#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
#
# Fixture tests for scripts/gates/w0.sh. Each case builds a scratch git
# repository holding the gate scripts and one planted artefact, serves the
# GitHub API from files through a stub curl, runs the gate with W0_CHECKS
# set to the check under test, and asserts the result line for that check.
# No network, cargo or GitHub token is used.
#
# The planted artefacts include each false green found in review: a commit
# with more than 100 check runs, governance jobs named "... conformance",
# empty untracked handover files, blank and glob backend names, nudged
# fabricated metrics, a one-heading rulings ledger, a "nix flake" claim,
# legacy statuses and rules past page one, a pinned context met by the
# wrong app, inline `#` comments, ledger sections inside comment blocks and
# a claims.json whose root is an array.
#
# Usage: scripts/gates/w0.selftest.sh     Exit 0 iff every case behaves.

# SC2001: sed prefixes multi-line output, which ${var//} cannot do per line.
# SC2016: fixture text holds a literal $pattern on purpose.
# shellcheck disable=SC2001,SC2016
set -uo pipefail
export LC_ALL=C

here=$(cd "$(dirname "$0")" && pwd)
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
failures=0
cases=0

# ------------------------------------------------------------- scaffolding

mkdir -p "$tmp/bin"
cat > "$tmp/bin/curl" <<'EOF'
#!/usr/bin/env bash
# Serves https://api.github.com/<path> from $STUB_API/<path with /?&= as _>
# and logs its arguments, one call per line, to $STUB_API.calls.
url="${*: -1}"
printf '%s\n' "$*" >> "$STUB_API.calls"
key=$(printf '%s' "${url#https://api.github.com/}" | tr '/?&=' '____')
[ -f "$STUB_API/$key" ] || { echo "curl stub: no fixture for $url" >&2; exit 22; }
cat "$STUB_API/$key"
EOF
chmod +x "$tmp/bin/curl"

# new_repo: a fresh scratch repository with the gate scripts committed;
# sets R (its path) and STUB_API (its API fixture directory).
new_repo() {
  R=$(mktemp -d "$tmp/repo.XXXXXX")
  STUB_API="$R.api"
  mkdir -p "$R/scripts/gates" "$STUB_API"
  cp "$here/lib.sh" "$here/w0.sh" "$here/hotspot-goldens.sh" "$R/scripts/gates/"
  git -C "$R" init -q -b main
  git -C "$R" -c user.email=t@t -c user.name=t add -A
  git -C "$R" -c user.email=t@t -c user.name=t commit -qm base
}

commit_all() {
  git -C "$R" -c user.email=t@t -c user.name=t add -A
  git -C "$R" -c user.email=t@t -c user.name=t commit -qm "${1:-fixture}"
}

# serve <api path> <body>: the stub curl answers <api path> with <body>.
serve() {
  printf '%s\n' "$2" > "$STUB_API/$(printf '%s' "$1" | tr '/?&=' '____')"
}

# serve_status <repo> <sha> <body>: page 1 of the combined commit status.
# The unpaged path is served the same body, so the cases also run against
# the gate before it paginated (to show they fail there).
serve_status() {
  serve "repos/$1/commits/$2/status?per_page=100&page=1" "$3"
  serve "repos/$1/commits/$2/status" "$3"
}

# serve_rules <body>: page 1 of the echidna main rules (and the unpaged path).
serve_rules() {
  serve "repos/hyperpolymath/echidna/rules/branches/main?per_page=100&page=1" "$1"
  serve "repos/hyperpolymath/echidna/rules/branches/main" "$1"
}

# runs_json <count> <failing name or ""> <name padding>: a check-runs page.
runs_json() {
  jq -cn --argjson n "$1" --arg bad "$2" --arg pad "$3" --argjson off "${4:-0}" '
    {total_count: $n, check_runs: [range($n) as $i
      | {id: ($i + $off + 1), name: ("job-\($i + $off)-" + $pad), status: "completed",
         conclusion: (if ("job-\($i + $off)-" + $pad) == $bad then "failure" else "success" end)}]}'
}

# gate <checks> [VAR=value ...]: run w0.sh in $R; output in $OUT.
gate() {
  local checks="$1"
  shift
  OUT=$(cd "$R" && env PATH="$tmp/bin:$PATH" STUB_API="$STUB_API" GITHUB_TOKEN= \
    W0_CHECKS="$checks" "$@" bash scripts/gates/w0.sh 2>&1)
  RC=$?
}

# expect <case name> <PASS|FAIL|DEFERRED> <check id> [extra grep pattern]
expect() {
  local name="$1" want="$2" id="$3" pattern="${4:-}" ok=1
  cases=$((cases + 1))
  grep -qE "^$want +$id( |:)" <<<"$OUT" || ok=0
  if [ -n "$pattern" ] && ! grep -qE -- "$pattern" <<<"$OUT"; then ok=0; fi
  # A subset run must never exit 0.
  [ "$RC" -ne 0 ] || ok=0
  if [ "$ok" -eq 1 ]; then
    echo "ok   $name"
  else
    failures=$((failures + 1))
    echo "FAIL $name: wanted $want $id${pattern:+ and /$pattern/}, exit non-zero; got exit $RC"
    sed 's/^/     | /' <<<"$OUT"
  fi
}

# --------------------------------------------- check 2: >100 check runs

new_repo
base=$(git -C "$R" rev-parse HEAD)
echo x > "$R/f"; commit_all merge
head=$(git -C "$R" rev-parse HEAD)
pad=$(printf 'p%.0s' $(seq 1 1500))
serve "repos/hyperpolymath/echidna/commits/$head/check-runs?per_page=100&page=1" "$(runs_json 100 "" "$pad")"
serve "repos/hyperpolymath/echidna/commits/$head/check-runs?per_page=100&page=2" "$(runs_json 50 "job-140-$pad" "$pad" 100)"
serve_status hyperpolymath/echidna "$head" '{"state":"pending","total_count":0,"statuses":[]}'
gate 2 W0_BASE="$base" W0_HEAD="$head"
expect "check 2 sees a failure on page 2 of 150 large runs" FAIL 02-w0-merges-green "job-140-p+=failure"

serve "repos/hyperpolymath/echidna/commits/$head/check-runs?per_page=100&page=2" "$(runs_json 50 "" "$pad" 100)"
gate 2 W0_BASE="$base" W0_HEAD="$head"
expect "check 2 passes when all 150 runs succeed" PASS 02-w0-merges-green

serve "repos/hyperpolymath/echidna/commits/$head/check-runs?per_page=100&page=2" 'not json'
gate 2 W0_BASE="$base" W0_HEAD="$head"
expect "check 2 fails closed on an unparseable page" FAIL 02-w0-merges-green "unreadable"

rm -f "$STUB_API"/*page_2
gate 2 W0_BASE="$base" W0_HEAD="$head"
expect "check 2 fails closed on an unreadable page" FAIL 02-w0-merges-green "unreadable"

# ------------------------------- check 2: legacy statuses beyond page one

# statuses_json <count> <state of the last one> <combined state> <total> [offset]
statuses_json() {
  jq -cn --argjson n "$1" --arg last "$2" --arg st "$3" --argjson t "$4" --argjson off "${5:-0}" '
    {state: $st, total_count: $t, statuses: [range($n) as $i
      | {context: "legacy-\($i + $off)", state: (if $i == $n - 1 then $last else "success" end)}]}'
}
new_repo
base=$(git -C "$R" rev-parse HEAD)
echo x > "$R/f"; commit_all merge
head=$(git -C "$R" rev-parse HEAD)
serve "repos/hyperpolymath/echidna/commits/$head/check-runs?per_page=100&page=1" "$(runs_json 1 "" x)"
serve_status hyperpolymath/echidna "$head" "$(statuses_json 100 success failure 101)"
serve "repos/hyperpolymath/echidna/commits/$head/status?per_page=100&page=2" "$(statuses_json 1 failure failure 101 100)"
gate 2 W0_BASE="$base" W0_HEAD="$head"
expect "check 2 reads a red legacy status on page 2 of the statuses" FAIL 02-w0-merges-green "legacy-100=failure"

rm -f "$STUB_API"/*status_per_page_100_page_2
gate 2 W0_BASE="$base" W0_HEAD="$head"
expect "check 2 fails closed when a statuses page is missing" FAIL 02-w0-merges-green "unreadable"

serve_status hyperpolymath/echidna "$head" "$(statuses_json 2 success failure 2)"
gate 2 W0_BASE="$base" W0_HEAD="$head"
expect "check 2 requires the combined legacy state to be success" FAIL 02-w0-merges-green "combined status=failure"

serve_status hyperpolymath/echidna "$head" "$(statuses_json 100 success success 101)"
serve "repos/hyperpolymath/echidna/commits/$head/status?per_page=100&page=2" "$(statuses_json 1 success success 101 100)"
gate 2 W0_BASE="$base" W0_HEAD="$head"
expect "check 2 passes 101 green legacy statuses over two pages" PASS 02-w0-merges-green

# ----------------------------------------- check 1: probe PR required contexts

new_repo
psha=0123456789abcdef0123456789abcdef0123abcd
serve_rules '[{"type":"required_status_checks","parameters":{"required_status_checks":[{"context":"rust-ci / Cargo test"},{"context":"gitleaks"}]}}]'
serve "repos/hyperpolymath/echidna/pulls/7" "{\"head\":{\"sha\":\"$psha\"}}"
serve_status hyperpolymath/echidna "$psha" '{"state":"success","total_count":1,"statuses":[{"context":"gitleaks","state":"success"}]}'
serve "repos/hyperpolymath/echidna/commits/$psha/check-runs?per_page=100&page=1" '{"check_runs":[{"id":1,"name":"rust-ci / Cargo test","status":"completed","conclusion":"failure"}]}'
gate 1 W0_PROBE_PR=7
expect "a red required context fails check 1 by name" FAIL 01-probe-pr-required-contexts "not success: rust-ci / Cargo test;"
serve "repos/hyperpolymath/echidna/commits/$psha/check-runs?per_page=100&page=1" '{"check_runs":[{"id":1,"name":"rust-ci / Cargo test","status":"completed","conclusion":"success"}]}'
gate 1 W0_PROBE_PR=7
expect "every required context green passes check 1" PASS 01-probe-pr-required-contexts "all 2 required contexts"
gate 1
expect "check 1 needs W0_PROBE_PR" FAIL 01-probe-pr-required-contexts "W0_PROBE_PR is not set"
serve_rules '[]'
gate 1 W0_PROBE_PR=7
expect "a ruleset with no required context fails check 1" FAIL 01-probe-pr-required-contexts "requires no status context"

# Pinned contexts: integration_id names the app whose check run counts.
pinned='[{"type":"required_status_checks","parameters":{"required_status_checks":[{"context":"rust-ci / Cargo test","integration_id":15368},{"context":"gitleaks"}]}}]'
serve_rules "$pinned"
serve "repos/hyperpolymath/echidna/commits/$psha/check-runs?per_page=100&page=1" '{"check_runs":[{"id":1,"name":"rust-ci / Cargo test","status":"completed","conclusion":"success","app":{"id":999}}]}'
gate 1 W0_PROBE_PR=7
expect "a run from another app does not satisfy a pinned context" FAIL 01-probe-pr-required-contexts "not success: rust-ci / Cargo test \(app 15368\);"
serve "repos/hyperpolymath/echidna/commits/$psha/check-runs?per_page=100&page=1" '{"check_runs":[]}'
serve_status hyperpolymath/echidna "$psha" '{"state":"success","total_count":2,"statuses":[{"context":"gitleaks","state":"success"},{"context":"rust-ci / Cargo test","state":"success"}]}'
gate 1 W0_PROBE_PR=7
expect "a legacy status does not satisfy a pinned context" FAIL 01-probe-pr-required-contexts "rust-ci / Cargo test \(app 15368\)"
serve "repos/hyperpolymath/echidna/commits/$psha/check-runs?per_page=100&page=1" '{"check_runs":[{"id":1,"name":"rust-ci / Cargo test","status":"completed","conclusion":"success","app":{"id":999}},{"id":2,"name":"rust-ci / Cargo test","status":"completed","conclusion":"success","app":{"id":15368}}]}'
gate 1 W0_PROBE_PR=7
expect "a green run from the pinned app passes check 1" PASS 01-probe-pr-required-contexts "all 2 required contexts"

# Rules on page 2: page 1 is full (100 rules), the red context is on page 2.
serve_status hyperpolymath/echidna "$psha" '{"state":"success","total_count":1,"statuses":[{"context":"gitleaks","state":"success"}]}'
serve_rules "$(jq -cn '[range(99) | {type: "deletion"}] + [{type: "required_status_checks", parameters: {required_status_checks: [{context: "gitleaks"}]}}]')"
serve "repos/hyperpolymath/echidna/rules/branches/main?per_page=100&page=2" '[{"type":"required_status_checks","parameters":{"required_status_checks":[{"context":"rust-ci / Cargo test"}]}}]'
serve "repos/hyperpolymath/echidna/commits/$psha/check-runs?per_page=100&page=1" '{"check_runs":[{"id":1,"name":"rust-ci / Cargo test","status":"completed","conclusion":"failure"}]}'
gate 1 W0_PROBE_PR=7
expect "a required context in rules page 2 still gates check 1" FAIL 01-probe-pr-required-contexts "not success: rust-ci / Cargo test;"
rm -f "$STUB_API"/*main_per_page_100_page_2
gate 1 W0_PROBE_PR=7
expect "check 1 fails closed when a rules page is missing" FAIL 01-probe-pr-required-contexts "cannot read the live ruleset"

# Every GitHub API request is bounded in time.
cases=$((cases + 1))
if [ -s "$STUB_API.calls" ] \
   && ! grep -vE -- '--connect-timeout [0-9]+ ' "$STUB_API.calls" | grep -q . \
   && ! grep -vE -- '--max-time [0-9]+ ' "$STUB_API.calls" | grep -q . \
   && ! grep -vE -- '--retry-max-time [0-9]+ ' "$STUB_API.calls" | grep -q .; then
  echo "ok   every GitHub API request sets connect, total and retry time limits"
else
  failures=$((failures + 1)); echo "FAIL every GitHub API request sets connect, total and retry time limits"
  sed 's/^/     | /' "$STUB_API.calls" | head -n 3
fi

# ------------------------------------------- checks 11/12: consumer repos

# consumer <repo> <runs json>: serve the repo, its head and its runs.
consumer() {
  serve "repos/hyperpolymath/$1" '{"default_branch":"main"}'
  serve "repos/hyperpolymath/$1/commits/main" '{"sha":"0123456789abcdef0123456789abcdef01234567"}'
  serve "repos/hyperpolymath/$1/commits/0123456789abcdef0123456789abcdef01234567/check-runs?per_page=100&page=1" "$2"
}
gov='{"check_runs":[{"id":1,"name":"governance / UUID v7 conformance","status":"completed","conclusion":"success"},{"id":2,"name":"KYAML conformance","status":"completed","conclusion":"success"}]}'
good='{"check_runs":[{"id":3,"name":"ci / prove-result-conformance","status":"completed","conclusion":"success"},{"id":4,"name":"verisim-api-list","status":"completed","conclusion":"success"}]}'

new_repo
for r in echidnabot proof-burrower panic-attack verisimdb; do consumer "$r" "$gov"; done
gate 11
expect "governance '... conformance' jobs do not satisfy check 11" FAIL 11-conformance-panic-attack "no check run named 'prove-result-conformance'"

for r in echidnabot proof-burrower panic-attack verisimdb; do consumer "$r" "$good"; done
gate 11
expect "the named conformance job passes check 11" PASS 11-conformance-panic-attack
expect "the verisim-api-list job passes check 11" PASS 11-conformance-verisimdb

for r in echidnabot proof-burrower panic-attack verisimdb; do consumer "$r" "$gov"; done
mkdir -p "$R/docs/handover/cross-repo/panic-attack"
: > "$R/docs/handover/cross-repo/panic-attack/x.patch"
: > "$R/docs/handover/cross-repo/panic-attack/issue.md"
: > "$R/docs/handover/cross-repo/panic-attack/PUSH-REFUSED.txt"
gate 11
expect "empty untracked handover files do not defer" FAIL 11-conformance-panic-attack "no committed handover"

for f in x.patch issue.md PUSH-REFUSED.txt; do echo content > "$R/docs/handover/cross-repo/panic-attack/$f"; done
gate 11
expect "non-empty but uncommitted handover does not defer" FAIL 11-conformance-panic-attack "no committed handover"

rm "$R/docs/handover/cross-repo/panic-attack/PUSH-REFUSED.txt"; commit_all handover
gate 11
expect "a handover without PUSH-REFUSED.txt does not defer" FAIL 11-conformance-panic-attack

echo "remote: Permission denied" > "$R/docs/handover/cross-repo/panic-attack/PUSH-REFUSED.txt"; commit_all refused
gate 11
expect "a committed handover with the refusal defers" DEFERRED 11-conformance-panic-attack "no-push:panic-attack"

echo edited >> "$R/docs/handover/cross-repo/panic-attack/issue.md"
gate 11
expect "a handover with uncommitted edits does not defer" FAIL 11-conformance-panic-attack "no committed handover"
git -C "$R" checkout -q -- docs/handover

: > "$R/docs/handover/cross-repo/panic-attack/PUSH-REFUSED.txt"; commit_all empty-refusal
gate 11
expect "a committed but empty PUSH-REFUSED.txt does not defer" FAIL 11-conformance-panic-attack "no committed handover"
echo "remote: Permission denied" > "$R/docs/handover/cross-repo/panic-attack/PUSH-REFUSED.txt"; commit_all refused-again

consumer panic-attack "$good"
gate 11
expect "a green job passes even when a handover exists" PASS 11-conformance-panic-attack

consumer proof-burrower "$gov"
mkdir -p "$R/docs/handover/cross-repo/proof-burrower"
for f in fix.patch issue.md PUSH-REFUSED.txt; do echo c > "$R/docs/handover/cross-repo/proof-burrower/$f"; done
commit_all pb
gate 12
expect "check 12 needs the patch to be the Agda one" FAIL 12-proof-burrower-agda
git -C "$R" mv docs/handover/cross-repo/proof-burrower/fix.patch docs/handover/cross-repo/proof-burrower/agda-ci.patch; commit_all pb-agda
gate 12
expect "check 12 defers with an Agda patch" DEFERRED 12-proof-burrower-agda

# ------------------------------------------------- check 6a: XFAIL ledger

xfail() { mkdir -p "$R/tests/fixtures"; printf '%s\n' "$1" > "$R/tests/fixtures/XFAIL.json"; gate 6; }
new_repo
xfail '[{"backend":""},{"backend":" "},{"backend":"","prover":"vampire"}]'
expect "blank backend names fail 06a" FAIL 06a-xfail-ledger "does not name its backend"
xfail '{"entries":[{"backend":"\n"}]}'
expect "a newline backend name fails 06a" FAIL 06a-xfail-ledger
xfail '[{"backend":"*"}]'
expect "a glob backend name fails 06a without expanding" FAIL 06a-xfail-ledger "does not name its backend"
xfail '[{"backend":"agda z3"}]'
expect "a two-word backend name fails 06a" FAIL 06a-xfail-ledger
xfail '[{"backend":"vampire"}]'
expect "an out-of-scope backend fails 06a" FAIL 06a-xfail-ledger "outside V-3 scope: vampire"
xfail '[{"backend":"z3"},{"prover":"agda"}]'
expect "in-scope backends pass 06a" PASS 06a-xfail-ledger "2 entries"
xfail '[]'
expect "an empty ledger passes 06a" PASS 06a-xfail-ledger "empty"

# ---------------------------------------------- check 9: training metrics

metrics() { mkdir -p "$R/models"; printf '%s\n' "$1" > "$R/models/training_metrics.json"; gate 9; }
new_repo
gate 9
expect "absent metrics pass check 9" PASS 09-no-fabricated-metrics "is gone"
metrics '{}'
expect "an empty object fails check 9" FAIL 09-no-fabricated-metrics "no run provenance"
metrics '{"MRR":0.85,"nDCG":0.85,"training_data_size":10012,"timestamp":"2026-04-25T15:26:45.717Z"}'
expect "nudged fabricated metrics fail check 9" FAIL 09-no-fabricated-metrics "fabricated"
metrics '{"MRR":0.41,"nDCG":0.52,"provenance":{"commit":"0123456789abcdef0123456789abcdef01234567","run_id":"run-7"}}'
expect "metrics with run provenance pass check 9" PASS 09-no-fabricated-metrics "run-7"

# ------------------------------------------------ check 10a: rulings ledger

ids="D-A D-B D-C D-D D-E D-F D-G D-H D-I D-J D-K D-L D-M D-N D2 D3 D5 D6 D7"
ledger() { mkdir -p "$R/docs/decisions"; printf '%s\n' "$1" > "$R/docs/decisions/ADR-020-rulings-ledger.adoc"; gate 10; }
new_repo
ledger "$(printf '= Rulings\n\n== %s\n:status: open\n' "$ids")"
expect "one heading naming every ruling fails 10a" FAIL 10a-rulings-ledger "names more than one ruling"
ledger "$(printf '= Rulings %s\n:status: ruled\nhttps://example.invalid\n' "$ids")"
expect "the document title does not count as sections" FAIL 10a-rulings-ledger "no section of its own"
good_ledger=$(printf '= Rulings\n'; for r in $ids; do printf '\n== %s\n:status: open\n' "$r"; done)
ledger "$good_ledger"
expect "one open section per ruling passes 10a" PASS 10a-rulings-ledger
ledger "${good_ledger/:status: open/:status: ruled
https://example.invalid/x}"
expect "a ruled section with a foreign link fails 10a" FAIL 10a-rulings-ledger "D-A: ruled without a link"
ledger "${good_ledger/:status: open/:status: ruled
https://github.com/hyperpolymath/echidna/issues/1#issuecomment-1}"
expect "a ruled section with the owner's record passes 10a" PASS 10a-rulings-ledger
ledger "${good_ledger/:status: open/:status: open
:status: ruled}"
expect "two status lines in one section fail 10a" FAIL 10a-rulings-ledger "D-A: 2 :status: lines"
commented_ledger=$(printf '= Rulings\n\n////\n== D-A\n:status: open\n////\n'; for r in ${ids#D-A }; do printf '\n== %s\n:status: open\n' "$r"; done)
ledger "$commented_ledger"
expect "a section inside a //// comment block does not count for 10a" FAIL 10a-rulings-ledger "D-A: no section of its own"
ledger "${good_ledger/:status: open/:status: open

----
:status: ruled
== D-A
----

....
:status: ruled
....}"
expect "status lines and headings in listing blocks do not count for 10a" PASS 10a-rulings-ledger

# ------------------------------------------------- check 13: Lean claims

claims() { mkdir -p "$R/docs/proofs"; jq -cS . <<<"$1" > "$R/docs/proofs/claims.json"; gate 13; }
new_repo
claims '{"claims":[{"name":"nix flake check","note":"lean 4.13.0","status":"pass"}]}'
expect "'flake' is not a lake build" FAIL 13-lean-build-recorded
claims '{"claims":[{"claim":"lake build","toolchain":"14.13.01","status":"pass"}]}'
expect "14.13.01 is not version 4.13.0" FAIL 13-lean-build-recorded
claims '{"claims":[{"claim":"lake build","toolchain":"4.13.0","issue":"x"}]}'
expect "a bare issue string is not a scheduled repair" FAIL 13-lean-build-recorded
claims '{"claims":[{"claim":"lake build","toolchain":"4.13.0","repair":{"id":"R-1"}}]}'
expect "a repair item with no place in the schedule fails 13" FAIL 13-lean-build-recorded
claims '{"claims":[{"claim":"lake build","toolchain":"4.13.0","repair":{"id":"R-1","before":"F-3"}}]}'
expect "a repair item before F-3 passes 13" PASS 13-lean-build-recorded
claims '{"claims":[{"claim":"Lean 4 lake build of verification/proofs/lean4","toolchain":"leanprover/lean4:v4.13.0","result":"green"}]}'
expect "a green lake build passes 13" PASS 13-lean-build-recorded
claims '[{"claim":"Lean 4 lake build","toolchain":"4.13.0","result":"green"}]'
expect "a claims.json whose root is an array fails 13" FAIL 13-lean-build-recorded "not a JSON object at its root"

# ----------------------------------------------- check 7: Idris/Agda hygiene

new_repo
mkdir -p "$R/.github/workflows" "$R/src/abi/EchidnaABI" "$R/meta-checker/src/Echidna" "$R/scripts/ci"
printf '# for pattern in postulate; do grep\nrun: echo\n' > "$R/.github/workflows/idris2-abi-ci.yml"
printf 'package x\nmodules = EchidnaABI.CapnSchemas, CoprocessorForeign\n' > "$R/src/abi/echidnaabi.ipkg"
touch "$R/src/abi/EchidnaABI/CapnSchemas.idr" "$R/src/abi/CoprocessorForeign.idr"
printf 'module Echidna.MetaChecker where\n{- import Echidna.AxiomTrackerCompleteness -}\n' > "$R/meta-checker/src/Echidna/MetaChecker.agda"
printf 'run: bash scripts/ci/check-agda.sh\n' > "$R/.github/workflows/agda-meta-checker.yml"
printf 'agda --safe src/Echidna/MetaChecker.agda\n' > "$R/scripts/ci/check-agda.sh"
gate 7
expect "a postulate grep inside a comment fails 07a" FAIL 07a-idris-postulate-grep
expect "the one-line modules layout passes 07b" PASS 07b-ipkg-coverage
expect "an import inside a block comment fails 07c" FAIL 07c-meta-checker-completeness
printf 'run: |\n  for pattern in believe_me postulate; do grep -rn "$pattern" src/abi; done\n' > "$R/.github/workflows/idris2-abi-ci.yml"
printf 'package x\nmodules = Main\n     , EchidnaABI.CapnSchemas\ndepends = base\n     , CoprocessorForeign\n' > "$R/src/abi/echidnaabi.ipkg"
printf 'module Echidna.MetaChecker where\nopen import Echidna.AxiomTrackerCompleteness public\n' > "$R/meta-checker/src/Echidna/MetaChecker.agda"
gate 7
expect "a real postulate grep passes 07a" PASS 07a-idris-postulate-grep
expect "a module listed under depends does not count for 07b" FAIL 07b-ipkg-coverage "CoprocessorForeign"
expect "a real import checked through check-agda.sh passes 07c" PASS 07c-meta-checker-completeness

# Inline `#` comments: a mention after code on the line does not count.
printf 'run: echo ok # grep -rn postulate src/abi\n' > "$R/.github/workflows/idris2-abi-ci.yml"
printf 'module Echidna.MetaChecker where\n' > "$R/meta-checker/src/Echidna/MetaChecker.agda"
printf 'run: echo ok # agda src/Echidna/AxiomTrackerCompleteness.agda\n' > "$R/.github/workflows/agda-meta-checker.yml"
gate 7
expect "a postulate grep in an inline comment fails 07a" FAIL 07a-idris-postulate-grep
expect "an agda call in an inline comment fails 07c" FAIL 07c-meta-checker-completeness
printf 'run: grep -rnE "believe_me #|postulate" src/abi\n' > "$R/.github/workflows/idris2-abi-ci.yml"
printf "run: echo don't # agda src/Echidna/AxiomTrackerCompleteness.agda\n" > "$R/.github/workflows/agda-meta-checker.yml"
gate 7
expect "a # inside quotes does not cut the line for 07a" PASS 07a-idris-postulate-grep
expect "an apostrophe does not hide an inline comment from 07c" FAIL 07c-meta-checker-completeness
printf 'run: agda --safe src/Echidna/AxiomTrackerCompleteness.agda # completeness\n' > "$R/.github/workflows/agda-meta-checker.yml"
gate 7
expect "an agda call before an inline comment passes 07c" PASS 07c-meta-checker-completeness

# ---------------------------------------------------- subset runs and config

new_repo
gate 9
cases=$((cases + 1))
if grep -qE '^FAIL +w0-subset' <<<"$OUT" && grep -q '^W0 config: ' <<<"$OUT" && [ "$RC" -ne 0 ]; then
  echo "ok   a subset run records w0-subset as FAIL and prints its configuration"
else
  failures=$((failures + 1)); echo "FAIL a subset run records w0-subset as FAIL and prints its configuration"
  sed 's/^/     | /' <<<"$OUT"
fi

echo "w0.selftest: $cases cases, $failures failed"
[ "$failures" -eq 0 ]

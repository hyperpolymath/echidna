#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Fast, toolchain-independent regression checks for the issue-maintenance sweep.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/../.."
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

# The real workflows and a synthetic copy of the accidental toolchain rewrite.
bash scripts/ci/check-workflow-duplicate-keys.sh
cat > "$tmp/duplicate.yml" <<'YAML'
jobs:
  test:
    steps:
      - uses: dtolnay/rust-toolchain@v1
        with:
          toolchain: master
        with:
          toolchain: stable
YAML
if bash scripts/ci/check-workflow-duplicate-keys.sh "$tmp/duplicate.yml" > "$tmp/duplicate.log"; then
  echo 'FAIL: duplicate toolchain mapping accepted' >&2
  exit 1
fi
grep -q "duplicate key(s): 'with'" "$tmp/duplicate.log"
cat > "$tmp/valid.yml" <<'YAML'
jobs:
  first:
    steps:
      - name: First
        run: |
          echo 'with: not a YAML key'
          echo 'with: still shell text'
      - name: Second
        run: echo ok
  second:
    steps:
      - name: Third
        run: echo ok
YAML
bash scripts/ci/check-workflow-duplicate-keys.sh "$tmp/valid.yml"

# Managed workflows start with an actions-lock comment, not the SPDX header.
# Inspect the comment preamble rather than assuming the licence is line one.
for f in .github/workflows/*.yml; do
  sed '/^[^#[:space:]]/q' "$f" | grep -q '^# SPDX-License-Identifier:' || {
    echo "FAIL: $f missing SPDX header" >&2; exit 1;
  }
  grep -q '^permissions:' "$f" || {
    echo "FAIL: $f missing top-level permissions" >&2; exit 1;
  }
done

# #240: deletion of legacy source must not leave a reusable exemption behind.
if [[ -n $(git ls-files '*.res') ]]; then
  echo 'FAIL: tracked ReScript source reintroduced' >&2
  exit 1
fi
if grep -Eq '^[^#[:space:]].*\.res$' .hypatia-ignore; then
  echo 'FAIL: stale ReScript exemption reintroduced' >&2
  exit 1
fi

# #239: preserve evidence, route dangerous obligations, and distinguish only
# unambiguous non-deployed runtime assertions. Mixed src modules stay reviewed.
cat > "$tmp/findings.json" <<'JSON'
[
  {"rule_module":"code_safety","type":"unwrap_without_check","severity":"high","file":"/scan/tests/example.rs","line":12},
  {"rule_module":"code_safety","type":"lock_unwrap","severity":"high","file":"/scan/src/rust/testing.rs"},
  {"rule_module":"code_safety","type":"from_raw","severity":"high","file":"tests/ffi.rs"},
  {"rule_module":"code_safety","type":"agda_postulate","severity":"critical","file":"tests/Proof.agda"},
  {"rule_module":"migration_rules","type":"deprecated_api","severity":"medium","file":"src/rescript/src/api/Client.res"},
  {"rule_module":"code_safety","type":"new_rule","severity":"high","file":"src/new.rs"},
  {"rule_module":"code_safety","type":"panic_macro","severity":"high","file":"/elsewhere/tests/example.rs"},
  {"rule_module":"workflow_audit","type":"missing_workflow","severity":"medium","file":"quality.yml"}
]
JSON
jq --arg root /scan -f scripts/ci/triage-hypatia.jq "$tmp/findings.json" > "$tmp/triaged.json"
jq -e --slurpfile original "$tmp/findings.json" '
  (map(del(.triage)) == $original[0]) and
  (.[0].triage | .source_file == "tests/example.rs" and .source_line == 12 and .priority == "test-only-review" and .route == "panicbot") and
  (.[1].triage | .priority == "review" and .context == "production-or-unreviewed" and .source_line == null) and
  (.[2].triage | .risk_class == "ffi-memory-safety" and .route == "echidnabot" and .priority == "review") and
  (.[3].triage | .risk_class == "proof-soundness" and .route == "echidnabot" and .priority == "review") and
  (.[4].triage | .risk_class == "language-migration" and .route == "rhodibot") and
  (.[5].triage | .risk_class == "unclassified-code-safety" and .route == "manual-review") and
  (.[6].triage | .priority == "review" and .source_file == "/elsewhere/tests/example.rs") and
  (.[7].triage.risk_class == "other")
' "$tmp/triaged.json" > /dev/null
for invalid in '{}' '[null]' 'not-json'; do
  if printf '%s\n' "$invalid" | jq --arg root /scan -f scripts/ci/triage-hypatia.jq > /dev/null 2>&1; then
    echo 'FAIL: invalid findings accepted' >&2
    exit 1
  fi
done
printf '[]\n' | jq -e --arg root /scan -f scripts/ci/triage-hypatia.jq > /dev/null

echo 'Issue regression checks passed.'

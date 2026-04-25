#!/usr/bin/env bash
# SPDX-License-Identifier: PMPL-1.0-or-later
# Collect field signal data for STATE.a2ml [field-signal] section
# Runs weekly to track: cold-start latency, corpus growth, vulnerability count, test coverage

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
STATE_FILE="${REPO_ROOT}/.machine_readable/6a2/STATE.a2ml"
TIMESTAMP=$(date -u +"%Y-%m-%d")

# 1. Cold-start latency from Fly.io logs (requires auth)
echo "Collecting Fly.io cold-start metrics..."
if command -v flyctl &> /dev/null; then
    COLD_START=$(flyctl logs --app echidna-nesy 2>/dev/null | grep -o "cold-start latency: [0-9]*" | tail -1 | awk '{print $NF}' || echo "N/A")
else
    COLD_START="N/A (flyctl not installed)"
fi

# 2. Corpus size from merge_corpus.jl output or training_data directory
echo "Collecting corpus metrics..."
if [ -d "${REPO_ROOT}/training_data" ]; then
    CORPUS_SIZE=$(du -sh "${REPO_ROOT}/training_data" | awk '{print $1}')
    PROOF_COUNT=$(find "${REPO_ROOT}/training_data" -name "*.jsonl" -exec wc -l {} + | awk '{sum+=$1} END {print sum}')
else
    CORPUS_SIZE="unknown"
    PROOF_COUNT="0"
fi

# 3. Open vulnerabilities from GitHub API (requires GITHUB_TOKEN)
echo "Collecting vulnerability metrics..."
if [ -n "${GITHUB_TOKEN:-}" ]; then
    VULNS=$(curl -s -H "Authorization: token $GITHUB_TOKEN" \
        "https://api.github.com/repos/hyperpolymath/echidna/vulnerability-alerts" \
        | jq '[.[] | select(.state == "open")] | length' 2>/dev/null || echo "N/A")
else
    VULNS="N/A (GITHUB_TOKEN not set)"
fi

# 4. Test coverage from last test run
echo "Collecting test coverage..."
if [ -f "${REPO_ROOT}/target/.test_summary.txt" ]; then
    TEST_COUNT=$(grep -o "test result:" "${REPO_ROOT}/target/.test_summary.txt" | wc -l || echo "N/A")
else
    TEST_COUNT="N/A"
fi

# 5. Output formatted for manual entry into STATE.a2ml
cat << EOF
# ─ Field signals to add to STATE.a2ml [field-signal] section ─

[[field-signal.signal]]
source = "collect-field-signal.sh automated run"
metric = "cold-start latency"
value = "$COLD_START seconds (echidna-nesy Fly.io deployment)"
collected = "$TIMESTAMP"

[[field-signal.signal]]
source = "training_data directory size"
metric = "corpus growth"
value = "$CORPUS_SIZE total; $PROOF_COUNT proofs (merge_corpus.jl output)"
collected = "$TIMESTAMP"

[[field-signal.signal]]
source = "GitHub API dependabot"
metric = "open vulnerabilities"
value = "$VULNS open alerts"
collected = "$TIMESTAMP"

[[field-signal.signal]]
source = "cargo test --lib"
metric = "test pass rate"
value = "$TEST_COUNT (verify with: cargo test --lib 2>&1 | tail -20)"
collected = "$TIMESTAMP"

# ─ Run this script weekly via cron or scheduled agent ─
# Usage: ./scripts/collect-field-signal.sh >> .field-signal-log.txt
EOF

echo ""
echo "✓ Field signal collection complete. Add the above entries to STATE.a2ml manually or via sed/awk."

#!/usr/bin/env bash
# SPDX-License-Identifier: PMPL-1.0-or-later
# SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell <jonathan.jewell@open.ac.uk>
# Integration tests for ECHIDNA v1.3 full stack

set -euo pipefail

JULIA_URL="http://127.0.0.1:8090"
RUST_URL="http://127.0.0.1:8080/api"
UI_URL="http://127.0.0.1:8000"

echo "╔═══════════════════════════════════════════════════════════╗"
echo "║  ECHIDNA v1.3 - Full Stack Integration Tests             ║"
echo "╚═══════════════════════════════════════════════════════════╝"
echo

# Test 1: Julia ML Health
echo "Test 1: Julia ML API Health"
JULIA_STATUS=$(curl -sf "$JULIA_URL/health" | jq -r '.status')
if [ "$JULIA_STATUS" = "ok" ]; then
    echo "  ✓ Julia ML API responding"
    curl -s "$JULIA_URL/health" | jq '.models'
else
    echo "  ✗ Julia ML API not healthy"
    exit 1
fi
echo

# Test 2: Rust Backend Health
echo "Test 2: Rust Backend Health"
RUST_STATUS=$(curl -sf "$RUST_URL/health" | jq -r '.status')
if [ "$RUST_STATUS" = "ok" ]; then
    echo "  ✓ Rust backend responding"
else
    echo "  ✗ Rust backend not healthy"
    exit 1
fi
echo

# Test 3: List Provers
echo "Test 3: List Available Provers"
PROVER_COUNT=$(curl -sf "$RUST_URL/provers" | jq '.provers | length')
echo "  ✓ Found $PROVER_COUNT provers"
curl -sf "$RUST_URL/provers" | jq -r '.provers[] | "    - \(.name)"'
echo

# Test 4: Julia ML Tactic Suggestions
echo "Test 4: Julia ML Tactic Suggestions (Direct)"
GOAL='{"goal":"forall n : nat, n + 0 = n", "prover":"Coq", "top_k":3}'
SUGGESTION_COUNT=$(curl -sf -X POST "$JULIA_URL/suggest" \
    -H "Content-Type: application/json" \
    -d "$GOAL" | jq '.suggestions | length')
echo "  ✓ Got $SUGGESTION_COUNT ML suggestions from Julia"
curl -sf -X POST "$JULIA_URL/suggest" \
    -H "Content-Type: application/json" \
    -d "$GOAL" | jq -r '.suggestions[] | "    - \(.tactic) (confidence: \(.confidence))"'
echo

# Test 5: Rust → Julia Integration
echo "Test 5: Rust Backend → Julia ML Integration"
RUST_GOAL='{"goal":"forall n : nat, n + 0 = n", "prover":"Coq", "top_k":5}'
RUST_SUGGESTION_COUNT=$(curl -sf -X POST "$RUST_URL/tactics/suggest" \
    -H "Content-Type: application/json" \
    -d "$RUST_GOAL" | jq '.suggestions | length')
echo "  ✓ Got $RUST_SUGGESTION_COUNT suggestions via Rust backend"
curl -sf -X POST "$RUST_URL/tactics/suggest" \
    -H "Content-Type: application/json" \
    -d "$RUST_GOAL" | jq -r '.suggestions[] | "    - \(.tactic) (confidence: \(.confidence))"'
echo

# Test 6: Create Proof Session
echo "Test 6: Create Proof Session"
SESSION_RESP=$(curl -sf -X POST "$RUST_URL/session/create" \
    -H "Content-Type: application/json" \
    -d '{"prover":"Coq"}')
SESSION_ID=$(echo "$SESSION_RESP" | jq -r '.session_id')
echo "  ✓ Created session: $SESSION_ID"
echo

# Test 7: Get Aspect Tags
echo "Test 7: Get Aspect Tags"
TAG_COUNT=$(curl -sf "$RUST_URL/aspect-tags" | jq '.tags | length')
echo "  ✓ Found $TAG_COUNT aspect tags"
curl -sf "$RUST_URL/aspect-tags" | jq -r '.tags[] | "    - \(.name): \(.description)"'
echo

# Test 8: UI Dev Server
echo "Test 8: UI Dev Server"
UI_STATUS=$(curl -sf -o /dev/null -w "%{http_code}" "$UI_URL/")
if [ "$UI_STATUS" = "200" ]; then
    echo "  ✓ UI dev server responding"
else
    echo "  ✗ UI dev server not responding (status: $UI_STATUS)"
    exit 1
fi
echo

echo "╔═══════════════════════════════════════════════════════════╗"
echo "║  All Integration Tests Passed ✓                          ║"
echo "╚═══════════════════════════════════════════════════════════╝"
echo
echo "Services running:"
echo "  Julia ML API:    $JULIA_URL"
echo "  Rust Backend:    $RUST_URL"
echo "  ReScript UI:     $UI_URL"
echo
echo "Access the UI at: http://127.0.0.1:3000"

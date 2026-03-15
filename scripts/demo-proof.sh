#!/bin/bash
# SPDX-License-Identifier: MIT OR Palimpsest-0.6
# ECHIDNA Interactive Demo - Proof of Commutativity

set -e

API="http://127.0.0.1:8080/api"

echo "╔════════════════════════════════════════════════════════════╗"
echo "║         ECHIDNA Live Demo - Interactive Proof              ║"
echo "╚════════════════════════════════════════════════════════════╝"
echo ""

# Step 1: Create a proof session
echo "1️⃣  Creating proof session with Coq..."
SESSION_ID=$(curl -s -X POST $API/session/create \
  -H "Content-Type: application/json" \
  -d '{"prover":"Coq"}' | jq -r '.session_id')
echo "   ✓ Session created: $SESSION_ID"
echo ""

# Step 2: Get available provers
echo "2️⃣  Available provers:"
curl -s $API/provers | jq -r '.provers[] | "   • \(.name) (Tier \(.tier), Complexity \(.complexity))"'
echo ""

# Step 3: Get aspect tags
echo "3️⃣  Aspect tags for filtering:"
curl -s $API/aspect-tags | jq -r '.tags[] | "   • \(.name) (\(.category))"'
echo ""

# Step 4: Get tactic suggestions
echo "4️⃣  AI-powered tactic suggestions for goal:"
curl -s -X POST $API/tactics/suggest \
  -H "Content-Type: application/json" \
  -d '{"goal_id":"example-goal","active_tags":["algebraic","deductive"]}' | \
  jq -r '.suggestions[] | "   • \(.tactic) (confidence: \(.confidence * 100)%)"'
echo ""

# Step 5: Search theorems
echo "5️⃣  Searching theorem library for 'commutativity'..."
curl -s "$API/theorems/search?query=commutativity" | \
  jq -r '.results[] | "   • \(.)"'
echo ""

# Step 6: Get proof tree
echo "6️⃣  Proof tree structure:"
curl -s "$API/session/$SESSION_ID/tree" | jq '.'
echo ""

# Step 7: Get session state
echo "7️⃣  Session state:"
curl -s "$API/session/$SESSION_ID/state" | jq '.'
echo ""

echo "╔════════════════════════════════════════════════════════════╗"
echo "║                    Demo Complete! ✓                        ║"
echo "╚════════════════════════════════════════════════════════════╝"
echo ""
echo "Next steps:"
echo "  • Open http://127.0.0.1:3000 in your browser"
echo "  • Try applying tactics to the proof"
echo "  • Explore the interactive UI"
echo ""

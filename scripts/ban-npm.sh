#!/usr/bin/env bash
#
# ECHIDNA NPM Ban Enforcement Script
# This script checks for and blocks npm/node usage
#
# SPDX-License-Identifier: MPL-2.0

set -euo pipefail

RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

echo "🔍 ECHIDNA NPM Ban Check"
echo "========================"

VIOLATIONS=0

# Check for package-lock.json
if [ -f "package-lock.json" ]; then
    echo -e "${RED}❌ VIOLATION: package-lock.json found in root${NC}"
    VIOLATIONS=$((VIOLATIONS + 1))
fi

# Check for node_modules anywhere
if find . -type d -name "node_modules" 2>/dev/null | grep -q .; then
    echo -e "${RED}❌ VIOLATION: node_modules directory found${NC}"
    find . -type d -name "node_modules" 2>/dev/null
    VIOLATIONS=$((VIOLATIONS + 1))
fi

# Check for Deno manifests or lockfiles (deno is banned estate-wide; bun is the runtime)
DENO_FILES=$(find . \( -name .git -o -name target -o -name node_modules \) -prune -o -type f \( -name deno.json -o -name deno.jsonc -o -name deno.lock \) -print 2>/dev/null)
if [ -n "$DENO_FILES" ]; then
    echo -e "${RED}❌ VIOLATION: Deno manifest or lockfile found${NC}"
    echo "$DENO_FILES"
    VIOLATIONS=$((VIOLATIONS + 1))
fi

# Check for npm/npx usage in scripts
if grep -r "npm install\|npm i \|npx \|npm run" scripts/ 2>/dev/null | grep -v "ban-npm"; then
    echo -e "${RED}❌ VIOLATION: npm/npx commands found in scripts${NC}"
    VIOLATIONS=$((VIOLATIONS + 1))
fi

# Check Justfile for npm commands
if [ -f "Justfile" ] && grep -q "npm\|npx" Justfile; then
    echo -e "${RED}❌ VIOLATION: npm/npx found in Justfile${NC}"
    VIOLATIONS=$((VIOLATIONS + 1))
fi

# Summary
echo ""
if [ $VIOLATIONS -eq 0 ]; then
    echo -e "${GREEN}✅ No npm violations found!${NC}"
    echo ""
    echo "Approved package managers:"
    echo "  ✓ Bun (the estate JavaScript runtime)"
    echo ""
    echo "Banned:"
    echo "  ✗ npm, npx, node_modules, deno"
    echo "  ✗ package-lock.json"
    exit 0
else
    echo -e "${RED}❌ Found $VIOLATIONS violation(s)!${NC}"
    echo ""
    echo "To fix:"
    echo "  1. Remove package-lock.json: rm package-lock.json"
    echo "  2. Remove node_modules: rm -rf node_modules"
    echo "  3. Use 'bun run' instead of 'npm run'"
    exit 1
fi

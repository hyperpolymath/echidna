#!/usr/bin/env bash
# SPDX-License-Identifier: PMPL-1.0
# Pre-commit hook: block TypeScript/JavaScript and Node configs
set -euo pipefail

STAGED_FILES=$(git diff --cached --name-only --diff-filter=ACMR)
if [ -z "$STAGED_FILES" ]; then
  exit 0
fi

TS_FILES=$(echo "$STAGED_FILES" | grep -E '\.(ts|tsx)$' | grep -v '\.gen\.' || true)
JS_FILES=$(echo "$STAGED_FILES" | grep -E '\.(js|jsx|mjs|cjs)$' | grep -v '\.res\.js$' | grep -v '\.gen\.' || true)
TS_CONFIGS=$(echo "$STAGED_FILES" | grep -E '(^|/)(tsconfig.*\.json|package\.json|package-lock\.json|pnpm-lock\.yaml|yarn\.lock)$' || true)

if [ -n "$TS_FILES" ] || [ -n "$JS_FILES" ] || [ -n "$TS_CONFIGS" ]; then
  echo "❌ TypeScript/JavaScript or Node config detected. Use ReScript instead."
  [ -n "$TS_FILES" ] && echo "$TS_FILES"
  [ -n "$JS_FILES" ] && echo "$JS_FILES"
  [ -n "$TS_CONFIGS" ] && echo "$TS_CONFIGS"
  exit 1
fi

echo "✅ ReScript-only pre-commit check passed"

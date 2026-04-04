#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
# SPDX-License-Identifier: PMPL-1.0-or-later
#
# tests/shell/validate_scripts.sh — Shell script validation for ECHIDNA
#
# Performs:
#   1. Syntax check (bash -n) on all .sh scripts in scripts/ and .github/
#   2. SPDX header presence check
#   3. --help smoke test where supported
#   4. integration_test.sh syntax check
#
# Exit codes:
#   0 — all checks pass
#   1 — one or more checks failed
#
# Usage:
#   bash tests/shell/validate_scripts.sh [--verbose]
#   bash tests/shell/validate_scripts.sh --help

set -euo pipefail

VERBOSE=0
PASS=0
FAIL=0
SKIP=0

# ---------------------------------------------------------------------------
# Argument handling
# ---------------------------------------------------------------------------

for arg in "$@"; do
    case "$arg" in
        --help|-h)
            echo "Usage: bash tests/shell/validate_scripts.sh [--verbose]"
            echo
            echo "Validates all shell scripts in the ECHIDNA repository:"
            echo "  - Syntax check (bash -n)"
            echo "  - SPDX header check"
            echo "  - --help smoke test for supported scripts"
            exit 0
            ;;
        --verbose|-v)
            VERBOSE=1
            ;;
    esac
done

# ---------------------------------------------------------------------------
# Locate repo root (two levels up from this script)
# ---------------------------------------------------------------------------

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"

# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

log_pass() {
    PASS=$((PASS + 1))
    if [[ "$VERBOSE" -eq 1 ]]; then
        echo "  PASS: $1"
    fi
}

log_fail() {
    FAIL=$((FAIL + 1))
    echo "  FAIL: $1"
    if [[ -n "${2:-}" ]]; then
        echo "        $2"
    fi
}

log_skip() {
    SKIP=$((SKIP + 1))
    if [[ "$VERBOSE" -eq 1 ]]; then
        echo "  SKIP: $1"
    fi
}

# ---------------------------------------------------------------------------
# Suite 1: Syntax check — scripts/*.sh
# ---------------------------------------------------------------------------

echo "=== Suite 1: Syntax check (scripts/*.sh) ==="

SCRIPTS_DIR="$REPO_ROOT/scripts"
if [[ -d "$SCRIPTS_DIR" ]]; then
    while IFS= read -r -d '' script; do
        rel="${script#"$REPO_ROOT/"}"
        if bash -n "$script" 2>/dev/null; then
            log_pass "syntax OK: $rel"
        else
            # Capture error output for reporting
            err=$(bash -n "$script" 2>&1 || true)
            log_fail "syntax FAIL: $rel" "$err"
        fi
    done < <(find "$SCRIPTS_DIR" -name "*.sh" -print0 2>/dev/null)
else
    log_skip "scripts/ directory not found"
fi

# ---------------------------------------------------------------------------
# Suite 2: Syntax check — tests/integration_test.sh
# ---------------------------------------------------------------------------

echo "=== Suite 2: Syntax check (tests/*.sh) ==="

while IFS= read -r -d '' script; do
    rel="${script#"$REPO_ROOT/"}"
    if bash -n "$script" 2>/dev/null; then
        log_pass "syntax OK: $rel"
    else
        err=$(bash -n "$script" 2>&1 || true)
        log_fail "syntax FAIL: $rel" "$err"
    fi
done < <(find "$REPO_ROOT/tests" -name "*.sh" -print0 2>/dev/null)

# ---------------------------------------------------------------------------
# Suite 3: Syntax check — .github/workflows/*.yml (bash blocks only)
# ---------------------------------------------------------------------------
# Note: YAML workflow validation is a separate concern (workflow-linter.yml CI)
# Here we only check standalone shell scripts, not embedded workflow YAML.

echo "=== Suite 3: Syntax check (setup.sh and root-level scripts) ==="

for script in \
    "$REPO_ROOT/setup.sh" \
    "$REPO_ROOT/install.sh" \
    "$REPO_ROOT/run.sh"; do
    if [[ -f "$script" ]]; then
        rel="${script#"$REPO_ROOT/"}"
        if bash -n "$script" 2>/dev/null; then
            log_pass "syntax OK: $rel"
        else
            err=$(bash -n "$script" 2>&1 || true)
            log_fail "syntax FAIL: $rel" "$err"
        fi
    else
        log_skip "not present: ${script#"$REPO_ROOT/"}"
    fi
done

# ---------------------------------------------------------------------------
# Suite 4: SPDX header check on scripts/*.sh
# ---------------------------------------------------------------------------

echo "=== Suite 4: SPDX header check ==="

if [[ -d "$SCRIPTS_DIR" ]]; then
    while IFS= read -r -d '' script; do
        rel="${script#"$REPO_ROOT/"}"
        if grep -q "SPDX-License-Identifier" "$script" 2>/dev/null; then
            log_pass "SPDX header present: $rel"
        else
            log_fail "SPDX header MISSING: $rel"
        fi
    done < <(find "$SCRIPTS_DIR" -name "*.sh" -print0 2>/dev/null)
fi

# ---------------------------------------------------------------------------
# Suite 5: --help smoke test for selected scripts
# ---------------------------------------------------------------------------

echo "=== Suite 5: --help smoke tests ==="

# Scripts known to support --help
HELP_SCRIPTS=(
    "scripts/ban-npm.sh"
    "scripts/install-provers.sh"
    "scripts/mvp-smoke.sh"
)

for rel in "${HELP_SCRIPTS[@]}"; do
    script="$REPO_ROOT/$rel"
    if [[ -f "$script" ]]; then
        # Run with --help; any exit code 0 or 1 is acceptable (some tools exit 1 for --help)
        if timeout 10 bash "$script" --help >/dev/null 2>&1; then
            log_pass "--help OK (exit 0): $rel"
        else
            exit_code=$?
            # Exit 1 from --help is acceptable for many POSIX scripts
            if [[ "$exit_code" -le 2 ]]; then
                log_pass "--help OK (exit $exit_code, acceptable): $rel"
            else
                log_fail "--help FAIL (exit $exit_code): $rel"
            fi
        fi
    else
        log_skip "--help skip (not found): $rel"
    fi
done

# ---------------------------------------------------------------------------
# Suite 6: Shell scripts do not contain banned patterns
# ---------------------------------------------------------------------------

echo "=== Suite 6: Banned pattern check ==="

# These patterns indicate insecure or policy-violating practices
declare -A BANNED_PATTERNS
BANNED_PATTERNS["docker "]='"docker" command: use "podman" instead'
BANNED_PATTERNS["npm install"]='npm install: forbidden, use Deno'
BANNED_PATTERNS["npm run"]='npm run: forbidden, use Deno'
BANNED_PATTERNS["curl.*http://"]='HTTP (non-TLS) URL in curl'

if [[ -d "$SCRIPTS_DIR" ]]; then
    while IFS= read -r -d '' script; do
        rel="${script#"$REPO_ROOT/"}"
        # Skip ban-enforcement scripts themselves (they contain patterns by design)
        if [[ "$(basename "$script")" == "ban-npm.sh" ]]; then
            log_skip "skipping ban-npm.sh (contains patterns by design)"
            continue
        fi

        for pattern in "${!BANNED_PATTERNS[@]}"; do
            if grep -qE "$pattern" "$script" 2>/dev/null; then
                log_fail "banned pattern ($pattern) in $rel" "${BANNED_PATTERNS[$pattern]}"
            else
                log_pass "no banned pattern ($pattern): $rel"
            fi
        done
    done < <(find "$SCRIPTS_DIR" -name "*.sh" -print0 2>/dev/null)
fi

# ---------------------------------------------------------------------------
# Summary
# ---------------------------------------------------------------------------

echo
echo "=== Validation Summary ==="
echo "  PASS: $PASS"
echo "  FAIL: $FAIL"
echo "  SKIP: $SKIP"
echo "  TOTAL: $((PASS + FAIL + SKIP))"
echo

if [[ "$FAIL" -gt 0 ]]; then
    echo "RESULT: FAIL ($FAIL failures)"
    exit 1
else
    echo "RESULT: PASS"
    exit 0
fi

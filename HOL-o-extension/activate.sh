#!/usr/bin/env bash
# SPDX-License-Identifier: PMPL-1.0-or-later
#
# activate.sh — Enable the HOL-o-extension overlay
#
# Usage:
#   source echidna/HOL-o-extension/activate.sh
#
# This extends HOL's load path with custom theories and tactics from
# this o-extension. It does NOT modify any files in ../HOL/.
#
# To deactivate:
#   unset HOL_OEXT_ACTIVE HOL_OEXT_DIR
#   # Restart HOL to clear loaded theories

# Resolve the o-extension directory (works even when sourced from elsewhere)
HOL_OEXT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
export HOL_OEXT_DIR

# Verify base HOL exists
HOL_BASE="${HOL_OEXT_DIR}/../HOL"
if [[ ! -d "$HOL_BASE" ]]; then
    echo "ERROR: HOL base not found at ${HOL_BASE}" >&2
    echo "       The o-extension requires HOL4 as a peer directory at ../HOL" >&2
    return 1 2>/dev/null || exit 1
fi

# Extend HOLDIR's load path with our theories and tactics
# HOL4 uses HOLDIR for its root; we add our paths to the search
if [[ -z "${HOLDIR:-}" ]]; then
    export HOLDIR="${HOL_BASE}"
fi

# Add o-extension paths to HOL's load mechanism
# HOL4 uses HOLMOSMLPATH or HOLHEAP for additional search paths
if [[ -n "${HOLMOSMLPATH:-}" ]]; then
    export HOLMOSMLPATH="${HOL_OEXT_DIR}/theories:${HOL_OEXT_DIR}/tactics:${HOLMOSMLPATH}"
else
    export HOLMOSMLPATH="${HOL_OEXT_DIR}/theories:${HOL_OEXT_DIR}/tactics"
fi

# Mark as active
export HOL_OEXT_ACTIVE=1

echo "HOL-o-extension activated"
echo "  Base HOL:    ${HOL_BASE}"
echo "  Theories:    ${HOL_OEXT_DIR}/theories/"
echo "  Tactics:     ${HOL_OEXT_DIR}/tactics/"
echo "  Deactivate:  unset HOL_OEXT_ACTIVE HOL_OEXT_DIR"

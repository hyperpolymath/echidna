#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
#
# validate-k9.sh — K9 configuration file validation script
#
# Scans for .k9 and .k9.ncl files and validates:
#   1. K9! magic number on line 1
#   2. Pedigree block presence with required fields (name, version)
#   3. Security level is one of: kennel, yard, hunt (case-insensitive)
#   4. Hunt-level files must have a signature or signature_required field
#   5. SPDX-License-Identifier header presence
#
# Environment variables:
#   INPUT_PATH   — Directory to scan (default: .)
#   INPUT_STRICT — Promote warnings to errors (default: false)
#
# Exit codes:
#   0 — All files valid (or only warnings in non-strict mode)
#   1 — Validation errors found

set -euo pipefail

# ---------------------------------------------------------------------------
# Configuration
# ---------------------------------------------------------------------------

SCAN_PATH="${INPUT_PATH:-.}"
STRICT="${INPUT_STRICT:-false}"
PATHS_IGNORE_RAW="${INPUT_PATHS_IGNORE:-}"
GITHUB_OUTPUT_FILE="${GITHUB_OUTPUT:-/dev/null}"

# Parse paths-ignore: newline-separated fragments, blank lines and # comments
# stripped. Each fragment is a substring match against the file path. Pattern
# adopted from hyperpolymath/hypatia#243 — content-pattern validators must
# distinguish a target from a vendored / fixture file that legitimately
# contains the very pattern being checked.
PATHS_IGNORE=()
while IFS= read -r _frag; do
    # Strip leading and trailing whitespace (canonical bash idiom).
    _frag="${_frag#"${_frag%%[![:space:]]*}"}"
    _frag="${_frag%"${_frag##*[![:space:]]}"}"
    [[ -z "$_frag" || "$_frag" == \#* ]] && continue
    PATHS_IGNORE+=("$_frag")
done <<< "$PATHS_IGNORE_RAW"

# Returns 0 if path should be skipped (matches any ignore fragment)
path_ignored() {
    local p="$1" frag
    for frag in "${PATHS_IGNORE[@]}"; do
        [[ "$p" == *"$frag"* ]] && return 0
    done
    return 1
}

# Counters
FILES_SCANNED=0
ERRORS=0
WARNINGS=0

# Valid security levels (the leash metaphor)
VALID_LEVELS="kennel yard hunt"

# ---------------------------------------------------------------------------
# Helper: emit GitHub annotation
# ---------------------------------------------------------------------------
annotate() {
    local level="$1" file="$2" line="$3" message="$4"
    echo "::${level} file=${file},line=${line}::${message}"
}

# ---------------------------------------------------------------------------
# Helper: report issue (respects strict mode)
# ---------------------------------------------------------------------------
report_issue() {
    local severity="$1" file="$2" line="$3" message="$4"

    if [[ "$severity" == "warning" && "$STRICT" == "true" ]]; then
        severity="error"
    fi

    annotate "$severity" "$file" "$line" "$message"

    if [[ "$severity" == "error" ]]; then
        ERRORS=$((ERRORS + 1))
    else
        WARNINGS=$((WARNINGS + 1))
    fi
}

# ---------------------------------------------------------------------------
# Helper: normalise a security level string
# ---------------------------------------------------------------------------
# Strips quotes, leading/trailing whitespace, Nickel enum tick prefix
normalise_level() {
    local raw="$1"
    # Remove surrounding quotes, tick prefix ('Kennel -> Kennel), whitespace
    raw="${raw#*=}"              # Remove everything before =
    raw="${raw//\"/}"            # Remove double quotes
    raw="${raw//\'/}"            # Remove single quotes (Nickel tick)
    raw="${raw//,/}"             # Remove trailing commas
    raw="${raw## }"              # Trim leading space
    raw="${raw%% }"              # Trim trailing space
    raw="${raw%%#*}"             # Remove inline comments
    raw="${raw## }"              # Trim again
    raw="${raw%% }"
    echo "${raw,,}"             # Lowercase
}

# ---------------------------------------------------------------------------
# Validator: check a single K9 file
# ---------------------------------------------------------------------------
validate_k9() {
    local file="$1"
    FILES_SCANNED=$((FILES_SCANNED + 1))

    # --- Check 1: K9! magic number on first non-empty line ---
    local first_content_line=""
    local first_content_line_num=0
    local line_num=0

    while IFS= read -r line; do
        line_num=$((line_num + 1))
        # Skip empty lines
        if [[ -z "${line// /}" ]]; then
            continue
        fi
        first_content_line="$line"
        first_content_line_num=$line_num
        break
    done < "$file"

    if [[ "$first_content_line" != "K9!" ]]; then
        report_issue "error" "$file" "$first_content_line_num" \
            "Missing K9! magic number. First non-empty line must be exactly 'K9!'"
    fi

    # --- Check 2: SPDX header ---
    local has_spdx=false
    line_num=0
    while IFS= read -r line; do
        line_num=$((line_num + 1))
        if [[ $line_num -gt 10 ]]; then
            break
        fi
        if [[ "$line" == *"SPDX-License-Identifier"* ]]; then
            has_spdx=true
            break
        fi
    done < "$file"

    if [[ "$has_spdx" == "false" ]]; then
        report_issue "warning" "$file" 1 \
            "Missing SPDX-License-Identifier in first 10 lines"
    fi

    # --- Check 3: Pedigree block with required fields ---
    local has_pedigree=false
    local has_pedigree_name=false
    local has_pedigree_version=false
    local has_security_level=false
    local security_level_value=""
    local security_level_line=0
    local has_signature_field=false
    local in_pedigree=false
    local pedigree_depth=0

    line_num=0
    while IFS= read -r line; do
        line_num=$((line_num + 1))

        # Detect pedigree block start. Note: do NOT `continue` here — the
        # `pedigree = {` line itself contains the opening brace that
        # establishes the block. Falling through to the brace counter
        # below makes depth start at 1, so a subsequent `security = {…},`
        # closing brace correctly takes depth to 1 (not 0), keeping us
        # inside the pedigree block when later fields (name/version/leash)
        # are checked. Previously the `continue` skipped this opening
        # brace, depth started at 0, and the first nested block's close
        # prematurely terminated the validator's view of the pedigree —
        # making `pedigree.metadata.name` invisible.
        if [[ "$line" =~ ^[[:space:]]*pedigree[[:space:]]*= ]]; then
            has_pedigree=true
            in_pedigree=true
            pedigree_depth=0
            # fall through
        fi

        if [[ "$in_pedigree" == "true" ]]; then
            # Track brace depth to know when pedigree block ends
            local opens closes
            opens="${line//[^\{]/}"
            closes="${line//[^\}]/}"
            pedigree_depth=$(( pedigree_depth + ${#opens} - ${#closes} ))

            if [[ $pedigree_depth -le 0 && "$has_pedigree" == "true" ]]; then
                # Check this final line too before leaving
                :
            fi

            # Check for name field within pedigree.metadata or pedigree directly.
            # Two patterns cover both multi-line and single-line pedigrees:
            #   1. ^[[:space:]]+name[[:space:]]*= — the normal multi-line case where
            #      `name = "..."` appears on its own indented line.
            #   2. [[:space:]]name[[:space:]]*= — inline within a single-line
            #      pedigree assignment such as:
            #        pedigree = component_pedigree & { name = "foo" }
            #      (root cause: developer-ecosystem@baab1534 — single-line form
            #      was missed entirely because the pedigree block opened and
            #      closed in one line, never reaching the ^[[:space:]]+ check on
            #      a subsequent iteration.)
            if [[ "$line" =~ ^[[:space:]]+name[[:space:]]*= ]] || \
               [[ "$line" =~ [[:space:]]name[[:space:]]*= ]]; then
                has_pedigree_name=true
            fi

            # Check for version field
            if [[ "$line" =~ ^[[:space:]]+(version|schema_version)[[:space:]]*= ]] || \
               [[ "$line" =~ [[:space:]](version|schema_version)[[:space:]]*= ]]; then
                has_pedigree_version=true
            fi

            # Check for security level (leash field)
            if [[ "$line" =~ ^[[:space:]]+(leash|security_level)[[:space:]]*= ]]; then
                has_security_level=true
                security_level_value="$(normalise_level "$line")"
                security_level_line=$line_num
            fi

            # Check for signature fields
            if [[ "$line" =~ ^[[:space:]]+(signature|signature_required)[[:space:]]*= ]]; then
                has_signature_field=true
            fi

            # End of pedigree block
            if [[ $pedigree_depth -le 0 && "$has_pedigree" == "true" && "$line" == *"}"* ]]; then
                in_pedigree=false
            fi
        fi

        # Also check for signature fields outside pedigree (top-level)
        if [[ "$line" =~ ^[[:space:]]*(signature)[[:space:]]*= ]]; then
            has_signature_field=true
        fi
    done < "$file"

    if [[ "$has_pedigree" == "false" ]]; then
        report_issue "error" "$file" 1 \
            "Missing pedigree block. K9 files must contain a 'pedigree = { ... }' section"
    else
        if [[ "$has_pedigree_name" == "false" ]]; then
            report_issue "error" "$file" 1 \
                "Pedigree block missing 'name' field (in pedigree.metadata.name or pedigree.name)"
        fi

        if [[ "$has_pedigree_version" == "false" ]]; then
            report_issue "warning" "$file" 1 \
                "Pedigree block missing 'version' or 'schema_version' field"
        fi
    fi

    # --- Check 4: Security level validation ---
    if [[ "$has_security_level" == "true" ]]; then
        local level_valid=false
        for valid in $VALID_LEVELS; do
            if [[ "$security_level_value" == "$valid" ]]; then
                level_valid=true
                break
            fi
        done

        if [[ "$level_valid" == "false" ]]; then
            report_issue "error" "$file" "$security_level_line" \
                "Invalid security level '${security_level_value}'. Must be one of: kennel, yard, hunt"
        fi
    else
        if [[ "$has_pedigree" == "true" ]]; then
            report_issue "warning" "$file" 1 \
                "No security level (leash/security_level) found in pedigree block"
        fi
    fi

    # --- Check 5: Hunt-level signature requirement ---
    if [[ "$security_level_value" == "hunt" && "$has_signature_field" == "false" ]]; then
        report_issue "error" "$file" "$security_level_line" \
            "Hunt-level K9 file must include a 'signature' or 'signature_required' field"
    fi
}

# ---------------------------------------------------------------------------
# Main: discover and validate K9 files
# ---------------------------------------------------------------------------

echo "::group::K9 Configuration Validation"
echo "Scanning ${SCAN_PATH} for K9 files (.k9, .k9.ncl)..."
echo ""

# Find all K9 files, excluding .git directory
mapfile -t k9_candidates < <(find "$SCAN_PATH" \( -name '*.k9' -o -name '*.k9.ncl' \) -not -path '*/.git/*' -type f | sort)

# Apply paths-ignore filter
k9_files=()
SKIPPED=0
for _f in "${k9_candidates[@]}"; do
    if path_ignored "$_f"; then
        SKIPPED=$((SKIPPED + 1))
        continue
    fi
    k9_files+=("$_f")
done

if [[ $SKIPPED -gt 0 ]]; then
    echo "::notice::Skipped ${SKIPPED} file(s) matching paths-ignore"
fi

if [[ ${#k9_files[@]} -eq 0 ]]; then
    echo "::notice::No K9 files found in ${SCAN_PATH}"
    echo "files_scanned=0" >> "$GITHUB_OUTPUT_FILE" 2>/dev/null || true
    echo "errors=0" >> "$GITHUB_OUTPUT_FILE" 2>/dev/null || true
    echo "warnings=0" >> "$GITHUB_OUTPUT_FILE" 2>/dev/null || true
    echo "::endgroup::"
    exit 0
fi

echo "Found ${#k9_files[@]} K9 file(s)"
echo ""

for file in "${k9_files[@]}"; do
    echo "  Validating: ${file}"
    validate_k9 "$file"
done

echo ""
echo "────────────────────────────────────────"
echo "Files scanned: ${FILES_SCANNED}"
echo "Errors:        ${ERRORS}"
echo "Warnings:      ${WARNINGS}"
echo "Strict mode:   ${STRICT}"
echo "────────────────────────────────────────"

# Write outputs for GitHub Actions
{
    echo "files_scanned=${FILES_SCANNED}"
    echo "errors=${ERRORS}"
    echo "warnings=${WARNINGS}"
} >> "$GITHUB_OUTPUT_FILE" 2>/dev/null || true

echo "::endgroup::"

# Exit with failure if errors were found
if [[ $ERRORS -gt 0 ]]; then
    echo "::error::K9 validation failed with ${ERRORS} error(s)"
    exit 1
fi

echo "K9 validation passed."
exit 0

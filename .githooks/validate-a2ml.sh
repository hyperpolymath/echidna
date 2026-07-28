#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
#
# validate-a2ml.sh — A2ML manifest validation script
#
# Scans for .a2ml files and validates:
#   1. Required fields: agent-id or pedigree name, version
#   2. SPDX-License-Identifier header presence
#   3. Attestation block structure (if present)
#   4. Section heading syntax ([section] or ## section)
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

# ---------------------------------------------------------------------------
# Helper: emit GitHub annotation
# ---------------------------------------------------------------------------
# Usage: annotate <level> <file> <line> <message>
#   level: error | warning | notice
annotate() {
    local level="$1" file="$2" line="$3" message="$4"
    echo "::${level} file=${file},line=${line}::${message}"
}

# ---------------------------------------------------------------------------
# Helper: report issue (respects strict mode)
# ---------------------------------------------------------------------------
# Usage: report_issue <severity> <file> <line> <message>
#   severity: error | warning
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
# Validator: check a single .a2ml file
# ---------------------------------------------------------------------------
validate_a2ml() {
    local file="$1"
    FILES_SCANNED=$((FILES_SCANNED + 1))

    # --- Check 1: SPDX header ---
    # The SPDX-License-Identifier should appear in the first 10 lines
    local has_spdx=false
    local line_num=0
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

    # --- Check 2: Required identity fields ---
    # A2ML files must contain either:
    #   - agent-id = "..." or agent_id = "..."
    #   - pedigree block with name field
    #   - name = "..." at top level (for AI manifests)
    #   - project = "..." (for STATE.a2ml)
    local has_identity=false
    local has_version=false
    line_num=0

    while IFS= read -r line; do
        line_num=$((line_num + 1))

        # Check for identity fields (various A2ML patterns)
        # TOML/kv form: `name = "..."`, `project = "..."`, `agent-id = "..."`
        if [[ "$line" =~ ^[[:space:]]*(agent[-_]id|name|project)[[:space:]]*= ]]; then
            has_identity=true
        fi
        # S-expression form: `(name "...")`, `(project "...")`,
        # `(agent-id "...")`. Some A2ML dialects (audit registries,
        # classification stores) use Lisp-style s-expressions for the
        # metadata block instead of TOML. Identity carries the same
        # semantics; only the syntax differs. Match at any indent so it
        # also picks up entries nested under `(metadata ...)`.
        if [[ "$line" =~ ^[[:space:]]*\([[:space:]]*(agent[-_]id|name|project)[[:space:]]+\" ]]; then
            has_identity=true
        fi
        # Colon / brace-block form: `name: "..."`, `id: "..."`, `project: "..."`.
        # YAML-ish and brace-block A2ML dialects (e.g. `Trust { name: "..." }`,
        # `id: "tsdm-standard"`) carry the same identity semantics; only the
        # delimiter (`:` vs `=`) differs. `id` is the brace-block spelling of an
        # identity key.
        if [[ "$line" =~ ^[[:space:]]*(agent[-_]id|name|project|id)[[:space:]]*: ]]; then
            has_identity=true
        fi
        # Check for version field — TOML form
        if [[ "$line" =~ ^[[:space:]]*(version|schema_version)[[:space:]]*= ]]; then
            has_version=true
        fi
        # Version field — s-expression form
        if [[ "$line" =~ ^[[:space:]]*\([[:space:]]*(version|schema_version)[[:space:]]+\" ]]; then
            has_version=true
        fi
        # Version field — colon / brace-block form
        if [[ "$line" =~ ^[[:space:]]*(version|schema_version)[[:space:]]*: ]]; then
            has_version=true
        fi
    done < "$file"

    # AI manifest files (0-AI-MANIFEST.a2ml, 0.1-AI-MANIFEST.a2ml, etc.)
    # use markdown-style headers and free text, so identity check is relaxed
    local basename
    basename="$(basename "$file")"
    local is_manifest=false
    if [[ "$basename" == *"AI-MANIFEST"* ]]; then
        is_manifest=true
    fi
    # Canonical typed manifests under .machine_readable/descriptiles/ — identity comes
    # from the enclosing directory + filename, not an in-file field. Sibling
    # files in the same directory (ECOSYSTEM.a2ml, STATE.a2ml) DO carry their
    # own $name/project and continue to be validated normally.
    case "$basename" in
        AGENTIC.a2ml|META.a2ml|NEUROSYM.a2ml|PLAYBOOK.a2ml|AI.a2ml)
            # AI.a2ml = free-text "AI Assistant Instructions" manifest, the same
            # doc type as 0-AI-MANIFEST.a2ml but with the bare name; identity is
            # carried by the enclosing repo/plugin dir, not an in-file field.
            is_manifest=true
            ;;
        # Dockerfile-style top-level typed manifests (Intentfile, Trustfile, …)
        # use markdown-flavoured A2ML; identity is carried by the parent repo.
        *file.a2ml)
            is_manifest=true
            ;;
    esac

    # Contractile-shape A2ML files use `@directive:` syntax instead of
    # TOML `key = value`. Trustfile.a2ml, Intentfile.a2ml, Mustfile.a2ml,
    # Adjustfile.a2ml etc. are policy / trust / intent / abstract files
    # whose identity is implicit in their @-prefixed directives
    # (`@trust-level`, `@intent`, ...) rather than a TOML name/version
    # pair. Treating them as manifest-shape produces 100% false positives —
    # they're a different A2ML doc type. Detected by the presence of any
    # contractile directive in the file body.
    local is_contractile_shape=false
    if grep -qE '^@(abstract|trust-level|trust-boundary|trust-actions|trust-deny|intent|must|adjust|end)([[:space:]]*:|$)' "$file"; then
        is_contractile_shape=true
    fi

    # Canonical structured A2ML tree. Everything under a `.machine_readable/`
    # directory is a typed agent-readable doc (CLADE, ANCHOR, STATE,
    # ECOSYSTEM, bot_directives/{debt,coverage,methodology}, ai/AI,
    # policies/*, integrations/*, …). Per the RSR convention these carry
    # identity structurally — owning repo + path + filename — not via an
    # in-file `name`/`agent-id`. This generalises the `.machine_readable/descriptiles/`
    # rationale above to the whole tree: rsr-template-repo itself ships these
    # files without an in-file identity key, so requiring one produces
    # estate-wide false positives on every repo built from the canonical
    # template. Files outside `.machine_readable/` are still validated.
    local is_structural_identity=false
    if [[ "$file" == *"/.machine_readable/"* || "$file" == "./.machine_readable/"* || "$file" == ".machine_readable/"* ]]; then
        is_structural_identity=true
    fi

    if [[ "$has_identity" == "false" && "$is_manifest" == "false" && "$is_contractile_shape" == "false" && "$is_structural_identity" == "false" ]]; then
        report_issue "error" "$file" 1 \
            "Missing required identity field (agent-id, name, or project)"
    fi

    if [[ "$has_version" == "false" && "$is_manifest" == "false" && "$is_contractile_shape" == "false" && "$is_structural_identity" == "false" ]]; then
        report_issue "warning" "$file" 1 \
            "Missing version or schema_version field"
    fi

    # --- Check 3: Attestation block structure ---
    # If file contains [attestation] or ## ATTESTATION, validate it has
    # required sub-fields: proof or signature
    local in_attestation=false
    local attestation_line=0
    local attestation_has_content=false
    line_num=0

    while IFS= read -r line; do
        line_num=$((line_num + 1))

        # Detect attestation section start
        if [[ "$line" =~ ^\[attestation\] ]] || [[ "$line" =~ ^##[[:space:]]+[Aa]ttestation ]] || [[ "$line" =~ ^##[[:space:]]+ATTESTATION ]]; then
            in_attestation=true
            attestation_line=$line_num
            continue
        fi

        # Detect next section (ends attestation block)
        if [[ "$in_attestation" == "true" ]]; then
            if [[ "$line" =~ ^\[.+\] ]] || [[ "$line" =~ ^##[[:space:]] ]]; then
                in_attestation=false
                continue
            fi
            # Check for content in attestation block
            if [[ "$line" =~ (proof|signature|verified|hash)[[:space:]]*= ]]; then
                attestation_has_content=true
            fi
        fi
    done < "$file"

    if [[ $attestation_line -gt 0 && "$attestation_has_content" == "false" ]]; then
        report_issue "warning" "$file" "$attestation_line" \
            "Attestation block found but missing proof/signature/hash fields"
    fi

    # --- Check 4: Section heading syntax ---
    # Validate that [section] headings are well-formed (no unclosed brackets)
    line_num=0
    while IFS= read -r line; do
        line_num=$((line_num + 1))
        # Lines starting with [ should have a matching ]
        if [[ "$line" =~ ^\[ && ! "$line" =~ ^\[.+\] ]]; then
            # Exclude markdown-style links and multi-line values
            if [[ ! "$line" =~ ^\[.*\]\( && ! "$line" =~ ^\[TODO && ! "$line" =~ ^\[YOUR ]]; then
                report_issue "warning" "$file" "$line_num" \
                    "Possibly malformed section heading: unclosed bracket"
            fi
        fi
    done < "$file"
}

# ---------------------------------------------------------------------------
# Main: discover and validate .a2ml files
# ---------------------------------------------------------------------------

echo "::group::A2ML Manifest Validation"
echo "Scanning ${SCAN_PATH} for .a2ml files..."
echo ""

# Find all .a2ml files, excluding .git directory
mapfile -t a2ml_candidates < <(find "$SCAN_PATH" -name '*.a2ml' -not -path '*/.git/*' -type f | sort)

# Apply paths-ignore filter
a2ml_files=()
SKIPPED=0
for _f in "${a2ml_candidates[@]}"; do
    if path_ignored "$_f"; then
        SKIPPED=$((SKIPPED + 1))
        continue
    fi
    a2ml_files+=("$_f")
done

if [[ $SKIPPED -gt 0 ]]; then
    echo "::notice::Skipped ${SKIPPED} file(s) matching paths-ignore"
fi

if [[ ${#a2ml_files[@]} -eq 0 ]]; then
    echo "::notice::No .a2ml files found in ${SCAN_PATH}"
    echo "files_scanned=0" >> "$GITHUB_OUTPUT_FILE" 2>/dev/null || true
    echo "errors=0" >> "$GITHUB_OUTPUT_FILE" 2>/dev/null || true
    echo "warnings=0" >> "$GITHUB_OUTPUT_FILE" 2>/dev/null || true
    echo "::endgroup::"
    exit 0
fi

echo "Found ${#a2ml_files[@]} .a2ml file(s)"
echo ""

for file in "${a2ml_files[@]}"; do
    echo "  Validating: ${file}"
    validate_a2ml "$file"
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
    echo "::error::A2ML validation failed with ${ERRORS} error(s)"
    exit 1
fi

echo "A2ML validation passed."
exit 0

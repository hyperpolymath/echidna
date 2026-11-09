# SPDX-License-Identifier: MPL-2.0
# Imported by the root Justfile (hotspot split); recipes moved verbatim.

# Initialize from RSR template (placeholder replacement)
init:
    #!/usr/bin/env bash
    set -euo pipefail

    echo "═══════════════════════════════════════════════════"
    echo "  RSR Project Bootstrap"
    echo "═══════════════════════════════════════════════════"
    echo ""

    # --- Load defaults from config (if exists) ---
    # Create yours: ~/.config/rsr/defaults
    # Format: OWNER=myorg  AUTHOR="My Name"  AUTHOR_EMAIL=me@example.org ...
    DEFAULTS="${XDG_CONFIG_HOME:-$HOME/.config}/rsr/defaults"
    if [ -f "$DEFAULTS" ]; then
        echo "Loading defaults from $DEFAULTS"
        # shellcheck source=/dev/null
        source "$DEFAULTS"
        echo ""
    fi

    # --- Required values (pre-filled from defaults if available) ---
    read -rp "Project name (human-readable, e.g. My Project): " PROJECT_NAME
    [ -z "$PROJECT_NAME" ] && echo "Error: project name required" && exit 1

    read -rp "Repository slug (e.g. my-project): " REPO
    [ -z "$REPO" ] && echo "Error: repo slug required" && exit 1

    read -rp "Owner [${OWNER:-}]: " _OWNER
    OWNER="${_OWNER:-${OWNER:-}}"
    [ -z "$OWNER" ] && echo "Error: owner required" && exit 1

    read -rp "Author full name [${AUTHOR:-}]: " _AUTHOR
    AUTHOR="${_AUTHOR:-${AUTHOR:-}}"
    [ -z "$AUTHOR" ] && echo "Error: author name required" && exit 1

    read -rp "Author email [${AUTHOR_EMAIL:-}]: " _AUTHOR_EMAIL
    AUTHOR_EMAIL="${_AUTHOR_EMAIL:-${AUTHOR_EMAIL:-}}"
    [ -z "$AUTHOR_EMAIL" ] && echo "Error: email required" && exit 1

    # --- Optional values (pre-filled from defaults if available) ---
    read -rp "Author organization [${AUTHOR_ORG:-none}]: " _AUTHOR_ORG
    AUTHOR_ORG="${_AUTHOR_ORG:-${AUTHOR_ORG:-}}"

    read -rp "Previous/alt email [${AUTHOR_EMAIL_ALT:-none}]: " _AUTHOR_EMAIL_ALT
    AUTHOR_EMAIL_ALT="${_AUTHOR_EMAIL_ALT:-${AUTHOR_EMAIL_ALT:-}}"

    read -rp "Project description []: " PROJECT_DESCRIPTION

    read -rp "Forge domain [${FORGE:-github.com}]: " _FORGE
    FORGE="${_FORGE:-${FORGE:-github.com}}"

    read -rp "Security contact email [${SECURITY_EMAIL:-$AUTHOR_EMAIL}]: " _SECURITY_EMAIL
    SECURITY_EMAIL="${_SECURITY_EMAIL:-${SECURITY_EMAIL:-$AUTHOR_EMAIL}}"

    read -rp "Conduct contact email [${CONDUCT_EMAIL:-$AUTHOR_EMAIL}]: " _CONDUCT_EMAIL
    CONDUCT_EMAIL="${_CONDUCT_EMAIL:-${CONDUCT_EMAIL:-$AUTHOR_EMAIL}}"

    read -rp "Project type (library|binary|monorepo|service|website) [library]: " PROJECT_TYPE
    PROJECT_TYPE="${PROJECT_TYPE:-library}"

    read -rp "Website URL [https://${FORGE}/${OWNER}/${REPO}]: " WEBSITE
    WEBSITE="${WEBSITE:-https://${FORGE}/${OWNER}/${REPO}}"

    # --- Container values (optional — only relevant if container/ exists) ---
    if [ -d "container" ]; then
        echo ""
        echo "── Container configuration (optional) ─────────"
        read -rp "Service name [${REPO}]: " _SERVICE_NAME
        SERVICE_NAME="${_SERVICE_NAME:-${REPO}}"
        read -rp "Primary port [8080]: " _PORT
        PORT="${_PORT:-8080}"
        read -rp "Container registry [ghcr.io/${OWNER}]: " _REGISTRY
        REGISTRY="${_REGISTRY:-ghcr.io/${OWNER}}"
    else
        SERVICE_NAME="${REPO}"
        PORT="8080"
        REGISTRY="ghcr.io/${OWNER}"
    fi

    # --- Derived values ---
    PROJECT_UPPER=$(echo "$REPO" | tr '[:lower:]-' '[:upper:]_')
    PROJECT_LOWER=$(echo "$REPO" | tr '[:upper:]-' '[:lower:]_')
    CURRENT_YEAR=$(date +%Y)
    CURRENT_DATE=$(date +%Y-%m-%d)
    VERSION="0.1.0"

    # Derive citation name parts (best-effort split on last space)
    AUTHOR_LAST="${AUTHOR##* }"
    AUTHOR_FIRST="${AUTHOR% *}"
    FIRST_INITIAL="${AUTHOR_FIRST:0:1}."
    if [ "$AUTHOR_LAST" = "$AUTHOR_FIRST" ]; then
        AUTHOR_FIRST="$AUTHOR"
        AUTHOR_LAST=""
        FIRST_INITIAL=""
    fi

    echo ""
    echo "── Summary ──────────────────────────────────────"
    echo "  Project:     $PROJECT_NAME"
    echo "  Repo:        $REPO"
    echo "  Owner:       $OWNER"
    echo "  Author:      $AUTHOR <$AUTHOR_EMAIL>"
    [ -n "$AUTHOR_ORG" ] && echo "  Organization: $AUTHOR_ORG"
    echo "  Forge:       $FORGE"
    echo "  Year:        $CURRENT_YEAR"
    echo "────────────────────────────────────────────────"
    echo ""
    read -rp "Proceed? [Y/n] " CONFIRM
    [[ "${CONFIRM:-Y}" =~ ^[Nn] ]] && echo "Aborted." && exit 0

    echo ""
    echo "Replacing placeholders..."

    # Brace tokens as variables (hex avoids just interpolation)
    LB=$(printf '\x7b\x7b')
    RB=$(printf '\x7d\x7d')

    # Build the sed expression list
    # Note: using | as delimiter since URLs contain /
    SED_ARGS=(
        -e "s|${LB}PROJECT_NAME${RB}|${PROJECT_NAME}|g"
        -e "s|${LB}PROJECT_DESCRIPTION${RB}|${PROJECT_DESCRIPTION}|g"
        -e "s|${LB}PROJECT${RB}|${PROJECT_UPPER}|g"
        -e "s|${LB}project${RB}|${PROJECT_LOWER}|g"
        -e "s|${LB}REPO${RB}|${REPO}|g"
        -e "s|${LB}OWNER${RB}|${OWNER}|g"
        -e "s|${LB}AUTHOR${RB}|${AUTHOR}|g"
        -e "s|${LB}AUTHOR_EMAIL${RB}|${AUTHOR_EMAIL}|g"
        -e "s|${LB}AUTHOR_ORG${RB}|${AUTHOR_ORG}|g"
        -e "s|${LB}AUTHOR_LAST${RB}|${AUTHOR_LAST}|g"
        -e "s|${LB}AUTHOR_FIRST${RB}|${AUTHOR_FIRST}|g"
        -e "s|${LB}AUTHOR_INITIALS${RB}|${FIRST_INITIAL}|g"
        -e "s|${LB}FORGE${RB}|${FORGE}|g"
        -e "s|${LB}CURRENT_YEAR${RB}|${CURRENT_YEAR}|g"
        -e "s|${LB}CURRENT_DATE${RB}|${CURRENT_DATE}|g"
        -e "s|${LB}DATE${RB}|${CURRENT_DATE}|g"
        -e "s|${LB}SECURITY_EMAIL${RB}|${SECURITY_EMAIL}|g"
        -e "s|${LB}CONDUCT_EMAIL${RB}|${CONDUCT_EMAIL}|g"
        -e "s|${LB}LICENSE${RB}|MPL-2.0|g"
        -e "s|${LB}CONDUCT_TEAM${RB}|Code of Conduct Committee|g"
        -e "s|${LB}RESPONSE_TIME${RB}|48 hours|g"
        -e "s|${LB}MAIN_BRANCH${RB}|main|g"
        -e "s|${LB}PROJECT_PURPOSE${RB}|${PROJECT_DESCRIPTION}|g"
        -e "s|${LB}PROJECT_ROLE${RB}|${PROJECT_TYPE}|g"
        -e "s|${LB}PROJECT_TYPE${RB}|${PROJECT_TYPE}|g"
        -e "s|${LB}WEBSITE${RB}|${WEBSITE}|g"
        -e "s|${LB}SERVICE_NAME${RB}|${SERVICE_NAME}|g"
        -e "s|${LB}PORT${RB}|${PORT}|g"
        -e "s|${LB}REGISTRY${RB}|${REGISTRY}|g"
        -e "s|${LB}IMAGE${RB}|${REGISTRY}/${SERVICE_NAME}|g"
        -e "s|${LB}VERSION${RB}|${VERSION}|g"
        -e "s|${LB}EMAIL${RB}|${AUTHOR_EMAIL}|g"
    )
    [ -n "$AUTHOR_EMAIL_ALT" ] && SED_ARGS+=(-e "s|${LB}AUTHOR_EMAIL_ALT${RB}|${AUTHOR_EMAIL_ALT}|g")

    # Replace in all text files (skip .git, LICENSE text, and binaries)
    find . -type f \
        -not -path './.git/*' \
        -not -name 'MPL-2.0.txt' \
        -not -name '*.png' -not -name '*.jpg' -not -name '*.gif' \
        -not -name '*.woff' -not -name '*.woff2' \
        | while read -r file; do
        if file --brief "$file" | grep -qi 'text\|ascii\|utf'; then
            sed -i "${SED_ARGS[@]}" "$file"
        fi
    done

    # Also replace [YOUR-REPO-NAME] and [YOUR-NAME/ORG] in AI manifest
    sed -i "s|\[YOUR-REPO-NAME\]|${PROJECT_NAME}|g" 0-AI-MANIFEST.a2ml 2>/dev/null || true
    sed -i "s|\[YOUR-NAME/ORG\]|${OWNER}|g" 0-AI-MANIFEST.a2ml 2>/dev/null || true

    echo ""
    echo "── Validation ───────────────────────────────────"

    # Check for remaining placeholders
    PATTERN="${LB}[A-Z_]*${RB}"
    REMAINING=$(grep -rl "$PATTERN" . --include='*.md' --include='*.adoc' --include='*.yml' --include='*.yaml' --include='*.a2ml' --include='*.toml' --include='*.scm' --include='*.ncl' --include='*.guix' --include='*.json' --include='*.sh' 2>/dev/null | grep -v '.git/' | grep -v '.machine_readable/ai/PLACEHOLDERS.adoc' || true)
    if [ -n "$REMAINING" ]; then
        echo "WARNING: Remaining placeholders in:"
        echo "$REMAINING" | sed 's/^/  /'
        echo ""
        echo "Run: grep -rn '$LB' . --include='*.md' to inspect"
    else
        echo "All placeholders replaced successfully!"
    fi

    echo ""
    echo "Done! Next steps:"
    echo "  1. Review changes: git diff"
    echo "  2. Remove template cruft: rm .machine_readable/ai/PLACEHOLDERS.adoc"
    echo "  3. Customize README.adoc for your project"
    echo "  4. Commit: git add -A && git commit -m 'feat: initialize from RSR template'"
    echo "  5. Push: git remote add origin git@github.com:$OWNER/$REPO.git && git push -u origin main"

#!/usr/bin/env bash
# SPDX-License-Identifier: PMPL-1.0-or-later
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
#
# ECHIDNA — Non-interactive upstream corpus provisioning.
#
# Clones the upstream mirror of every theorem-prover corpus the extractors
# under scripts/extract_*.jl expect at external_corpora/<name>/.  Each
# clone uses --depth=1 to keep the bandwidth bill finite (~4-8 GB total
# when all sources are selected).
#
# Usage
# -----
#   scripts/provision_corpora.sh [NAME ...]     # provision the named sources
#   scripts/provision_corpora.sh --all          # provision every source
#   scripts/provision_corpora.sh --list         # print the source catalogue
#   scripts/provision_corpora.sh --status       # show which sources are on disk
#
# Selection names match the external_corpora/<name>/ directory each extractor
# expects.  Unknown names exit non-zero so typos fail loudly in CI.
#
# Behaviour
#   * If external_corpora/<name>/ already exists the source is skipped
#     (idempotent; safe to re-run).  Pass --force to re-clone into a
#     fresh directory.
#   * Network failures are retried once; a failure after that is logged
#     and the script continues to the next source (so a single offline
#     mirror doesn't abort a 40-source provisioning).
#   * Designed to be callable from a Justfile recipe or a nightly CI
#     workflow.  No interactive prompts, ever.

set -euo pipefail

ECHIDNA_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
CORPORA_DIR="${ECHIDNA_CORPORA_DIR:-$ECHIDNA_ROOT/external_corpora}"
FORCE=0

# ------------------------------------------------------------------
# Upstream catalogue
#
# Each entry: "<name>|<kind>|<url>|<subpath?>"
#   kind = git   — `git clone --depth=1 <url> <CORPORA_DIR>/<name>`
#   kind = tar   — `curl <url> | tar xz` into <CORPORA_DIR>/<name>
#   kind = skip  — metadata only (proprietary / form-gated / non-public)
#
# Adding a source:
#   1. Add a row here with the real upstream URL.
#   2. Update scripts/extract_<name>.jl to read from external_corpora/<name>.
# ------------------------------------------------------------------
CATALOGUE=(
    # Interactive proof assistants
    "abella|git|https://github.com/abella-prover/abella"
    "agda-stdlib|git|https://github.com/agda/agda-stdlib"
    "agda-cubical|git|https://github.com/agda/cubical"
    "agda-unimath|git|https://github.com/UniMath/agda-unimath"
    "arend|git|https://github.com/JetBrains/Arend"
    "CoqGym|git|https://github.com/princeton-vl/CoqGym"
    "mathcomp|git|https://github.com/math-comp/math-comp"
    "mathcomp-analysis|git|https://github.com/math-comp/analysis"
    "mathcomp-finmap|git|https://github.com/math-comp/finmap"
    "mathcomp-algebra-tactics|git|https://github.com/math-comp/algebra-tactics"
    "mathlib3|git|https://github.com/leanprover-community/mathlib"
    "mathlib4|git|https://github.com/leanprover-community/mathlib4"
    "hol4|git|https://github.com/HOL-Theorem-Prover/HOL"
    "hol_light|git|https://github.com/jrh13/hol-light"
    "fstar|git|https://github.com/FStarLang/FStar"
    "idris2|git|https://github.com/idris-lang/Idris2"
    "matita|git|https://github.com/rocq-prover/matita"
    "mizar|git|https://github.com/MizarProject/mml"
    "metamath|git|https://github.com/metamath/set.mm"
    "opentheory|git|https://github.com/gilith/opentheory"
    "pvs|git|https://github.com/nasa/pvslib"
    "afp|git|https://foss.heptapod.net/isa-afp/afp-devel.git"

    # ACL2 family
    "acl2|git|https://github.com/acl2/acl2"
    "acl2s|git|https://github.com/acl2s/acl2s"

    # Auto-active verifiers
    "dafny|git|https://github.com/dafny-lang/dafny"
    "why3|git|https://gitlab.inria.fr/why3/why3"
    "boogie|git|https://github.com/boogie-org/boogie"
    "cameleer|git|https://github.com/ocaml-gospel/cameleer"
    "framac|git|https://git.frama-c.com/pub/frama-c"
    "viper|git|https://github.com/viperproject/silver"
    "key|git|https://github.com/KeYProject/key"

    # Model checkers / CI verifiers
    "cbmc|git|https://github.com/diffblue/cbmc"
    "seahorn|git|https://github.com/seahorn/seahorn"
    "spin|git|https://github.com/nimble-code/Spin"
    "prism|git|https://github.com/prismmodelchecker/prism-examples"
    "nusmv|skip|https://nusmv.fbk.eu/distrib/" # distro ships examples
    "uppaal|skip|https://uppaal.org/documentation/" # commercial; examples gated
    "tlaplus_examples|git|https://github.com/tlaplus/Examples"

    # SAT / SMT / FO-ATP benchmarks
    "abc|git|https://github.com/berkeley-abc/abc"
    "dreal4|git|https://github.com/dreal/dreal4"
    "smtlib|skip|https://smtlib.cs.uiowa.edu/benchmarks.shtml" # tarball index
    "sat_benchmarks|skip|https://www.satcompetition.org/" # annual tarballs
    "tptp|skip|https://www.tptp.org/" # form-free tarball

    # Security protocol verifiers
    "tamarin|git|https://github.com/tamarin-prover/tamarin-prover"
    "proverif|git|https://gitlab.inria.fr/bblanche/proverif"

    # Constraint / optimisation
    "alloy|git|https://github.com/AlloyTools/models"
    "minizinc|git|https://github.com/MiniZinc/minizinc-benchmarks"

    # Logic frameworks / misc
    "dedukti|git|https://github.com/Deducteam/Libraries"
    "elpi-lang|git|https://github.com/LPCIC/elpi"
    "naproche|git|https://github.com/naproche/naproche"
    "mercury-lang|git|https://github.com/Mercury-Language/mercury"
    "nunchaku|git|https://github.com/nunchaku-inria/nunchaku"
    "athena|git|https://github.com/AthenaFoundation/athena"
)

# ------------------------------------------------------------------

usage() {
    sed -n '4,25p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'
}

list_catalogue() {
    printf "%-28s %-5s %s\n" "NAME" "KIND" "URL"
    printf "%-28s %-5s %s\n" "----" "----" "---"
    for entry in "${CATALOGUE[@]}"; do
        IFS='|' read -r name kind url _ <<<"$entry"
        printf "%-28s %-5s %s\n" "$name" "$kind" "$url"
    done
}

show_status() {
    local present=0
    local missing=0
    printf "%-28s %-9s %s\n" "NAME" "STATUS" "SIZE"
    printf "%-28s %-9s %s\n" "----" "------" "----"
    for entry in "${CATALOGUE[@]}"; do
        IFS='|' read -r name kind _ _ <<<"$entry"
        local path="$CORPORA_DIR/$name"
        if [[ -d "$path" ]]; then
            local size
            size="$(du -sh "$path" 2>/dev/null | awk '{print $1}')"
            printf "%-28s %-9s %s\n" "$name" "present" "$size"
            present=$((present + 1))
        elif [[ "$kind" == "skip" ]]; then
            printf "%-28s %-9s %s\n" "$name" "manual" "(gated upstream)"
        else
            printf "%-28s %-9s %s\n" "$name" "missing" "-"
            missing=$((missing + 1))
        fi
    done
    echo
    echo "Summary: $present present, $missing missing, $(( ${#CATALOGUE[@]} - present - missing )) manual."
    echo "Root:    $CORPORA_DIR"
}

find_entry() {
    local want="$1"
    for entry in "${CATALOGUE[@]}"; do
        IFS='|' read -r name _ _ _ <<<"$entry"
        if [[ "$name" == "$want" ]]; then
            echo "$entry"
            return 0
        fi
    done
    return 1
}

provision_one() {
    local entry="$1"
    IFS='|' read -r name kind url _ <<<"$entry"
    local dest="$CORPORA_DIR/$name"

    if [[ "$kind" == "skip" ]]; then
        echo "  [skip]   $name: provision manually from $url"
        return 0
    fi

    if [[ -d "$dest" && $FORCE -eq 0 ]]; then
        echo "  [ok]     $name: already present at $dest"
        return 0
    fi

    if [[ -d "$dest" && $FORCE -eq 1 ]]; then
        echo "  [force]  removing $dest"
        rm -rf "$dest"
    fi

    mkdir -p "$CORPORA_DIR"

    case "$kind" in
        git)
            echo "  [clone]  $name  <-  $url"
            if ! git clone --depth=1 --filter=blob:none "$url" "$dest" 2>&1 | tail -n 3; then
                echo "  [retry]  $name"
                sleep 2
                if ! git clone --depth=1 "$url" "$dest" 2>&1 | tail -n 3; then
                    echo "  [FAIL]   $name: clone failed; continuing"
                    return 1
                fi
            fi
            ;;
        tar)
            echo "  [tar]    $name  <-  $url"
            mkdir -p "$dest"
            if ! curl -fsSL "$url" | tar xz -C "$dest" --strip-components=1; then
                echo "  [FAIL]   $name: tarball extraction failed; continuing"
                return 1
            fi
            ;;
        *)
            echo "  [WARN]   unknown kind '$kind' for $name"
            return 1
            ;;
    esac
    echo "  [done]   $name"
}

provision_all() {
    local ok=0 fail=0 skip=0
    for entry in "${CATALOGUE[@]}"; do
        IFS='|' read -r _ kind _ _ <<<"$entry"
        if [[ "$kind" == "skip" ]]; then
            skip=$((skip + 1))
            provision_one "$entry" || true
            continue
        fi
        if provision_one "$entry"; then
            ok=$((ok + 1))
        else
            fail=$((fail + 1))
        fi
    done
    echo
    echo "Provisioning complete: $ok ok, $fail failed, $skip manual."
}

# ------------------------------------------------------------------

case "${1:-}" in
    ""|--help|-h)
        usage
        exit 0
        ;;
    --list)
        list_catalogue
        exit 0
        ;;
    --status)
        show_status
        exit 0
        ;;
    --all)
        shift
        [[ "${1:-}" == "--force" ]] && { FORCE=1; shift; }
        provision_all
        ;;
    --force)
        FORCE=1
        shift
        if [[ "${1:-}" == "--all" ]]; then
            shift
            provision_all
        else
            for name in "$@"; do
                entry="$(find_entry "$name")" || { echo "unknown source: $name (run --list)"; exit 2; }
                provision_one "$entry" || true
            done
        fi
        ;;
    *)
        for name in "$@"; do
            entry="$(find_entry "$name")" || { echo "unknown source: $name (run --list)"; exit 2; }
            provision_one "$entry" || true
        done
        ;;
esac

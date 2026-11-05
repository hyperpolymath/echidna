#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
#
# hotspot-goldens.sh — regenerate the hotspot-split goldens and diff them
# against the committed copies in tests/golden/hotspot/.
#
# The goldens pin the externally visible surface of the three files that the
# W0 hotspot split moves apart (src/rust/main.rs, src/rust/server.rs and the
# Justfile), so a "pure move" can be shown to be one:
#
#   cli-help.txt          `echidna --help` and `echidna <sub> [<sub>...] --help`
#                         for every subcommand, discovered recursively from
#                         the "Commands:" section of each help page.
#   routes.txt            METHOD PATH for every `.route(` registration in the
#                         HTTP server module (src/rust/server.rs or
#                         src/rust/server/**.rs), sorted.
#   just-list.txt         `just --list`
#   just-list-unsorted.txt `just --list --unsorted` (what bare `just` prints)
#
# Usage (from the repository root):
#   scripts/ci/hotspot-goldens.sh            check: regenerate into a temp dir, diff, exit 1 on drift
#   scripts/ci/hotspot-goldens.sh --update   rewrite tests/golden/hotspot/ from the current tree
#
# The CLI goldens need the echidna binary. By default the script builds it
# with `cargo build --locked --bin echidna` (honouring CARGO_TARGET_DIR) so a
# stale binary can never pass. Set ECHIDNA_BIN=/path/to/echidna to skip the
# build and use that binary instead.
#
# Exit codes: 0 no drift (or updated), 1 drift, 2 usage or environment error.
set -euo pipefail

mode=check
case "${1:-}" in
  "") ;;
  --update) mode=update ;;
  -h|--help) sed -n '2,32p' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
  *) echo "hotspot-goldens: unknown argument: $1" >&2; exit 2 ;;
esac

[ -f Cargo.toml ] && [ -f Justfile ] || { echo "hotspot-goldens: run from the repository root" >&2; exit 2; }
command -v just >/dev/null || { echo "hotspot-goldens: just not found (cargo install just --locked)" >&2; exit 2; }

golden_dir="tests/golden/hotspot"

# Deterministic environment for every generator.
export LC_ALL=C NO_COLOR=1 CLICOLOR=0 COLUMNS=100 TERM=dumb

if [ -n "${ECHIDNA_BIN:-}" ]; then
  bin="$ECHIDNA_BIN"
else
  cargo build --locked --quiet --bin echidna
  bin="${CARGO_TARGET_DIR:-target}/debug/echidna"
fi
[ -x "$bin" ] || { echo "hotspot-goldens: echidna binary not found at $bin" >&2; exit 2; }

# subcommands HELP_TEXT -> names listed under "Commands:", minus clap's `help`.
subcommands() {
  awk '
    /^Commands:/ { in_cmds = 1; next }
    in_cmds && /^[^ ]/ { in_cmds = 0 }
    in_cmds && /^  [a-z0-9]/ { print $1 }
  ' <<<"$1" | grep -vx help || true
}

# walk PATH... -> print the help page for `echidna PATH... --help`, then recurse.
# A help page that exits non-zero is recorded with its exit status, and a
# panic message is normalised (thread id and registry path removed) so the
# golden pins the failure itself rather than the machine it ran on.
walk() {
  local text sub rc=0
  text="$(RUST_BACKTRACE=0 "$bin" "$@" --help 2>&1)" || rc=$?
  if [ "$rc" -ne 0 ]; then
    text="$(sed -E \
      -e "s/^thread '([^']*)' \([0-9]+\) panicked at .*\/([^/]+:[0-9]+:[0-9]+):\$/thread '\1' panicked at \2:/" \
      -e '/^note: run with `RUST_BACKTRACE=1`/d' <<<"$text")"
    text="$text"$'\n'"[exit status $rc]"
  fi
  printf '==> echidna%s --help <==\n%s\n\n' "${*:+ $*}" "$text"
  while IFS= read -r sub; do
    [ -n "$sub" ] && walk "$@" "$sub"
  done < <(subcommands "$text")
}

gen_cli_help() { walk; }

# Every `.route("PATH", method(handler)[.method(handler)...])` in the server
# module, as one "METHOD PATH" line per method, sorted. Line comments are
# stripped first so commented-out routes do not count.
gen_routes() {
  local files
  files="$( (find src/rust/server.rs src/rust/server -name '*.rs' 2>/dev/null || true) | LC_ALL=C sort)"
  [ -n "$files" ] || { echo "hotspot-goldens: no server module found" >&2; exit 2; }
  # shellcheck disable=SC2086
  sed 's://.*$::' $files | tr '\n' ' ' \
    | grep -oE '\.route\([[:space:]]*"[^"]*"[[:space:]]*,[[:space:]]*[a-z_]+\([^()]*\)([[:space:]]*\.[a-z_]+\([^()]*\))*' \
    | while IFS= read -r reg; do
        path="$(sed -E 's/^\.route\([[:space:]]*"([^"]*)".*/\1/' <<<"$reg")"
        sed -E 's/^\.route\([[:space:]]*"[^"]*"[[:space:]]*,[[:space:]]*//' <<<"$reg" \
          | grep -oE '(^|\.)[a-z_]+\(' | tr -d '.(' \
          | while IFS= read -r method; do
              printf '%s %s\n' "$(tr '[:lower:]' '[:upper:]' <<<"$method")" "$path"
            done
      done | LC_ALL=C sort
}

gen_just_list() { just --list; }
gen_just_list_unsorted() { just --list --unsorted; }

generate_into() {
  local out="$1"
  mkdir -p "$out"
  gen_cli_help >"$out/cli-help.txt"
  gen_routes >"$out/routes.txt"
  gen_just_list >"$out/just-list.txt"
  gen_just_list_unsorted >"$out/just-list-unsorted.txt"
}

if [ "$mode" = update ]; then
  generate_into "$golden_dir"
  echo "hotspot-goldens: updated $golden_dir"
  exit 0
fi

tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
generate_into "$tmp"

rc=0
for f in cli-help.txt routes.txt just-list.txt just-list-unsorted.txt; do
  if [ ! -f "$golden_dir/$f" ]; then
    echo "hotspot-goldens: FAIL $golden_dir/$f is missing" >&2
    rc=1
  elif ! diff -u "$golden_dir/$f" "$tmp/$f"; then
    echo "hotspot-goldens: FAIL $f drifted from $golden_dir/$f" >&2
    rc=1
  else
    echo "hotspot-goldens: ok $f"
  fi
done
exit "$rc"

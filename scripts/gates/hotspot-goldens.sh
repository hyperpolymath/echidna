#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
#
# Goldens for NEW:hotspot-split (W0 gate check 5). The split of main.rs into
# cli/*, server.rs into server/* and the Justfile into just/*.just is a pure
# move, so these three surfaces must not change:
#
#   help/echidna[-<sub>[-<subsub>]].txt   `echidna [<sub> ...] --help`, every
#                                         subcommand, recursively (depth 3)
#   routes.txt                            every `.route(...)` line under
#                                         src/rust/, whitespace-trimmed, sorted
#   just-list.txt                         `just --list`
#
# Usage:
#   hotspot-goldens.sh capture [--dir DIR] [--bin PATH]   write the goldens
#   hotspot-goldens.sh check   [--dir DIR] [--bin PATH]   diff against them
#
# Capture on the pre-split tree (origin/main before the split lands), commit
# the result, and never re-capture to silence a diff after the split.
# DIR defaults to tests/golden/hotspot. Without --bin the echidna binary is
# built with `cargo build --locked --bin echidna` into $CARGO_TARGET_DIR
# (default target/). Run from the repository root.
#
# Exit codes: 0 no diff (or captured), 1 diff or missing golden, 2 cannot run.

set -euo pipefail
export LC_ALL=C

mode="${1:-}"
[ $# -gt 0 ] && shift
dir="tests/golden/hotspot"
bin=""
while [ $# -gt 0 ]; do
  case "$1" in
    --dir) dir="$2"; shift 2 ;;
    --bin) bin="$2"; shift 2 ;;
    -h|--help) sed -n '3,24p' "$0"; exit 0 ;;
    *) echo "unknown argument: $1" >&2; exit 2 ;;
  esac
done
case "$mode" in capture|check) ;; *) sed -n '3,24p' "$0" >&2; exit 2 ;; esac

for tool in just rg; do
  command -v "$tool" >/dev/null 2>&1 || { echo "cannot run: $tool is not installed" >&2; exit 2; }
done

if [ -z "$bin" ]; then
  cargo build --locked --quiet --bin echidna >&2 || { echo "cannot run: cargo build failed" >&2; exit 2; }
  bin="${CARGO_TARGET_DIR:-target}/debug/echidna"
fi
[ -x "$bin" ] || { echo "cannot run: $bin is not executable" >&2; exit 2; }

out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
mkdir -p "$out/help"

# Subcommand names from a clap help text: the indented first words under
# "Commands:", up to the next blank line. `help` is clap's own and skipped.
subcommands() {
  awk '/^Commands:/{on=1; next} on && /^$/{on=0} on && /^  [a-z0-9]/{print $1}' | grep -vx help || true
}

# help_tree <depth> <args...>
help_tree() {
  local depth="$1" name sub text
  shift
  name=$(printf '%s' "echidna${*:+ $*}" | tr ' ' '-')
  local rc=0
  text=$(NO_COLOR=1 COLUMNS=100 RUST_BACKTRACE=0 "$bin" "$@" --help 2>&1) || rc=$?
  if [ "$rc" -ne 0 ]; then
    # A failing --help is behaviour too, and a pure move must keep it. Record
    # the exit status and the message, without the thread id and the source
    # path of the panic, which differ between machines.
    text=$(printf '[exit %d]\n%s' "$rc" "$text" \
      | sed -E "s/^thread '([^']*)' \\([0-9]+\\) panicked at .*/thread '\\1' panicked:/")
    echo "note: '$*${*:+ }--help' exits $rc; recorded as behaviour" >&2
  fi
  printf '%s\n' "$text" > "$out/help/$name.txt"
  [ "$depth" -ge 3 ] && return 0
  for sub in $(printf '%s\n' "$text" | subcommands); do
    help_tree $((depth + 1)) "$@" "$sub"
  done
}
help_tree 0

rg --no-filename --no-line-number --glob '*.rs' '^\s*\.route\(' src/rust \
  | sed -E 's/^[[:space:]]+//; s/[[:space:]]+$//' | sort > "$out/routes.txt" || true
[ -s "$out/routes.txt" ] || { echo "cannot run: no .route( lines found under src/rust" >&2; exit 2; }

just --list > "$out/just-list.txt" 2>&1 || { echo "cannot run: just --list failed" >&2; exit 2; }

if [ "$mode" = capture ]; then
  mkdir -p "$dir"
  rm -rf "$dir/help"
  cp -R "$out/." "$dir/"
  echo "captured $(find "$dir" -type f | wc -l) golden files into $dir"
  exit 0
fi

[ -d "$dir" ] || { echo "golden directory $dir is missing; capture it on the pre-split tree" >&2; exit 1; }
if diff -ruN "$dir" "$out"; then
  echo "hotspot goldens: no diff ($(find "$out" -type f | wc -l) files)"
  exit 0
fi
exit 1

#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
#
# The FFI tag of each coprocessor kind is written twice: as an explicit
# discriminant of the Rust `CoprocessorKind` (src/rust/coprocessor/types.rs)
# and as a clause of `coprocessorKindToU8` in src/abi/Coprocessor/Foreign.idr.
# Neither compiler sees the other file, so this compares the two lists as
# "Name=tag" pairs. It fails if either list is empty, if a Rust variant has no
# explicit discriminant, or if the pairs differ.
set -euo pipefail
root=${1:-.}
rs="$root/src/rust/coprocessor/types.rs"
idr="$root/src/abi/Coprocessor/Foreign.idr"

body=$(awk '/^pub enum CoprocessorKind \{/{f=1;next} f&&/^\}/{exit} f' "$rs")
# Every variant line must be exactly `Name = <decimal>` (comma optional). Anything else (no
# discriminant, a hex or underscored literal, an expression) is refused rather
# than half-parsed: a regex that stopped at the first digits would read
# `Math = 0x10` as Math=0 and pass a real mismatch.
variants=$({ printf '%s\n' "$body" | grep -E '^[[:space:]]+[A-Z]' || true; })
odd=$({ printf '%s\n' "$variants" | grep -vE '^[[:space:]]+[A-Z][A-Za-z0-9]*[[:space:]]*=[[:space:]]*[0-9]+,?[[:space:]]*$' || true; })
if [[ -n "$odd" ]]; then
  echo "::error file=$rs::CoprocessorKind variants must read 'Name = <decimal>' (comma optional); these do not:"
  printf '%s\n' "$odd"
  exit 1
fi
rust=$(printf '%s\n' "$variants" | sed -E 's/,?[[:space:]]*$//' | tr -d ' ' | sort)
clauses=$({ grep -E '^coprocessorKindToU8[[:space:]]+[A-Z]' "$idr" || true; })
odd=$({ printf '%s\n' "$clauses" | grep -vE '^coprocessorKindToU8[[:space:]]+[A-Z][A-Za-z0-9]*[[:space:]]*=[[:space:]]*[0-9]+[[:space:]]*$' || true; })
if [[ -n "$clauses" && -n "$odd" ]]; then
  echo "::error file=$idr::coprocessorKindToU8 clauses must read 'coprocessorKindToU8 Name = <decimal>'; these do not:"
  printf '%s\n' "$odd"
  exit 1
fi
idris=$(printf '%s\n' "$clauses" | sed -E 's/^coprocessorKindToU8[[:space:]]+//' | tr -d ' ' | sed '/^$/d' | sort)

if [[ -z "$rust" ]] || [[ -z "$idris" ]]; then
  echo "::error::could not read the tags (rust: ${rust:+found}${rust:-none}, idris: ${idris:+found}${idris:-none})"
  exit 1
fi
if [[ "$rust" != "$idris" ]]; then
  echo "::error file=$idr::coprocessorKindToU8 disagrees with the Rust CoprocessorKind discriminants"
  diff <(printf '%s\n' "$rust") <(printf '%s\n' "$idris") | sed 's/^</rust /;s/^>/idris/' || true
  exit 1
fi
echo "coprocessor tags agree: $(printf '%s\n' "$rust" | wc -l) kinds"

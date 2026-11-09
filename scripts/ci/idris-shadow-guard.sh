#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Fail when Idris2 reports that a lowercase name in a type signature was
# implicitly bound over a definition from this package.
#
# Idris2 binds unknown-looking lowercase names in a signature as implicit
# arguments. When the name is also a top-level definition, the statement
# quietly changes meaning: `Not (schemaId = 0)` becomes "every Nat is
# non-zero". Idris2 only warns. This guard turns the warning into a failure
# for names that shadow a module of the package (library names such as
# Data.Nat.minimum used as an index variable stay allowed).
#
# Usage: idris-shadow-guard.sh <ipkg> <build-log>
set -euo pipefail
ipkg=${1:?usage: idris-shadow-guard.sh <ipkg> <build-log>}
log=${2:?usage: idris-shadow-guard.sh <ipkg> <build-log>}
[ -f "$ipkg" ] || { echo "idris-shadow-guard: no ipkg at $ipkg" >&2; exit 2; }
[ -f "$log" ] || { echo "idris-shadow-guard: no build log at $log" >&2; exit 2; }

# Module names listed in the ipkg (`modules = A, B.C, ...`, across lines).
modules=$(awk '
  /^[[:space:]]*modules[[:space:]]*=/ { on = 1; sub(/^[^=]*=/, "") }
  on && /^[[:space:]]*[a-z_]+[[:space:]]*=/ && !/modules/ { on = 0 }
  on { gsub(/--.*/, ""); gsub(/[,[:space:]]+/, "\n"); printf "%s\n", $0 }
' "$ipkg" | grep -E '^[A-Z][A-Za-z0-9_.]*$' || true)
[ -n "$modules" ] || { echo "idris-shadow-guard: no modules parsed from $ipkg" >&2; exit 2; }

found=0
while IFS= read -r line; do
  # "  name is shadowing Some.Module.name"
  target=$(printf '%s\n' "$line" | sed -nE 's/^[[:space:]]*[^[:space:]]+ is shadowing ([^[:space:]]+)[[:space:]]*$/\1/p')
  [ -n "$target" ] || continue
  ns=${target%.*}
  if printf '%s\n' "$modules" | grep -qxF -- "$ns"; then
    echo "::error::implicit binding shadows package definition: ${line#"${line%%[![:space:]]*}"}"
    found=1
  fi
done < "$log"

if [ "$found" -ne 0 ]; then
  echo "A signature mentions a package definition by its bare lowercase name, so"
  echo "Idris2 bound it as a fresh variable. Qualify it (Module.name)."
  exit 1
fi
echo "idris-shadow-guard: no package definition shadowed ($(printf '%s\n' "$modules" | wc -l) modules)"

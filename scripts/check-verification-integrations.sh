#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
set -euo pipefail

cd "$(dirname "$0")/.."
enum_source='crates/echidna-core/src/prover_kind.rs'
registry='.machine_readable/provers.a2ml'
ledger='.machine_readable/verification-integrations.a2ml'

mapfile -t enum_names < <(awk '
  /^pub enum ProverKind \{/ { inside = 1; next }
  inside && /^}/ { exit }
  inside && /^    [[:alpha:]][[:alnum:]_]*,/ {
    name = $1; sub(/,$/, "", name); print name
  }
' "$enum_source" | LC_ALL=C sort)
mapfile -t registry_names < <(sed -n 's/^\[prover\.\([[:alnum:]_]*\)\]$/\1/p' "$registry" | LC_ALL=C sort)

if ((${#enum_names[@]} != 141)); then
  printf 'Expected 141 ProverKind declarations, found %s\n' "${#enum_names[@]}" >&2
  exit 1
fi
if ! diff -u <(printf '%s\n' "${enum_names[@]}") <(printf '%s\n' "${registry_names[@]}"); then
  printf 'Registry differs from ProverKind declarations\n' >&2
  exit 1
fi
if ! grep -Eq '^count[[:space:]]*=[[:space:]]*141$' "$registry" ||
   ! grep -Eq '^source[[:space:]]*=[[:space:]]*"crates/echidna-core/src/prover_kind.rs::ProverKind"$' "$registry"; then
  printf 'Registry count or source metadata is stale\n' >&2
  exit 1
fi
if ! grep -Fxq 'schema = "verification-integrations/1"' "$ledger" ||
   ! grep -Fxq 'enum_default = "declared_unverified"' "$ledger"; then
  printf 'Ledger schema or default status is stale\n' >&2
  exit 1
fi
if ! grep -Fxq "enum_source = \"$enum_source\"" "$ledger"; then
  printf 'Ledger enum_source is stale\n' >&2
  exit 1
fi
if ! grep -Fxq "enum_registry = \"$registry\"" "$ledger"; then
  printf 'Ledger enum_registry is stale\n' >&2
  exit 1
fi

awk '
  /^[[:space:]]*$/ || /^#/ { next }
  /^\[metadata\]$/ || /^\[tool\.[[:alnum:]_]+\]$/ { next }
  /^[a-z_]+ = "[^"]*"$/ { next }
  /^local_paths = \["[^"]+"(, "[^"]+")*\]$/ { next }
  { printf "Unsupported or malformed ledger line %d: %s\n", NR, $0 > "/dev/stderr"; exit 1 }
' "$ledger"

declare -A statuses kinds parents roles evidence
while IFS='|' read -r tool status kind parent role has_paths; do
  [[ -n "$tool" ]] || continue
  if [[ -v statuses[$tool] ]]; then
    printf 'Duplicate tool entry: %s\n' "$tool" >&2; exit 1
  fi
  case "$status" in
    backend_declared|via_parent|partial_non_backend|not_integrated|not_a_prover) ;;
    *) printf 'Invalid status for %s: %s\n' "$tool" "$status" >&2; exit 1 ;;
  esac
  statuses[$tool]="$status"
  kinds[$tool]="$kind"
  parents[$tool]="$parent"
  roles[$tool]="$role"
  evidence[$tool]="$has_paths"
done < <(awk '
  # Write the current tool, status, kind, parent, role and path-presence flag
  # to stdout as one pipe-delimited line; emit nothing when tool is empty.
  function emit() { if (tool != "") print tool "|" status "|" kind "|" parent "|" role "|" has_paths }
  /^\[tool\.[[:alnum:]_]+\]$/ {
    emit(); tool = $0; sub(/^\[tool\./, "", tool); sub(/\]$/, "", tool)
    status = kind = parent = role = has_paths = ""; next
  }
  tool != "" && /^status = / { status = $3; gsub(/"/, "", status) }
  tool != "" && /^prover_kind = / { kind = $3; gsub(/"/, "", kind) }
  tool != "" && /^parent_tool = / { parent = $3; gsub(/"/, "", parent) }
  tool != "" && /^role = / { role = $0; sub(/^role = "/, "", role); sub(/"$/, "", role) }
  tool != "" && /^local_paths = / { has_paths = "yes" }
  END { emit() }
' "$ledger")

if ((${#statuses[@]} != 12)); then
  printf 'Expected 12 assessed tool roles, found %s\n' "${#statuses[@]}" >&2
  exit 1
fi
for tool in "${!statuses[@]}"; do
  if [[ -z "${roles[$tool]}" ]]; then
    printf 'Missing role for %s\n' "$tool" >&2; exit 1
  fi
  if [[ "${statuses[$tool]}" == backend_declared ]]; then
    if [[ -z "${kinds[$tool]}" ]] || ! printf '%s\n' "${enum_names[@]}" | grep -Fxq "${kinds[$tool]}"; then
      printf 'Missing declared backend variant for %s\n' "$tool" >&2; exit 1
    fi
    if [[ "${evidence[$tool]}" != yes ]]; then
      printf 'Missing local backend evidence for %s\n' "$tool" >&2; exit 1
    fi
  elif [[ -n "${kinds[$tool]}" ]]; then
    printf 'Non-backend %s declares a prover variant\n' "$tool" >&2; exit 1
  fi
  if [[ "${statuses[$tool]}" == not_integrated || "${statuses[$tool]}" == not_a_prover ]] &&
     printf '%s\n' "${enum_names[@]}" | grep -Fxq "$tool"; then
    printf '%s is declared in ProverKind but marked %s\n' "$tool" "${statuses[$tool]}" >&2; exit 1
  fi
  if [[ "${statuses[$tool]}" == via_parent ]]; then
    if [[ -z "${parents[$tool]}" || ! -v statuses[${parents[$tool]}] ]]; then
      printf 'Missing parent tool for %s\n' "$tool" >&2; exit 1
    fi
  fi
done

while IFS= read -r path; do
  [[ -n "$path" ]] || continue
  if ! git cat-file -e "HEAD:$path" 2>/dev/null; then
    printf 'Missing local evidence path: %s\n' "$path" >&2; exit 1
  fi
done < <(sed -n 's/^local_paths = \[\(.*\)\]$/\1/p' "$ledger" | tr -d '" ' | tr ',' '\n')

printf 'OK: %s ProverKind declarations; %s assessed tool roles\n' "${#enum_names[@]}" "${#statuses[@]}"

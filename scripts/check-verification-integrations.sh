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
if ! grep -Fxq "enum_source = \"$enum_source\"" "$ledger"; then
  printf 'Ledger enum_source is stale\n' >&2
  exit 1
fi
if ! grep -Fxq "enum_registry = \"$registry\"" "$ledger"; then
  printf 'Ledger enum_registry is stale\n' >&2
  exit 1
fi

declare -A statuses kinds parents
while IFS='|' read -r tool status kind parent; do
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
done < <(awk '
  function emit() { if (tool != "") print tool "|" status "|" kind "|" parent }
  /^\[tool\.[[:alnum:]_]+\]$/ {
    emit(); tool = $0; sub(/^\[tool\./, "", tool); sub(/\]$/, "", tool)
    status = kind = parent = ""; next
  }
  tool != "" && /^status = / { status = $3; gsub(/"/, "", status) }
  tool != "" && /^prover_kind = / { kind = $3; gsub(/"/, "", kind) }
  tool != "" && /^parent_tool = / { parent = $3; gsub(/"/, "", parent) }
  END { emit() }
' "$ledger")

if ((${#statuses[@]} != 12)); then
  printf 'Expected 12 assessed tool roles, found %s\n' "${#statuses[@]}" >&2
  exit 1
fi
for tool in "${!statuses[@]}"; do
  if [[ "${statuses[$tool]}" == backend_declared ]]; then
    if [[ -z "${kinds[$tool]}" ]] || ! printf '%s\n' "${enum_names[@]}" | grep -Fxq "${kinds[$tool]}"; then
      printf 'Missing declared backend variant for %s\n' "$tool" >&2; exit 1
    fi
  elif [[ -n "${kinds[$tool]}" ]]; then
    printf 'Non-backend %s declares a prover variant\n' "$tool" >&2; exit 1
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

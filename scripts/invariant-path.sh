#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd -- "${SCRIPT_DIR}/.." && pwd)"
IP_ROOT="${REPO_ROOT}/../invariant-path"

if [[ ! -f "${IP_ROOT}/Cargo.toml" ]]; then
  echo "invariant-path workspace not found at ${IP_ROOT}" >&2
  exit 1
fi

if [[ $# -eq 0 ]]; then
  set -- scan --profile echidna --file "${REPO_ROOT}/README.adoc" --artifact-uri "repo://README.adoc"
elif [[ "$1" == "scan" ]]; then
  shift
  has_profile="false"
  for arg in "$@"; do
    if [[ "$arg" == "--profile" ]]; then
      has_profile="true"
      break
    fi
  done
  if [[ "${has_profile}" == "true" ]]; then
    set -- scan "$@"
  else
    set -- scan --profile echidna "$@"
  fi
fi

exec cargo run --manifest-path "${IP_ROOT}/Cargo.toml" -p invariant-path-cli -- "$@"

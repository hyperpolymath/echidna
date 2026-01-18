#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
BIN="${ROOT_DIR}/target/release/echidna"

if [[ ! -x "$BIN" ]]; then
  echo "[MVP] echidna binary not found: $BIN"
  echo "[MVP] Build with: cargo build --release"
  exit 1
fi

PROVERS=(
  agda coq lean isabelle z3 cvc5 metamath hollight mizar pvs acl2 hol4
)

missing=()

check_cmd() {
  local cmd="$1"
  if ! command -v "$cmd" >/dev/null 2>&1; then
    missing+=("$cmd")
  fi
}

# Basic executable checks (best-effort: many provers are optional installs)
check_cmd agda
check_cmd coqtop
check_cmd lean
check_cmd isabelle
check_cmd z3
check_cmd cvc5
check_cmd metamath
check_cmd hol-light
check_cmd mizar
check_cmd pvs
check_cmd acl2
check_cmd hol4

if [[ ${#missing[@]} -gt 0 ]]; then
  echo "[MVP] Missing executables: ${missing[*]}"
fi

# Minimal list-provers check
"$BIN" list-provers >/dev/null

# Minimal health for server startup is manual; keep smoke lightweight

echo "[MVP] Smoke checks completed (missing executables are expected on dev machines)."

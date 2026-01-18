#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
BIN="${ROOT_DIR}/target/release/echidna"

if [[ ! -x "$BIN" ]]; then
  echo "[MVP] echidna binary not found: $BIN"
  echo "[MVP] Build with: cargo build --release"
  exit 1
fi

# Minimal proof samples (placeholders). If prover executable is missing,
# we skip and record.
PROVERS=(
  agda coq lean isabelle z3 cvc5 metamath hollight mizar pvs acl2 hol4
)

missing=()
passed=()
failed=()

check_cmd() {
  local cmd="$1"
  if ! command -v "$cmd" >/dev/null 2>&1; then
    return 1
  fi
  return 0
}

check_mizar_toolchain() {
  local verifier_cmd
  local mizf_cmd
  # Avoid invoking Mizar binaries in sandboxed environments unless explicitly allowed.
  if [[ -z "${MIZAR_TOOLCHAIN_OK:-}" ]]; then
    return 1
  fi
  verifier_cmd="$(command -v verifier || true)"
  mizf_cmd="$(command -v mizf || true)"
  if [[ -z "$verifier_cmd" || -z "$mizf_cmd" ]]; then
    return 1
  fi
  return 0
}

# Map prover -> executable
exe_for() {
  case "$1" in
    agda) echo agda;;
    coq) echo coqtop;;
    lean) echo lean;;
    isabelle) echo isabelle;;
    z3) echo z3;;
    cvc5) echo cvc5;;
    metamath) echo metamath;;
    hollight) echo hol-light;;
    mizar) echo mizar;;
    pvs) echo pvs;;
    acl2) echo acl2;;
    hol4) echo hol4;;
    *) echo "";;
  esac
}

# Minimal sample files (expected to exist in proofs/)
# If not present, we skip.
FILE_MAP=(
  "agda:proofs/agda/Basic.agda"
  "coq:proofs/coq/basic.v"
  "lean:proofs/lean/mvp_basic.lean"
  "isabelle:proofs/isabelle/Basic.thy"
  "z3:proofs/z3/basic.smt2"
  "cvc5:proofs/cvc5/basic.smt2"
  "metamath:proofs/metamath/basic.mm"
  "hollight:proofs/hol_light/basic.hl"
  "mizar:proofs/mizar/mvp_basic.miz"
  "pvs:proofs/pvs/basic.pvs"
  "acl2:proofs/acl2/basic.lisp"
  "hol4:proofs/hol4/basic.sml"
)

file_for() {
  local prover="$1"
  for entry in "${FILE_MAP[@]}"; do
    local key="${entry%%:*}"
    local path="${entry#*:}"
    if [[ "$key" == "$prover" ]]; then
      echo "$ROOT_DIR/$path"
      return
    fi
  done
  echo ""
}

for prover in "${PROVERS[@]}"; do
  exe="$(exe_for "$prover")"
  if [[ -z "$exe" ]] || ! check_cmd "$exe"; then
    missing+=("$prover")
    continue
  fi
  if [[ "$prover" == "mizar" ]] && ! check_mizar_toolchain; then
    missing+=("$prover")
    continue
  fi

  sample_file="$(file_for "$prover")"
  if [[ -z "$sample_file" || ! -f "$sample_file" ]]; then
    echo "[MVP] Missing sample for $prover ($sample_file); skipping."
    missing+=("$prover")
    continue
  fi

  if "$BIN" verify --prover "$prover" "$sample_file" >/dev/null 2>&1; then
    passed+=("$prover")
  else
    failed+=("$prover")
  fi

done

echo "[MVP] Functional sweep summary"
echo "  Passed: ${passed[*]:-none}"
echo "  Failed: ${failed[*]:-none}"
echo "  Missing: ${missing[*]:-none}"

if [[ ${#failed[@]} -gt 0 ]]; then
  exit 1
fi

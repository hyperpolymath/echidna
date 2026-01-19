#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
TOOLBOX_NAME="${TOOLBOX_NAME:-toolbx}"
IN_TOOLBOX=0
if [[ -f /run/.containerenv || -n "${TOOLBOX_PATH:-}" ]]; then
  IN_TOOLBOX=1
fi

BASE_PACKAGES=(
  agda
  coq
  cvc5
  acl2
)

OPTIONAL_PACKAGES=(
  isabelle
  hol4
  hol-light
  metamath
  mizar
)

run_host_install() {
  if [[ "$IN_TOOLBOX" -eq 1 ]]; then
    echo "[install] Running inside toolbox; skipping host installs."
    return 0
  fi
  if ! command -v dnf >/dev/null 2>&1; then
    echo "[install] dnf not found on host; skipping host installs."
    return 0
  fi

  echo "[install] Installing base provers on host..."
  sudo dnf -y install --skip-unavailable "${BASE_PACKAGES[@]}" || true

  echo "[install] Installing optional provers on host..."
  sudo dnf -y install --skip-unavailable "${OPTIONAL_PACKAGES[@]}" || true

  echo "[install] Host package search (for missing packages):"
  dnf search "${BASE_PACKAGES[@]}" "${OPTIONAL_PACKAGES[@]}" || true
}

run_toolbox_install() {
  if ! command -v toolbox >/dev/null 2>&1; then
    echo "[install] toolbox not available; skipping toolbox installs."
    return 0
  fi
  if [[ "$IN_TOOLBOX" -eq 1 ]]; then
    echo "[install] Installing provers inside current toolbox..."
    sudo dnf -y install --skip-unavailable "${BASE_PACKAGES[@]}" || true
    sudo dnf -y install --skip-unavailable "${OPTIONAL_PACKAGES[@]}" || true
    dnf search "${BASE_PACKAGES[@]}" "${OPTIONAL_PACKAGES[@]}" || true
    return 0
  fi

  echo "[install] Installing base provers in toolbox (${TOOLBOX_NAME})..."
  toolbox run -c "${TOOLBOX_NAME}" -- sudo dnf -y install --skip-unavailable ${BASE_PACKAGES[*]} || true

  echo "[install] Installing optional provers in toolbox (${TOOLBOX_NAME})..."
  toolbox run -c "${TOOLBOX_NAME}" -- sudo dnf -y install --skip-unavailable ${OPTIONAL_PACKAGES[*]} || true

  echo "[install] Toolbox package search (for missing packages):"
  toolbox run -c "${TOOLBOX_NAME}" -- dnf search ${BASE_PACKAGES[*]} ${OPTIONAL_PACKAGES[*]} || true
}

run_mizar_checks() {
  echo "[mizar] Checking Mizar toolchain on host..."
  if command -v verifier >/dev/null 2>&1 && command -v mizf >/dev/null 2>&1; then
    verifier -h >/dev/null 2>&1 || true
    mizf -h >/dev/null 2>&1 || true
    echo "[mizar] verifier and mizf are on PATH."
  else
    echo "[mizar] verifier/mizf not found on PATH."
  fi

  echo "[mizar] If installed under ~/.local/mizar, export:"
  echo "         export PATH=\"\$HOME/.local/mizar/bin:\$PATH\""
  echo "         export MIZFILES=\"\$HOME/.local/mizar/share\""
}

echo "[install] Working directory: ${ROOT_DIR}"
run_host_install
run_toolbox_install
run_mizar_checks

echo "[install] Done."

#!/usr/bin/env bash
# SPDX-License-Identifier: PMPL-1.0-or-later
#
# ECHIDNA — Cerro Torre build, sign, and verify pipeline
#
# Usage:
#   ./ct-build.sh                  # Build + sign (local only)
#   ./ct-build.sh --push           # Build + sign + push to registry

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

PUSH=""
for arg in "$@"; do
    if [ "$arg" = "--push" ]; then
        PUSH="--push"
    fi
done

CT_KEY_ID="${CT_KEY_ID:-echidna-release}"
CT_REGISTRY="${CT_REGISTRY:-ghcr.io/hyperpolymath}"
CT_TAG="${CT_TAG:-latest}"

IMAGE_NAME="echidna"
FULL_IMAGE="${CT_REGISTRY}/${IMAGE_NAME}:${CT_TAG}"
CTP_FILE="${SCRIPT_DIR}/${IMAGE_NAME}-${CT_TAG}.ctp"

echo "=== ECHIDNA Cerro Torre Build Pipeline ==="
echo "  Image:  ${FULL_IMAGE}"
echo "  Key:    ${CT_KEY_ID}"
echo "  Bundle: ${CTP_FILE}"
echo ""

echo "--- Step 1: Building container image ---"
podman build \
    -t "${FULL_IMAGE}" \
    -f "${SCRIPT_DIR}/Containerfile" \
    "${REPO_ROOT}"
echo "  Built: ${FULL_IMAGE}"
echo ""

echo "--- Step 2: Packing into .ctp bundle ---"
if command -v ct &>/dev/null; then
    ct pack "${FULL_IMAGE}" -o "${CTP_FILE}"
    echo "  Packed: ${CTP_FILE}"
else
    echo "  SKIP: ct not found (install cerro-torre CLI)"
    if [ "$PUSH" = "--push" ]; then
        echo "--- Pushing unsigned OCI image ---"
        podman push "${FULL_IMAGE}"
        echo "  Pushed: ${FULL_IMAGE} (unsigned OCI)"
    fi
    echo ""
    echo "=== Build complete (without .ctp signing) ==="
    exit 0
fi
echo ""

echo "--- Step 3: Signing .ctp bundle ---"
if command -v cerro-sign &>/dev/null; then
    cerro-sign sign "${CTP_FILE}" --key-id "${CT_KEY_ID}"
    echo "  Signed: ${CTP_FILE} (key: ${CT_KEY_ID})"
elif command -v ct &>/dev/null; then
    ct sign "${CTP_FILE}" --key "${CT_KEY_ID}"
    echo "  Signed: ${CTP_FILE} (key: ${CT_KEY_ID})"
else
    echo "  SKIP: cerro-sign not found"
fi
echo ""

echo "--- Step 4: Verifying .ctp bundle ---"
if command -v ct &>/dev/null; then
    ct verify "${CTP_FILE}"
    echo "  Verified: ${CTP_FILE}"
else
    echo "  SKIP: ct not found"
fi
echo ""

if [ "$PUSH" = "--push" ]; then
    echo "--- Step 5: Pushing to registry ---"
    if command -v ct &>/dev/null; then
        ct push "${CTP_FILE}" "${FULL_IMAGE}"
        echo "  Pushed: ${FULL_IMAGE}"
    else
        podman push "${FULL_IMAGE}"
        echo "  Pushed: ${FULL_IMAGE} (unsigned OCI)"
    fi
    echo ""
fi

echo "=== Build pipeline complete ==="
echo "  Image:  ${FULL_IMAGE}"
echo "  Bundle: ${CTP_FILE}"

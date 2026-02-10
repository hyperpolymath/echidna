#!/usr/bin/env bash
# SPDX-License-Identifier: PMPL-1.0-or-later
# Build ECHIDNA container images using Podman
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
IMAGE_NAME="${IMAGE_NAME:-echidna}"
TAG="${TAG:-latest}"

build_minimal() {
    echo "Building minimal image: ${IMAGE_NAME}:${TAG}"
    podman build \
        -f "$SCRIPT_DIR/Containerfile" \
        -t "${IMAGE_NAME}:${TAG}" \
        "$REPO_ROOT"
}

build_full() {
    echo "Building full image: ${IMAGE_NAME}:full"
    podman build \
        -f "$SCRIPT_DIR/Containerfile.full" \
        -t "${IMAGE_NAME}:full" \
        "$REPO_ROOT"
}

case "${1:-minimal}" in
    minimal)
        build_minimal
        ;;
    full)
        build_full
        ;;
    all)
        build_minimal
        build_full
        ;;
    *)
        echo "Usage: $0 {minimal|full|all}"
        exit 1
        ;;
esac

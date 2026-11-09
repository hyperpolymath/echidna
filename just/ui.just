# SPDX-License-Identifier: MPL-2.0
# Imported by the root Justfile (hotspot split); recipes moved verbatim.

# ── UI Management ──────────────────────────────────────────

# ── UI ──
# The AffineScript UI was removed 2026-08 (AffineScript is a banned language under the
# estate language policy; AffineScript-TEA is the replacement). The TEA sources
# live in src/ui/tea/ and the static shell in src/ui/public/, but the
# AffineScript compile pipeline is NOT wired yet — see issues #117 and #266
# (missing Http::fetch / Async / Json primitives).

# Build the UI — blocked on the AffineScript-TEA toolchain
build-ui:
    @echo "build-ui is unavailable: the AffineScript UI was removed and the"
    @echo "AffineScript-TEA pipeline is not wired yet (issues #117, #266)."
    @echo "Sources: src/ui/tea/echidna_gui.affine; shell: src/ui/public/."
    @exit 1

# Serve the static UI shell (no compile step) on http://localhost:3000.
# Bun is the estate JavaScript runtime; Deno is retired (2026-09-22 ruling).
serve-ui:
    cd src/ui/public && bun ../../../scripts/serve-static.js 3000

# Launch full ECHIDNA GUI (Backend + UI + Browser)
gui:
    #!/usr/bin/env bash
    set -euo pipefail
    echo "Launching ECHIDNA GUI..."
    # Start backend
    cargo run -- server --port 8081 --cors > /dev/null 2>&1 & BACKEND_PID=$!
    echo "Started backend (PID $BACKEND_PID)"
    # Start UI server
    (cd src/ui/public && bun ../../../scripts/serve-static.js 3000) > /dev/null 2>&1 & UI_PID=$!
    echo "Started UI server (PID $UI_PID)"
    # Cleanup on exit
    trap "kill $BACKEND_PID $UI_PID 2>/dev/null || true" EXIT
    # Wait for servers to start
    echo "Waiting for servers to initialize..."
    sleep 2
    # Open browser
    URL="http://localhost:3000"
    echo "Opening $URL..."
    xdg-open "$URL" > /dev/null 2>&1 || open "$URL" > /dev/null 2>&1 || echo "Please open $URL in your browser"
    echo "ECHIDNA GUI is running. Press Ctrl+C in this terminal to stop."
    # Wait for background processes
    wait

# All checks before commit
pre-commit: fmt-check lint test
    @echo "All checks passed!"

# MVP 1.0 smoke checks
mvp:
    ./scripts/mvp-smoke.sh

# MVP 1.0 dependency checklist (best-effort)
mvp-env:
    ./scripts/mvp-smoke.sh || true

# Build minimal container image (Z3, CVC5, Lean, Idris2)
container-build:
    podman build -f .containerization/Containerfile -t echidna:latest .

# Build full container image (all provers + Julia)
container-build-full:
    podman build -f .containerization/Containerfile.full -t echidna:full .

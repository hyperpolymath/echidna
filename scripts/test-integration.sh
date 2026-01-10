#!/bin/bash
# SPDX-FileCopyrightText: 2025 ECHIDNA Project Team
# SPDX-License-Identifier: MIT OR Palimpsest-0.6

# Integration test runner for Rust↔Julia communication
# Starts Julia test server, runs Rust integration tests, then stops server

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"
JULIA_DIR="$PROJECT_ROOT/src/julia"
PORT="${1:-8081}"

echo "=== ECHIDNA Integration Test Runner ==="
echo "Project root: $PROJECT_ROOT"
echo "Julia directory: $JULIA_DIR"
echo "Port: $PORT"
echo ""

# Function to cleanup on exit
cleanup() {
    echo ""
    echo "Cleaning up..."
    if [ -n "$JULIA_PID" ]; then
        echo "Stopping Julia server (PID: $JULIA_PID)..."
        kill $JULIA_PID 2>/dev/null || true
        wait $JULIA_PID 2>/dev/null || true
    fi
}
trap cleanup EXIT

# Check Julia is available
if ! command -v julia &> /dev/null; then
    echo "ERROR: Julia not found in PATH"
    exit 1
fi

echo "Julia version: $(julia --version)"
echo ""

# Install Julia dependencies if needed
echo "Checking Julia dependencies..."
cd "$JULIA_DIR"
julia --project=. -e 'using Pkg; Pkg.instantiate()' 2>/dev/null || {
    echo "Installing Julia dependencies..."
    julia --project=. -e 'using Pkg; Pkg.instantiate()'
}

# Start Julia test server in background
echo ""
echo "Starting Julia test server on port $PORT..."
julia --project=. test_server.jl $PORT &
JULIA_PID=$!

# Wait for server to be ready
echo "Waiting for server to start..."
MAX_RETRIES=30
RETRY_COUNT=0
while [ $RETRY_COUNT -lt $MAX_RETRIES ]; do
    if curl -s "http://localhost:$PORT/health" > /dev/null 2>&1; then
        echo "Server is ready!"
        break
    fi
    sleep 0.5
    RETRY_COUNT=$((RETRY_COUNT + 1))
done

if [ $RETRY_COUNT -eq $MAX_RETRIES ]; then
    echo "ERROR: Server failed to start within timeout"
    exit 1
fi

# Run Rust integration tests
echo ""
echo "Running Rust integration tests..."
cd "$PROJECT_ROOT"
cargo test --test test_neural_integration -- --include-ignored --nocapture

echo ""
echo "=== Integration tests completed successfully ==="

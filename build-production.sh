#!/bin/bash
# SPDX-License-Identifier: MIT OR Palimpsest-0.6
# Production build script for ECHIDNA

set -e

echo "╔════════════════════════════════════════════════════════════╗"
echo "║         ECHIDNA Production Build                           ║"
echo "╚════════════════════════════════════════════════════════════╝"
echo ""

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# Step 1: Build Rust backend
echo -e "${YELLOW}[1/4]${NC} Building Rust backend (release mode)..."
cargo build --release
echo -e "${GREEN}✓${NC} Rust backend built"
echo ""

# Step 2: Build ReScript frontend
echo -e "${YELLOW}[2/4]${NC} Building ReScript frontend..."
cd src/rescript
./node_modules/.bin/rescript build
echo -e "${GREEN}✓${NC} ReScript frontend compiled"
echo ""

# Step 3: Create distribution directory
echo -e "${YELLOW}[3/4]${NC} Creating distribution package..."
cd ../..
mkdir -p dist/echidna
mkdir -p dist/echidna/bin
mkdir -p dist/echidna/ui
mkdir -p dist/echidna/models
mkdir -p dist/echidna/examples

# Copy binaries
cp target/release/echidna dist/echidna/bin/

# Copy UI files
cp src/rescript/index.html dist/echidna/ui/
cp -r src/rescript/src/*.bs.js dist/echidna/ui/
cp -r src/rescript/src/**/*.bs.js dist/echidna/ui/ 2>/dev/null || true

# Copy ML models if they exist
cp models/*.jlso dist/echidna/models/ 2>/dev/null || true

# Copy examples
cp -r examples/*.* dist/echidna/examples/ 2>/dev/null || true

echo -e "${GREEN}✓${NC} Distribution package created"
echo ""

# Step 4: Create startup script
echo -e "${YELLOW}[4/4]${NC} Creating startup script..."
cat > dist/echidna/start.sh << 'STARTUP'
#!/bin/bash
# Start ECHIDNA platform

# Start backend
echo "Starting ECHIDNA backend..."
./bin/echidna server --port 8080 --cors &
BACKEND_PID=$!

# Wait for backend to be ready
sleep 2

# Start frontend
echo "Starting ECHIDNA frontend..."
cd ui
python3 -m http.server 3000 &
FRONTEND_PID=$!

echo ""
echo "╔════════════════════════════════════════════════════════════╗"
echo "║              ECHIDNA is now running!                       ║"
echo "╠════════════════════════════════════════════════════════════╣"
echo "║  UI:  http://127.0.0.1:3000                                ║"
echo "║  API: http://127.0.0.1:8080/api                            ║"
echo "╚════════════════════════════════════════════════════════════╝"
echo ""
echo "Press Ctrl+C to stop both servers"

# Wait for Ctrl+C
trap "kill $BACKEND_PID $FRONTEND_PID" EXIT
wait
STARTUP

chmod +x dist/echidna/start.sh

echo -e "${GREEN}✓${NC} Startup script created"
echo ""

# Create README
cat > dist/echidna/README.md << 'README'
# ECHIDNA Distribution

**Neurosymbolic Theorem Proving Platform**

## Quick Start

```bash
./start.sh
```

Then open http://127.0.0.1:3000 in your browser.

## Contents

- `bin/echidna` - Main executable
- `ui/` - Web interface
- `models/` - ML models
- `examples/` - Example proofs
- `start.sh` - Startup script

## Requirements

- Python 3 (for UI server)
- Modern web browser
- Linux/macOS

## Manual Start

Backend:
```bash
./bin/echidna server --port 8080 --cors
```

Frontend:
```bash
cd ui && python3 -m http.server 3000
```

## Documentation

See QUICKSTART.md for full documentation.
README

echo "╔════════════════════════════════════════════════════════════╗"
echo "║              Production Build Complete! ✓                  ║"
echo "╚════════════════════════════════════════════════════════════╝"
echo ""
echo "Distribution created in: dist/echidna/"
echo ""
echo "To run:"
echo "  cd dist/echidna"
echo "  ./start.sh"
echo ""

#!/bin/bash
# SPDX-License-Identifier: MIT OR Palimpsest-0.6
# Quick training data expansion script for ECHIDNA

set -e

ECHIDNA_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
DATA_DIR="$ECHIDNA_ROOT/external_corpora"
TRAINING_DIR="$ECHIDNA_ROOT/training_data"

echo "=================================="
echo "ECHIDNA Training Data Expansion"
echo "=================================="
echo

# Phase 1: Mine existing proof files
echo "Phase 1: Mining existing proof files..."
echo "  Current: 107 proofs"
echo "  Target:  ~150 proofs (+40%)"
echo

# Count existing proofs
EXISTING_COUNT=$(find "$ECHIDNA_ROOT/proofs" -name "*.v" -o -name "*.lean" -o -name "*.thy" -o -name "*.lisp" -o -name "*.pvs" 2>/dev/null | wc -l)
echo "  Found $EXISTING_COUNT proof files to mine"

if [ "$EXISTING_COUNT" -gt 10 ]; then
    echo "  ✓ Ready to extract"
    echo
    echo "  Run this to extract:"
    echo "    cd $ECHIDNA_ROOT"
    echo "    julia --project=src/julia -e 'include(\"src/julia/extract_training_data.jl\")'"
else
    echo "  ⚠ Few proof files found - may need to add more examples"
fi

echo
echo "Phase 2: Download proof corpora..."
echo "  CoqGym:    71,000 proofs (2.4 GB)"
echo "  Mathlib4:  100,000+ tactics (1.2 GB)"
echo "  Metamath:  30,000 theorems (50 MB)"
echo "  Total:     ~200,000 proofs (4 GB)"
echo

read -p "Download proof corpora? (y/N) " -n 1 -r
echo
if [[ $REPLY =~ ^[Yy]$ ]]; then
    mkdir -p "$DATA_DIR"
    cd "$DATA_DIR"

    # CoqGym (highest value/size ratio)
    if [ ! -d "CoqGym" ]; then
        echo "Downloading CoqGym (2.4 GB)..."
        git clone --depth 1 https://github.com/princeton-vl/CoqGym.git
        echo "✓ CoqGym downloaded"
    else
        echo "✓ CoqGym already exists"
    fi

    # Metamath (small but high quality)
    if [ ! -d "metamath" ]; then
        echo "Downloading Metamath (50 MB)..."
        git clone --depth 1 https://github.com/metamath/set.mm.git metamath
        echo "✓ Metamath downloaded"
    else
        echo "✓ Metamath already exists"
    fi

    # Lean mathlib (large, deferred)
    if [ ! -d "mathlib4" ]; then
        echo "Lean mathlib4 (1.2 GB) - skipped (add manually if needed)"
        echo "  git clone --depth 1 https://github.com/leanprover-community/mathlib4.git"
    fi

    echo
    echo "✓ Download complete!"
    du -sh "$DATA_DIR"/*
else
    echo "Skipped download"
fi

echo
echo "Phase 3: Extract and prepare data..."
echo

# Show next steps
cat <<'EOF'
Next Steps:
===========

1. Extract from existing proofs (5 minutes):
   cd /var/home/hyper/Documents/hyperpolymath-repos/echidna
   julia --project=src/julia src/julia/extract_training_data.jl

2. Extract from CoqGym (if downloaded, 30 minutes):
   julia --project=src/julia -e '
     using JSON3
     # Parse CoqGym JSON files
     # Add to training_data/
   '

3. Retrain models (10 minutes):
   julia --project=src/julia src/julia/train_models.jl

4. Test new models:
   # Restart Julia API server
   julia --project=src/julia src/julia/api_server.jl &

   # Test predictions
   curl -X POST http://127.0.0.1:9000/suggest \
     -d '{"goal":"forall n, n + 0 = n","prover":"Coq"}'

Expected Results:
=================
- Proofs:      107 → 150+ (Phase 1) → 5000+ (Phase 2+3)
- Tactics:     585 → 800+ → 20000+
- Vocab:       62 → 150+ → 500+
- Confidence:  ~65% → 75%+ → 80%+

Notes:
======
- Phase 1 is free and quick (recommended start)
- Phase 2 requires 4GB disk space
- Phase 3 requires compute time for training
- Models improve incrementally with each phase

Documentation: TRAINING_DATA_EXPANSION.md
EOF

echo
echo "=================================="
echo "Ready to expand training data!"
echo "=================================="

# ECHIDNA v1.3 - Quick Start Guide

> Get ECHIDNA running in 5 minutes

## Prerequisites

- **Julia 1.10+** with packages: HTTP, JSON3, LinearAlgebra
- **Rust 1.75+** with Cargo
- **Python 3.8+** (for dev server)
- **curl** and **jq** (for testing)

## Quick Start (3 commands)

```bash
# 1. Start Julia ML API (port 9000)
julia src/julia/api_server.jl &

# 2. Start Rust backend (port 8080)
./target/release/echidna server --port 8080 --enable-cors &

# 3. Start UI dev server (port 3000)
cd src/rescript && python3 -m http.server 3000 &
```

**Access UI:** http://127.0.0.1:3000

## Verify Installation

```bash
./tests/integration_test.sh
```

Expected output:
```
╔═══════════════════════════════════════════════════════════╗
║  All Integration Tests Passed ✓                          ║
╚═══════════════════════════════════════════════════════════╝
```

## Architecture Overview

```
┌─────────────────┐
│  ReScript UI    │  Port 3000
│  (Browser)      │  → Fetch API
└────────┬────────┘
         │
         v
┌─────────────────┐
│  Rust Backend   │  Port 8080
│  (HTTP Server)  │  → reqwest
└────────┬────────┘
         │
         v
┌─────────────────┐
│  Julia ML API   │  Port 9000
│  (Trained       │  → HTTP.jl
│   Models)       │
└─────────────────┘
         │
         v
┌─────────────────┐
│  12 Prover      │  Subprocesses
│  Backends       │  → stdin/stdout
└─────────────────┘
```

## Example: Prove a Theorem

### Via REST API

```bash
curl -X POST http://127.0.0.1:8080/api/tactics/suggest \
  -H "Content-Type: application/json" \
  -d '{
    "goal": "forall n : nat, n + 0 = n",
    "prover": "Coq",
    "top_k": 5
  }'
```

**Response:**
```json
{
  "suggestions": [
    {"tactic": "reflexivity", "confidence": 0.321},
    {"tactic": "simpl", "confidence": 0.288},
    {"tactic": "intros", "confidence": 0.233},
    {"tactic": "apply", "confidence": 0.076},
    {"tactic": "rewrite", "confidence": 0.046}
  ]
}
```

### Via CLI

```bash
./target/release/echidna repl --prover Coq
```

Then type:
```coq
Theorem plus_0_r : forall n : nat, n + 0 = n.
suggest
apply reflexivity
```

## What Just Happened?

1. **ReScript UI** sends goal to Rust backend
2. **Rust backend** forwards to Julia ML API
3. **Julia ML API** runs trained model (logistic regression on 332 proofs)
4. **ML model** returns tactic suggestions with confidence scores
5. **Rust backend** formats response for UI
6. **UI** displays suggestions with aspect tags

## Trained Models

Located in `models/`:
- `tactic_model.txt` - Logistic regression (8 classes, 62 features)
- `tactic_vocab.txt` - Vocabulary (62 words)
- `premise_vocab.txt` - Premise vocabulary (870 terms)

Training data: **332 proofs** across 12 provers (1,603 tactics)

## Services & Ports

| Service | Port | Purpose | Tech |
|---------|------|---------|------|
| Julia ML API | 9000 | Neural inference | Julia + HTTP.jl |
| Rust Backend | 8080 | REST API, sessions | Rust + Axum |
| UI Dev Server | 3000 | Static files | Python http.server |

## REST API Endpoints

### Health & Info
- `GET /api/health` - Health check
- `GET /api/provers` - List 12 provers
- `GET /api/aspect-tags` - List 6 aspect tags

### Proof Operations
- `POST /api/tactics/suggest` - Get AI tactic suggestions
- `POST /api/theorems/search` - Search theorem library
- `POST /api/session/create` - Create proof session
- `GET /api/session/:id/state` - Get session state
- `POST /api/session/:id/apply` - Apply tactic
- `GET /api/session/:id/tree` - Get proof tree

## Development Workflow

### Rebuild After Changes

```bash
# Rebuild Rust (if backend changed)
cargo build --release

# Rebuild ReScript (if UI changed)
cd src/rescript && npm run build

# Restart services
pkill -f "echidna server"
pkill -f "api_server.jl"
pkill -f "http.server 3000"

# Re-run quick start commands
```

### Run Tests

```bash
# Unit tests
cargo test

# Property tests (1000 cases each)
cargo test --test property_tests

# Benchmarks
cargo bench

# Integration tests
./tests/integration_test.sh
```

## Trust & Validation

ECHIDNA provides **formal guarantees** of soundness:

1. **Benchmarks** - Performance regression tracking (Criterion.rs)
2. **Property Tests** - 8 invariants validated (PropTest)
3. **Formal Verification** - Idris2 proof validator with dependent types
4. **Anomaly Detection** - 7 anomaly types, multi-prover consensus

See [TRUST_AND_VALIDATION_FRAMEWORK.md](./TRUST_AND_VALIDATION_FRAMEWORK.md)

## Troubleshooting

### "Julia ML API not available"
- Check Julia is installed: `julia --version`
- Install packages: `julia -e 'using Pkg; Pkg.add(["HTTP", "JSON3"])'`
- Check port 9000 is free: `lsof -i :9000`

### "Rust backend not responding"
- Build failed? Check: `cargo build --release`
- Check port 8080 is free: `lsof -i :8080`
- Check logs: `tail -f /tmp/claude/-var-home-hyper/tasks/*/output`

### "ReScript UI not loading"
- Compiled? Check: `ls src/rescript/src/*.bs.js`
- Build: `cd src/rescript && npm run build`
- Check port 3000: `curl http://127.0.0.1:3000`

### "No tactic suggestions returned"
- Check models exist: `ls models/`
- Retrain if needed: `julia src/julia/train_models.jl`

## Next Steps

- **Production Deployment:** See [DEPLOYMENT.md](./DEPLOYMENT.md)
- **Training More Data:** See [TRAINING_EXPANSION_RESULTS.md](./TRAINING_EXPANSION_RESULTS.md)
- **Chapel Parallelism:** See [CHAPEL_METALAYER_ANALYSIS.md](./CHAPEL_METALAYER_ANALYSIS.md)
- **Trust Framework:** See [TRUST_IMPLEMENTATION_GUIDE.md](./TRUST_IMPLEMENTATION_GUIDE.md)

## License

MIT OR Palimpsest-0.6

## Support

- GitHub Issues: https://github.com/hyperpolymath/echidna/issues
- Documentation: https://echidna.hyperpolymath.org

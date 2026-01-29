# ECHIDNA Quick Start Guide

**Get up and running with the neurosymbolic theorem proving platform in 5 minutes!**

## Prerequisites

- Rust 1.70+ (`rustup`)
- Julia 1.9+ (`juliaup`)
- ReScript 11+ (included)
- Modern browser with ES6 support

## Quick Start

### 1. Start the Backend

```bash
# Build and run the Rust HTTP server
cargo build --release
./target/release/echidna server --port 8080 --cors
```

The server will start on `http://127.0.0.1:8080` with CORS enabled.

### 2. Start the Frontend

```bash
# Navigate to UI directory
cd src/rescript

# Start development server
python3 -m http.server 3000
```

The UI will be available at `http://127.0.0.1:3000`

### 3. Open in Browser

Navigate to `http://127.0.0.1:3000` and you'll see:

- **Prover Selector**: Choose from 12 theorem provers
- **Tactic Suggester**: Get AI-powered tactic recommendations
- **Theorem Search**: Search across theorem libraries
- **Goal List**: View current proof goals
- **Proof Viewer**: See your proof script
- **Proof Tree**: Visualize proof structure

## Try the Demo

Run the interactive demo script:

```bash
./demo-proof.sh
```

This will:
1. Create a proof session
2. Show available provers
3. Display aspect tags
4. Get AI tactic suggestions
5. Search theorem libraries
6. Show proof tree structure

## API Endpoints

All endpoints available at `http://127.0.0.1:8080/api`:

### Core Endpoints

| Endpoint | Method | Description |
|----------|--------|-------------|
| `/health` | GET | Health check |
| `/provers` | GET | List all 12 provers |
| `/session/create` | POST | Create new proof session |
| `/session/:id/state` | GET | Get current session state |
| `/session/:id/apply` | POST | Apply tactic to session |

### UI-Specific Endpoints

| Endpoint | Method | Description |
|----------|--------|-------------|
| `/aspect-tags` | GET | Get filtering tags |
| `/tactics/suggest` | POST | AI tactic suggestions |
| `/theorems/search` | GET | Search theorem library |
| `/session/:id/tree` | GET | Get proof tree |

## Example: Create a Session

```bash
# Create a Coq proof session
curl -X POST http://127.0.0.1:8080/api/session/create \
  -H "Content-Type: application/json" \
  -d '{"prover":"Coq"}'

# Response:
# {"session_id":"794aab59-5b16-4934-98a0-4a3a4d19aa0e"}
```

## Example: Get Tactic Suggestions

```bash
curl -X POST http://127.0.0.1:8080/api/tactics/suggest \
  -H "Content-Type: application/json" \
  -d '{"goal_id":"goal-1","active_tags":["algebraic"]}'

# Response:
# {
#   "suggestions": [
#     {
#       "tactic": "intro",
#       "confidence": 0.92,
#       "premise": "Introduce hypothesis",
#       "aspect_tags": ["deductive"]
#     },
#     ...
#   ]
# }
```

## Example: Search Theorems

```bash
curl "http://127.0.0.1:8080/api/theorems/search?query=associativity"

# Response:
# {
#   "results": [
#     "Theorem: associativity_add (a + b) + c = a + (b + c)",
#     "Theorem: commutativity_mul a * b = b * a",
#     "Lemma: distributivity a * (b + c) = a * b + a * c"
#   ]
# }
```

## Architecture

```
Browser → ReScript UI (port 3000)
            ↓
         Rust API (port 8080)
            ↓
    ┌───────┴────────┐
    ↓                ↓
Julia ML         12 Provers
(Neural AI)    (Tier 1-4)
```

## Supported Provers

### Tier 1 (Production Ready)
- Agda - Dependently typed proof assistant
- Coq - Interactive theorem prover (CIC)
- Lean - Modern proof assistant
- Isabelle - Generic proof assistant (HOL)
- Z3 - SMT solver
- CVC5 - SMT solver

### Tier 2 (Stable)
- Metamath - Minimal proof verification
- HOL Light - Simple HOL prover
- Mizar - Natural language proofs

### Tier 3 (Experimental)
- PVS - Specification system
- ACL2 - Computational logic

### Tier 4 (Research)
- HOL4 - Interactive HOL prover

## Features

✅ **12 Theorem Provers** - Widest coverage in any platform  
✅ **AI-Powered Suggestions** - Neural premise selection & tactic prediction  
✅ **Aspect Tagging** - Filter by domain (algebraic, geometric, logical) or technique  
✅ **OpenCyc Integration** - Semantic understanding of mathematical concepts  
✅ **Interactive UI** - Modern React-based interface  
✅ **REST API** - Easy integration with external tools  
✅ **Session Management** - Multiple concurrent proof sessions  
✅ **Proof Visualization** - Interactive proof tree explorer  

## Troubleshooting

### Port Already in Use

```bash
# Find and kill process on port 8080
lsof -ti:8080 | xargs kill -9

# Or use a different port
./target/release/echidna server --port 8081
```

### CORS Issues

Make sure the server is started with `--cors` flag:

```bash
./target/release/echidna server --port 8080 --cors
```

### UI Not Loading

1. Check that both servers are running:
   - Backend: `curl http://127.0.0.1:8080/api/health`
   - Frontend: `curl http://127.0.0.1:3000`

2. Check browser console for errors (F12)

3. Try clearing browser cache

### ReScript Compilation Errors

Rebuild from clean state:

```bash
cd src/rescript
rm -rf node_modules lib
npm install
./node_modules/.bin/rescript build
```

## Next Steps

1. **Try the Examples**: Check `examples/` directory for sample proofs
2. **Read the Docs**: See `docs/` for detailed documentation
3. **Join Development**: See `CONTRIBUTING.md` to contribute
4. **Report Issues**: Use GitHub Issues for bug reports

## Support

- **Documentation**: `docs/`
- **Examples**: `examples/`
- **API Reference**: `INTEGRATION_TEST_RESULTS.md`
- **Issues**: https://github.com/hyperpolymath/echidna/issues

---

**Happy Proving! 🦔**

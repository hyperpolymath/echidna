<!--
SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
SPDX-License-Identifier: CC-BY-SA-4.0
-->

# Supported Provers

ECHIDNA implements 100+ prover backends, but the surface a new user
encounters is deliberately smaller. This document is the source of truth
for what works out of the box.

## What the API actually exposes

`GET /api/provers` returns 12 **core** provers (`ProverKind::all_core()`
in `src/rust/provers/mod.rs:689`). These are the only ones the bundled
UI (`src/ui/public/prove.html`) and the REST clients see by default:

| Prover     | Kind                                  | Required binary | Install hint                                                                                    |
|------------|---------------------------------------|-----------------|-------------------------------------------------------------------------------------------------|
| Agda       | Dependent ITP                         | `agda`          | `cabal install Agda` or distro package                                                          |
| Coq        | Calculus of Inductive Constructions   | `coqc`          | `opam install coq` (or Coq Platform installer)                                                  |
| Lean       | Lean 4                                | `lean`, `lake`  | `elan` toolchain manager: <https://leanprover.github.io/lean4/doc/quickstart.html>              |
| Isabelle   | Higher-order logic                    | `isabelle`      | <https://isabelle.in.tum.de/installation.html>                                                  |
| Z3         | SMT solver                            | `z3`            | `apt install z3` / `brew install z3` / release tarball                                          |
| CVC5       | SMT solver                            | `cvc5`          | <https://cvc5.github.io/downloads.html>                                                         |
| Metamath   | Pure-Rust in-process checker          | *(none)*        | Works without external binary — pure-Rust implementation in `src/rust/provers/metamath.rs`      |
| HOL Light  | Classical higher-order logic          | `hol_light`     | OCaml + HOL Light: <https://github.com/jrh13/hol-light>                                         |
| Mizar      | Tarski–Grothendieck set theory        | `mizf`, `verifier` | <http://mizar.org/system/index.html>                                                         |
| PVS        | Prototype Verification System         | `pvs`           | <https://pvs.csl.sri.com/>                                                                      |
| ACL2       | Applicative Common Lisp               | `acl2`          | <https://www.cs.utexas.edu/users/moore/acl2/>                                                   |
| HOL4       | HOL family theorem prover             | `hol`           | <https://hol-theorem-prover.org/>                                                               |

ECHIDNA does **not** install or bundle these binaries. When a binary is
missing, the corresponding `POST /api/prove` call returns a structured
error (e.g. `"Failed to spawn Z3 process: \"z3\""`) — it does not crash
the server and the other 11 provers remain available.

## Quickstart: prove your first goal

```bash
# 1. Install Z3 (smallest dependency, ~5 MB)
sudo apt install z3        # Debian/Ubuntu
brew install z3            # macOS

# 2. Build and run the server
cargo run --bin echidna -- server --cors

# 3. In another terminal — health check
curl http://127.0.0.1:8081/api/health
# → {"status":"ok","version":"2.1.0"}

# 4. Prove a satisfiable SMT-LIB goal
curl -X POST http://127.0.0.1:8081/api/prove \
  -H 'Content-Type: application/json' \
  -d '{
        "prover": "Z3",
        "content": "(set-logic QF_LIA)\n(declare-const x Int)\n(assert (> x 0))\n(check-sat)\n",
        "timeout": 30
      }'
# → {"success":true,"goals":1,"message":"Proof verified successfully"}
```

For a browser UI, open `src/ui/public/prove.html` directly in any
modern browser and point the "API base" field at the running server.
No build step is required.

## Beyond the core 12

`ProverKind::all()` lists 67 additional backends (79 total — 12 core
plus 67 extended) with full
`ProverBackend` trait implementations (real subprocess invocation, not
stubs), spanning interactive provers (Idris2, Lean3, F\*), first-order
ATPs (Vampire, E, SPASS), constraint/SAT solvers (MiniSat, CaDiCaL,
Kissat, MiniZinc), model checkers (SPIN, NuSMV, TLC, UPPAAL),
auto-active verifiers (Dafny, Why3), security tools (Tamarin, ProVerif,
CryptoVerif, EasyCrypt), and more.

These are reachable via the Rust API:

```rust
use echidna::provers::{ProverFactory, ProverKind, ProverConfig};
let backend = ProverFactory::create(ProverKind::Vampire, ProverConfig::default())?;
```

They are deliberately not in `all_core()` because each adds an external
binary dependency and most users do not need them. To expose extra
backends through the REST API, edit `src/rust/provers/mod.rs:689` and
add the relevant `ProverKind` variants to `all_core()`.

The full `ProverKind` enum has 141 variants. The delta between 141 and
79 covers dialect variants (e.g. `Lean3` alongside `Lean`, `Rocq`
alongside `Coq`, `IsabelleZF` alongside `Isabelle`) and experimental
adapters not yet promoted to the canonical roster. They have
implementation files but are not exercised by the default test suite.

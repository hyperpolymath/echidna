<!-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk> -->
<!-- SPDX-License-Identifier: CC-BY-SA-4.0 -->
# Getting Started

The canonical quickstart docs live in the repo:

- [`QUICKSTART-USER.adoc`](https://github.com/hyperpolymath/echidna/blob/main/QUICKSTART-USER.adoc) — first proof, REPL, simple verification
- [`QUICKSTART-DEV.adoc`](https://github.com/hyperpolymath/echidna/blob/main/QUICKSTART-DEV.adoc) — development workflow, Justfile-first
- [`QUICKSTART-MAINTAINER.adoc`](https://github.com/hyperpolymath/echidna/blob/main/QUICKSTART-MAINTAINER.adoc) — release, packaging, CI

This page is a short orientation; defer to those for current details.

## Prerequisites

- **Rust** stable (MSRV pinned in `rust-toolchain.toml`; nightly accepted, not required)
- **Julia 1.10+** (for the ML sidecar — optional; the core compiles without it)
- **Just** (task runner — primary build system per RSR-H14)
- **Guix** (primary package manager; sealed-container escape hatch at `.containerization/Containerfile.wave3`)
- **Podman** (containers — RSR-H15; **do not** use Docker)

> Note: Nix as a fallback was deprecated in the 2026-05-18 estate ruling and fully removed estate-wide on 2026-06-01. Use Guix or the sealed container only.

## Quick setup

```bash
git clone https://github.com/hyperpolymath/echidna.git
cd echidna

just setup            # installs deps via Guix manifest where possible
just doctor           # diagnose any missing components
just build            # cargo build --release
```

## First proof

```bash
# Interactive REPL
just repl

# Verify a proof file
just verify examples/simple.v
```

## Verify the dogfood proof corpus

ECHIDNA dogfoods formal verification: its own trust-kernel proofs live under
`proofs/` (Coq, Lean 4, Agda) and `src/idris`, and every one type-checks in CI
(`dogfood-proofs-ci.yml` for Coq/Lean/Agda, `idris2-abi-ci.yml` for the Idris2
ABI + validator). Run the same checks locally with the `just` recipes CI calls:

```bash
just proofs          # roll-up: Coq + Lean + Agda + Idris2
just proofs-coq      # coqc over proofs/coq
just proofs-lean     # lake build in proofs/lean (Lean toolchain pinned by lean-toolchain)
just proofs-agda     # agda over proofs/agda (needs agda-stdlib registered)
just proofs-idris    # idris2 --typecheck the src/idris validator
```

Toolchain versions match CI: Coq 8.18, Lean v4.13.0, Agda 2.6.3 with stdlib
v1.7.3, and Idris2 0.8.0.

## Install prover backends

The 12 core (Tier 1) backends need their binaries on PATH. See
[`docs/PROVER_COUNT.md`](https://github.com/hyperpolymath/echidna/blob/main/docs/PROVER_COUNT.md)
for the tier table. The Guix manifest at `manifests/live-provers.scm` covers
the bulk; the sealed container at `.containerization/Containerfile.wave3`
covers the non-free / not-in-Guix tail.

```bash
# Inside a Guix environment:
guix shell -m manifests/live-provers.scm -- just test-live

# Or inside the container:
podman build -f .containerization/Containerfile.wave3 -t echidna:wave3 .
podman run --rm -it echidna:wave3 just test
```

## ML sidecar (optional, gates GNN features)

```bash
# Train on the static corpus (CPU smoke)
just train-cpu

# Or on GPU with the full 553 MB corpus
just train

# Evaluate the trained weights against the held-out validation split
just eval
```

See [`docs/handover/S5-VERIFICATION-RUNBOOK.md`](https://github.com/hyperpolymath/echidna/blob/main/docs/handover/S5-VERIFICATION-RUNBOOK.md)
for the end-to-end verification flow.

## Ingest a corpus

The 2026-06-01 saturation campaign added 13 new corpus adapters (17 total: agda, coq, lean, idris2, isabelle, metamath, mizar, hol_light, hol4, dafny, why3, fstar, acl2_books, tptp, smtlib, proofnet, minif2f). Each one is a `pub fn ingest(root: &Path) -> Result<Corpus>` under `src/rust/corpus/<name>.rs`.

```rust
use std::path::Path;
use echidna::corpus::isabelle;

let corpus = isabelle::ingest(Path::new("/path/to/afp/thys"))?;

// Look up a theorem by short name (also matches qualified names
// and falls back to case-insensitive substring search):
for entry in corpus.find("theorem_name") {
    println!("{} in {}:{}", entry.qualified, entry.module_idx, entry.line);
    if entry.axiom_usage.any() {
        eprintln!("  HAZARD: {:?}", entry.axiom_usage);
    }
}
```

The entry types (`src/rust/corpus/mod.rs`):

- [`DeclKind`](https://github.com/hyperpolymath/echidna/blob/main/src/rust/corpus/mod.rs#L70) — `Function | Data | Record | Postulate | Module`.
- [`AxiomUsage`](https://github.com/hyperpolymath/echidna/blob/main/src/rust/corpus/mod.rs#L92) — boolean flags for `postulate`, `believe_me`, `assert_total`, `admitted`, `sorry`, `trustme`, plus `other: Vec<String>` for free-form hazards. `AxiomUsage::any()` is true if anything fired.
- [`CorpusEntry`](https://github.com/hyperpolymath/echidna/blob/main/src/rust/corpus/mod.rs#L132) — one per top-level decl: `name`, `qualified`, `module_idx`, `kind`, `statement`, `proof: Option<String>`, `line`, `dependencies: Vec<String>`, `axiom_usage`.

Full adapter table: [`docs/CORPUS-ADAPTERS.md`](https://github.com/hyperpolymath/echidna/blob/main/docs/CORPUS-ADAPTERS.md).

## Cross-prover synonym lookup

`SynonymTable` loads `data/synonyms/<prover>.toml` and exposes alias-aware lookup (`src/rust/suggest/synonyms.rs`).

```rust
use std::path::Path;
use echidna::suggest::synonyms::{SynonymTable, load_cross_prover_dicts};
use echidna::ProverKind;

let dir = Path::new("data/synonyms");

// Per-prover table — "what does Lean call the same thing?":
let lean = SynonymTable::load(ProverKind::Lean, dir)?;
for alt in lean.alternatives("simp") {
    println!("Lean alias: {}", alt);
}

// Cross-prover bridges — MSC2020 / WordNet / ConceptNet:
let dicts = load_cross_prover_dicts(dir)?;
println!("MSC2020 entries: {}", dicts.msc2020.len());
println!("WordNet math entries: {}", dicts.wordnet_math.len());
println!("ConceptNet seed entries: {}", dicts.conceptnet_seed.len());

// Merge a bridge into a per-prover table for unified semantic_class queries:
let mut lean = lean;
lean.merge_external(&dicts.msc2020);
for entry in lean.by_semantic_class("well-foundedness") {
    println!("  {} (class: {:?})", entry.canonical, entry.semantic_class);
}
```

The cross-prover dictionaries are optional — `load_cross_prover_dicts` returns empty tables for any missing file (offline-resilient).

## Arbitrate disagreeing provers

When two provers disagree, the `BayesianArbiter` combines their evidence into a calibrated posterior (`src/rust/verification/bayesian_arbiter.rs`).

```rust
use echidna::verification::bayesian_arbiter::{
    BayesianArbiter, ProverEvidence, Verdict,
};
use echidna::provers::ProverKind;

let arb = BayesianArbiter::new(0.5); // uniform prior

let evidence = vec![
    ProverEvidence {
        prover: ProverKind::Z3,
        verdict: Verdict::Proven,
        time_ms: 240,
        confidence_self_reported: None,
    },
    ProverEvidence {
        prover: ProverKind::Coq,
        verdict: Verdict::Refuted,
        time_ms: 1_800,
        confidence_self_reported: None,
    },
];

let post = arb.combine(&evidence);
// PosteriorVerdict { p_proven, p_refuted, p_unknown, entropy_bits, winning }
println!(
    "winning={:?} p_proven={:.3} p_refuted={:.3} entropy={:.2} bits",
    post.winning, post.p_proven, post.p_refuted, post.entropy_bits,
);
```

Coq's default likelihood is calibrated higher than Z3's, so the posterior leans toward Refuted on this tied disagreement (see the `conflicting_z3_proven_and_coq_refuted_depends_on_priors` test in the same module). Verdicts of `Timeout`, `Unknown`, and `Error` contribute a likelihood ratio of 1.0 (no update) but shift mass to `p_unknown`.

## What's next

- [Guides](Guides) — adding a backend, API usage, training the model
- [Architecture](Architecture) — how the pieces fit
- [`docs/ROADMAP.md`](https://github.com/hyperpolymath/echidna/blob/main/docs/ROADMAP.md) — what's being built next

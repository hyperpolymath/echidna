<!-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk> -->
<!-- SPDX-License-Identifier: CC-BY-SA-4.0 -->
# Guides

## Adding a new prover backend

1. Create `src/rust/provers/your_prover.rs` implementing the `ProverBackend` trait. See [`src/rust/provers/z3.rs`](https://github.com/hyperpolymath/echidna/blob/main/src/rust/provers/z3.rs) or [`src/rust/provers/coq.rs`](https://github.com/hyperpolymath/echidna/blob/main/src/rust/provers/coq.rs) for templates.
2. Add a variant to `ProverKind` in `src/rust/provers/mod.rs`.
3. Wire it into `ProverFactory::create`.
4. Add test fixtures under `tests/fixtures/your_prover/`.
5. If the prover has a binary, add the SHAKE3-512 + BLAKE3 hashes to `config/solver-manifest.toml`.
6. If the prover should ship with the project, add it to `manifests/live-provers.scm` (Guix) or to `.containerization/Containerfile.wave3` (sealed container).
7. Update [`docs/PROVER_COUNT.md`](https://github.com/hyperpolymath/echidna/blob/main/docs/PROVER_COUNT.md) with the new tier assignment.
8. Run `just check && just test`.

## Using the API

```bash
# Start the API server
just serve

# REST: POST /api/verify
curl -X POST http://localhost:8000/api/verify \
  -H 'Content-Type: application/json' \
  -d '{"prover": "z3", "content": "(declare-const x Int) (assert (= (* x x) 4)) (check-sat)"}'

# GraphQL: port 8000/graphql
# gRPC:    port 50051
```

API surface and schemas: see [`src/interfaces/`](https://github.com/hyperpolymath/echidna/tree/main/src/interfaces).

## Training the GNN

The Julia ML sidecar trains from `training_data/` (553 MB corpus, ~67k proofs / ~180k tactics across 16 prover systems).

```bash
# CPU smoke run (~5 min)
just train-cpu

# Full GPU run (1–4h depending on hardware)
just train

# Evaluate against the held-out 20% validation split
just eval
```

Trained weights land in `models/neural/gnn_ranker/`. The Julia server hot-loads them on startup; a planned `POST /reload` endpoint will allow hot-swap without restart. See [`docs/handover/S5-VERIFICATION-RUNBOOK.md`](https://github.com/hyperpolymath/echidna/blob/main/docs/handover/S5-VERIFICATION-RUNBOOK.md).

## Configuring trust thresholds

Trust pipeline parameters live in `DispatchConfig` (`src/rust/dispatch.rs`). Adjust:

- `generate_certificates` — request DRAT/LRAT/TSTP certificates where supported
- `timeout` — per-prover wall-clock budget
- `cross_check_required` — minimum portfolio agreement
- `min_trust_level` — refuse below this Bayesian tier

Per-(prover, domain) timeout estimates come from `StatisticsTracker::estimate_timeout` once the learning loop has accumulated evidence. See [`docs/ARCHITECTURE.md`](https://github.com/hyperpolymath/echidna/blob/main/docs/ARCHITECTURE.md).

## Working with the learning loop

The loop flows: prover runs → outcome → VeriSimDB `proof_attempts` table → `mv_prover_success_by_class` materialised view → `VeriSimAdvisor` reads in dispatch / Julia `/training/update` pushes weights. Closing this loop is **Stage 3c** on the roadmap; current status and dead-wire findings are in [`docs/handover/STATE.md`](https://github.com/hyperpolymath/echidna/blob/main/docs/handover/STATE.md).

## Environment variables

Every env var the system reads is enumerated in [`docs/ENV-VARS.md`](https://github.com/hyperpolymath/echidna/blob/main/docs/ENV-VARS.md).

## Following the roadmap

[`docs/ROADMAP.md`](https://github.com/hyperpolymath/echidna/blob/main/docs/ROADMAP.md) is the canonical 8-stage map. [`docs/handover/HANDOVER-INDEX.md`](https://github.com/hyperpolymath/echidna/blob/main/docs/handover/HANDOVER-INDEX.md) navigates the prompt-and-runbook suite that drives each stage.

## Guide: Adding a new corpus adapter

The 2026-06-01 saturation campaign brought the adapter count to 17. The mechanical pattern is small enough to fit on one page; the criteria for *when* to add one are in [`docs/CORPUS-ADAPTERS.md` § "When to add a new adapter"](https://github.com/hyperpolymath/echidna/blob/main/docs/CORPUS-ADAPTERS.md#when-to-add-a-new-adapter).

1. **Pick a reference adapter.** Read [`src/rust/corpus/agda.rs`](https://github.com/hyperpolymath/echidna/blob/main/src/rust/corpus/agda.rs) for a layout-sensitive language or [`src/rust/corpus/coq.rs`](https://github.com/hyperpolymath/echidna/blob/main/src/rust/corpus/coq.rs) for a keyword-delimited one. Both are heuristic, not full parsers — that's deliberate (see the module-level doc on `src/rust/corpus/mod.rs`).
2. **Create `src/rust/corpus/<your_adapter>.rs`** exposing `pub fn ingest(root: &Path) -> Result<Corpus>`.
3. **Two-pass extraction.** Pass 1 walks the tree, enumerates module names and decl names. Pass 2 walks each decl's text and records references to any name in pass-1's known set. Strip comments before reference scanning but preserve newlines so line numbers stay aligned (see the Isabelle adapter for the canonical comment-stripping shape).
4. **Hazard detection.** Fill `AxiomUsage` per entry. The detector is heuristic — scan the comment-stripped slice covering the decl's lines for prover-specific banned tokens (`axiomatization`, `sorry`, `cheat`, `believe_me`, `Admitted`, …). False positives inside string literals are acceptable; flag in `axiom_usage.other` for human review.
5. **Register in `src/rust/corpus/mod.rs`.** Add `pub mod your_adapter;` to the module list.
6. **Add the per-prover synonyms TOML** at `data/synonyms/<your_adapter>.toml` with schema `[[synonym]]` rows (`canonical`, `aliases`, optional `tactic_class`, `semantic_class`). Map the new `ProverKind` variant to its filename in `prover_table_filename` in [`src/rust/suggest/synonyms.rs`](https://github.com/hyperpolymath/echidna/blob/main/src/rust/suggest/synonyms.rs).
7. **Add a fixture** under `tests/corpus_fixtures/<your_adapter>/` covering one happy-path decl and one hazard case. Keep it tiny — the goal is smoke correctness, not coverage.
8. **Update [`docs/CORPUS-ADAPTERS.md`](https://github.com/hyperpolymath/echidna/blob/main/docs/CORPUS-ADAPTERS.md)** with the new row in the adapter table.

## Guide: Picking an arbitration mechanism

ECHIDNA ships four arbiters. They're complementary; the right choice depends on what you want the output to *be*.

| Arbiter | Output shape | Use when |
|---|---|---|
| **Portfolio** (`src/rust/verification/portfolio.rs`) | Categorical agreement summary (`PortfolioConfidence` + `SolverResult` list) | You want simple-majority consensus across N solvers — fast, no calibration needed. Default for "did any two solvers agree?" |
| **Bayesian** (`src/rust/verification/bayesian_arbiter.rs`) | `PosteriorVerdict { p_proven, p_refuted, p_unknown, entropy_bits, winning }` | You have calibrated per-prover precision/FPR and want a probability with uncertainty. Returns Shannon entropy too. |
| **Dempster-Shafer** (`src/rust/verification/dempster_shafer.rs`) | `BeliefPlausibility` over `VerdictSet` — or `ArbiterError::HighConflict(k)` if conflict mass `k > 0.95` | You want to model *ignorance* as first-class (mass on `{Proven, Refuted}` = "I don't know"). Refuses to commit when conflict is too high. |
| **Pareto** (`src/rust/verification/pareto_arbiter.rs`) | `ParetoDecision` over `AttemptOutcome` records | You're optimising on *multiple* axes (time, memory, certificate-size, trust-tier) and want non-dominated outcomes, not a single verdict. |

Motivating examples:

- **Portfolio** — "Run Z3, CVC5, Vampire; if any two say Proven, ship it."
- **Bayesian** — "Z3 says Proven, Coq says Refuted; given Coq's higher precision, what's the posterior?" (see the test in `bayesian_arbiter.rs:268`).
- **Dempster-Shafer** — "Five solvers; three Proven, two Refuted; either commit a posterior or *refuse to arbitrate* because conflict is too high."
- **Pareto** — "Lean took 30s and produced a 4kB certificate; Z3 took 0.2s and produced no certificate. Which dominates?" — neither; return both as Pareto-optimal.

### Unified entry point: `ResultArbiter`

You normally don't call the four mechanisms directly. `ResultArbiter` (`src/rust/verification/result_arbiter.rs`) takes the per-prover `ProverOutcome`s from a cross-checked dispatch, adapts them into whichever mechanism `DispatchConfig.arbitration_policy` selects (`portfolio` default | `bayesian` | `dempster_shafer`), and returns an `ArbitratedVerdict`: winning verdict, agreeing/disagreeing/inconclusive camps, a `[0,1]` conflict metric, `needs_review`, and a Pareto-recommended prover among the agreeing set. `Dispatcher::verify_proof_cross_checked` attaches it to `DispatchResult.arbitration`. Key semantics: timeouts and errors are no-information (they no longer veto agreement), and a genuine Proven-vs-Refuted split is flagged for review instead of being flattened to `verified = false`.

## Guide: Cross-prover semantic queries

The synonym layer carries an optional `semantic_class` tag per entry. Combined with the three cross-prover dictionaries (`_msc2020.toml`, `_wordnet_math.toml`, `_conceptnet_seed.toml`) this gives "every prover's name for the same concept" lookups, fully offline.

```rust
use std::path::Path;
use echidna::suggest::synonyms::{
    SynonymTable, load_all, load_cross_prover_dicts,
};
use echidna::ProverKind;

let dir = Path::new("data/synonyms");

// Load all per-prover tables (saturation-campaign set: 13 provers).
let mut tables = load_all(dir)?;

// Merge each cross-prover dictionary into every per-prover table
// so `by_semantic_class` queries find rows regardless of origin.
let dicts = load_cross_prover_dicts(dir)?;
for table in tables.values_mut() {
    table.merge_external(&dicts.msc2020);
    table.merge_external(&dicts.wordnet_math);
    table.merge_external(&dicts.conceptnet_seed);
}

// "What's everyone's name for well-foundedness?"
for (prover, table) in &tables {
    for entry in table.by_semantic_class("well-foundedness") {
        println!(
            "{:?}: {} (aliases: {:?})",
            prover, entry.canonical, entry.aliases,
        );
    }
}
```

The semantic classes are deliberately coarse (e.g. `"well-foundedness"`, `"accessibility"`, `"transitivity"`) — fine-grained equivalence belongs in the OpenTheory / Dedukti exchange layer (`src/rust/exchange/`).

## Guide: Adding a new exchange bridge

Exchange modules translate proof artefacts between formalisms. The 2026-06-01 saturation campaign added six (TPTP, LambdaPi, SMTCoq stub, plus existing Dedukti, OpenTheory, Alethe). The pattern from [`src/rust/exchange/tptp.rs`](https://github.com/hyperpolymath/echidna/blob/main/src/rust/exchange/tptp.rs) and [`src/rust/exchange/lambdapi.rs`](https://github.com/hyperpolymath/echidna/blob/main/src/rust/exchange/lambdapi.rs):

1. **Module-level doc** stating the format, upstream URL, and what's in vs. out of scope. Be explicit about "stub bridge" vs "full bridge" — see [`src/rust/exchange/smtcoq.rs`](https://github.com/hyperpolymath/echidna/blob/main/src/rust/exchange/smtcoq.rs) for the canonical stub-bridge disclosure (gated on upstream SMTCoq Coq plugin invocation).
2. **`ExchangeError` enum** with at minimum `UnsupportedDialect(String)`, `ParseError(String)`, `TranslationError(String)`, `EmptyProblem`. Implement `Display` and `std::error::Error`.
3. **Structured AST** for the format — typically a `Problem` / `Module` struct holding a `Vec<AnnotatedFormula>` or equivalent. Derive `Serialize + Deserialize + PartialEq + Eq + Clone + Debug` so consumers can persist intermediate forms.
4. **`pub fn parse(input: &str) -> Result<Problem, ExchangeError>`** — best-effort parser, lenient on whitespace, strict on dialect mismatch.
5. **`pub fn emit(p: &Problem) -> String`** — round-trip safe for the supported dialect subset.
6. **Translation seams** to/from neighbouring formats (TPTP ↔ SMT-LIB, LambdaPi ↔ Dedukti). Reject unsupported dialects with `UnsupportedDialect` rather than silently mistranslating.
7. **Unit tests** covering a parse-emit round-trip on at least one fixture from the upstream problem set.
